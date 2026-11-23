#!/usr/bin/env python3
"""Map the archive's declarations and what each one mentions, read as text. Nothing in the archive is run.

    python3 -I tools/rh/decl_map.py SRC OUT_DIR --names NAMES.tsv [--jobs N] [--only PREFIX]

SRC is the archive's source directory. NAMES.tsv lists the constants of Mathlib at the archive's pin, one name at
the start of each line (it is what tells a Mathlib name from a local variable). The script writes to OUT_DIR:

* `graph.pkl`: every declaration (name, kind, file, lines) and its edges, for `decl_query.py`;
* `report.json`: totals, and the size of what the roots reach under each rule below.

It is an approximation. Lean resolves names with types; this resolves them with text:

* a command starts at a line whose first column holds a command keyword; a declaration's name is the current
  namespace and the name after the keyword (`namespace A.B` opens two, and `end B` closes one); `private` names
  are looked up in their own file only;
* an identifier is looked up as Lean does, in the namespaces around the declaration from the inside out, then at
  the root and in the opened namespaces together; if the whole name is unknown its last component is dropped and
  it is tried again, and the dropped components are recorded as fields;
* names bound by a binder in the same declaration are not looked up (found with a few patterns);
* a name after a dot whose head is not a constant (`h.foo`, `(f x).foo`) is a field: it reaches `N.foo` for
  every `N` that is itself reached or is a Mathlib constant;
* an instance is reached when every archive constant of its signature is; so is an `attribute` command that is
  not local when every constant it names is; a local instance, attribute or notation is counted as mentioned by
  every later declaration of its section;
* instances and attribute commands that name no archive constant are listed as orphans and not followed;
* a name that ends in `Cpt` and is not declared is a copy that the archive's `cpt_copy_thms` makes: it reaches
  the declaration without the suffix, and the command.

What it cannot see: an instance or a simp lemma that a proof uses without naming it is reached only by the rules
above, names made by attributes (`simps`, `to_additive`) are matched by prefix only, and a binder that the patterns
miss makes a spurious edge. The exact map needs the archive compiled.
"""
import argparse
import json
import multiprocessing as mp
import os
import pickle
import re
import sys
import time
from array import array
from collections import Counter, defaultdict, deque

COMP = r"[^\W\d][\w'!?]*"
TOKEN = re.compile(r'"(?:\\.|[^"\\])*"|(?<![\w\'])(' + COMP + r"(?:\." + COMP + r")*)")
STRIP = re.compile(r'--[^\n]*|/-|"(?:\\.|[^"\\\n])*"')
BLOCK = re.compile(r"/-|-/")
WORD = re.compile(r"[^\s(\[{⟨⦃:]+")

DECL_KW = {"theorem", "lemma", "def", "abbrev", "instance", "structure", "class", "inductive", "example", "alias",
           "opaque", "axiom", "irreducible_def"}
SYN_KW = {"notation", "infix", "infixl", "infixr", "prefix", "postfix", "macro", "macro_rules", "syntax", "elab",
          "elab_rules", "declare_syntax_cat", "unif_hint", "run_cmd", "cpt_copy_thms", "add_decl_doc",
          "initialize_simps_projections"}
IGNORE_KW = {"universe", "set_option", "include", "omit", "import", "suppress_compilation", "deriving"}
MODS = {"private", "protected", "noncomputable", "nonrec", "partial", "unsafe", "scoped", "local", "public", "meta"}
SCOPE_KW = {"namespace", "section", "end", "open", "export", "variable", "attribute", "mutual"}
START = re.compile(r"(?:@\[|#\w|(?:" + "|".join(sorted(DECL_KW | SYN_KW | IGNORE_KW | MODS | SCOPE_KW)) + r")\b)")
SETOPT_IN = re.compile(r"set_option\s+\S+\s+\S+\s+in\b")
OTHER_IN = re.compile(r"(?:omit|include|variable|universe)\s+[^\n]*?\s+in\b")
OPEN_IN = re.compile(r"open\s+([^\n]*?)\s+in\b")
# `attribute [local instance] a b in`, before the command it is for (and often after an `open … in`)
ATTR_IN = re.compile(r"attribute\s*\[[^\]\n]*\]([^\n]*?)\s+in\b")
SPLIT = re.compile(r'"(?:\\.|[^"\\])*"|[(\[{⟨⦃]|[)\]}⟩⦄]|:=|\bwhere\b|\n[ \t]*\|')
BRACKET = re.compile(r'"(?:\\.|[^"\\])*"|[\[\]]')

# binders: names that these introduce are local, and are not looked up
B_GROUP = re.compile(r"[({⦃\[]\s*((?:[^\W\d][\w']*\s+)*[^\W\d][\w']*)\s*:(?!=)")
B_FUN = re.compile(r"(?:\bfun\b|λ)([^\n:=↦]*)")
# (the names end at `∂` too: in `∀ᵐ q ∂quotMeasure Γ μ, …` the measure is a term)
B_QUANT = re.compile(r"(?:∀|∃!?|∑|∏|∫⁻?|⨆|⨅|⋃|⋂)([^\n:=↦,∈∉<≤>≥≠⊆∂]*)")
B_QWORD = re.compile(r"\bfun\b|λ|∀|∃!?|∑|∏|∫⁻?|⨆|⨅|⋃|⋂")
B_QGROUPS = re.compile(r"(?:\bfun\b|λ|∀|∃!?|∑|∏|∫⁻?|⨆|⨅|⋃|⋂)\s*((?:[({⦃\[][^()\[\]{}⦃⦄\n]*[)}\]⦄]\s*)+)")
B_TAC = re.compile(r"(?:^|[;·(]|\bby|=>|<;>)[ \t]*(?:intros?|rintro|obtain|ext1?|funext|choose!?|by_cases|by_contra!?"
                   r"|rename_i|case'?|next)\b([^\n:=↦;<]*)", re.M)
B_WITH = re.compile(r"\bwith\b([^\n:=↦;<]*)")
B_HAVE = re.compile(r"\b(?:have|suffices|let|set|haveI|letI)\s+([^\W\d][\w']*|⟨[^⟩\n]*⟩)\s*(?=:|[({\[⦃])")
B_SET = re.compile(r"\{\s*([^\W\d][\w']*)\s*(?:\||:(?!=))")
B_ALT = re.compile(r"\n[ \t]*\|([^\n=]*)=>")
B_CUT = re.compile(r"\b(?:using|at|from|with|by|generalizing|in)\b")
# a field given a value in a structure instance, `{ x := v, y := w }`, and a named argument `(x := v)`
B_FIELD = re.compile(r"[{,(][ \t]*([^\W\d][\w']*)[ \t]*:=")
WHERE = re.compile(r"\bwhere[ \t]*\n")
BODY_OPEN = re.compile(r"\bopen[ \t]+((?:[^\W\d][\w.']*[ \t]+)+)in\b")
# a field of a `structure` in brackets, on a line of its own: `[top : TopologicalSpace X]`
B_SBRACK = re.compile(r"^[ \t]+[\[({⦃][ \t]*((?:[^\W\d][\w']*[ \t]+)*[^\W\d][\w']*)[ \t]*:(?!=)", re.M)
# a field given a value after `where`, with or without arguments: `map_add x y := …`
B_FIELD_ARGS = re.compile(r"((?:[^\W\d][\w']*[ \t]+)*[^\W\d][\w']*)[ \t]*:=")


def where_fields(text):
    """The names that the lines after a `where` bind: the lines that begin where the first of them begins. A
    line of a proof that ends in `:=` is not one (`chartRing ℤ x i := by` continues a `have`), so only a
    `where` block is read this way. After the body of a declaration, such a line defines a local function, and
    binds its name and its arguments. Where the `where` stands for the body (`def cxStage : CxSt F where`),
    the lines give values to the fields of a structure: `pn Y σ Δ := pn Y σ Δ` binds `Y σ Δ`, and the field's
    name is not a variable there: the second `pn` is the function of that name outside."""
    out = set()
    for m in WHERE.finditer(text):
        fields = ":=" not in text[:m.start()]
        indent = None
        for line in text[m.end():].split("\n"):
            if not line.strip():
                continue
            k = len(line) - len(line.lstrip(" \t"))
            if indent is None:
                indent = k
            if k < indent:
                break
            if k == indent:
                f = B_FIELD_ARGS.match(line, k)
                if f:
                    out.update(f.group(1).split()[1:] if fields else f.group(1).split())
    return out
# the fields that a `structure` or `class` declares, one line each: `re im : ℝ`, `map_add (x y : α) : …`
B_SFIELD = re.compile(r"^[ \t]+((?:[^\W\d][\w']*[ \t]+)*[^\W\d][\w']*)[ \t]*(?:[({\[⦃][^\n]*?[)}\]⦄][ \t]*)*:(?!=)", re.M)
B_HEAD = re.compile(r'"(?:\\.|[^"\\])*"|[(\[{⟨⦃]|[)\]}⟩⦄]|:')
SIMPLE = re.compile(r"(?<![\w'.])[^\W\d][\w']*(?![\w'.])")

# words of the syntax, which no declaration can be named; a tactic's name can be a declaration's (`ext`, `left`)
KEYWORDS = frozenset("""by fun at with using from in if then else match do calc where have show let Type Prop Sort
theorem lemma def abbrev instance structure class inductive namespace section end open variable universe
set_option attribute noncomputable private protected local scoped""".split())

# attributes that make declarations named after the one they are on: `foo_assoc`, `foo_apply`, `foo_iff`
MAKERS = {"simps", "to_additive", "reassoc", "elementwise", "mk_iff"}

WEAK_ATTRS = {"simp", "norm_cast", "push_cast", "ext", "fun_prop", "gcongr", "aesop", "grind", "continuity",
              "measurability", "bound", "mono", "congr", "refl", "symm", "trans", "positivity", "norm_num", "simp↓",
              "instance"}

F_PRIVATE, F_LOCAL, F_SCOPED, F_WEAK, F_ROOT, F_PROTECTED = 1, 2, 4, 8, 16, 32


def strip_comments(text):
    out, i, n = [], 0, len(text)
    while True:
        m = STRIP.search(text, i)
        if not m:
            out.append(text[i:])
            break
        out.append(text[i:m.start()])
        tok = m.group()
        if tok.startswith("--"):
            i = m.end()
        elif tok == "/-":
            depth, j = 1, m.end()
            while depth:
                mm = BLOCK.search(text, j)
                if not mm:
                    j = n
                    break
                depth += 1 if mm.group() == "/-" else -1
                j = mm.end()
            out.append("\n" * text.count("\n", m.start(), j))
            i = j
        else:
            out.append(tok)
            i = m.end()
    return "".join(out)


def split_commands(text):
    start, cur = None, []
    for i, line in enumerate(text.split("\n")):
        if line and not line[0].isspace() and START.match(line):
            if cur:
                yield start, i - 1, "\n".join(cur)
            start, cur = i, [line]
        elif cur:
            cur.append(line)
    if cur:
        yield start, start + len(cur) - 1, "\n".join(cur)


def close_bracket(t, i):
    """Index of the `]` that closes the `[` at index i."""
    depth = 0
    for m in BRACKET.finditer(t, i):
        g = m.group()
        if g == "[":
            depth += 1
        elif g == "]":
            depth -= 1
            if depth == 0:
                return m.start()
    return len(t) - 1


def split_sig(t):
    depth = 0
    for m in SPLIT.finditer(t):
        c = m.group()[0]
        if c == '"':
            continue
        if c in "([{⟨⦃":
            depth += 1
        elif c in ")]}⟩⦄":
            depth -= 1
        elif depth <= 0:
            return t[:m.start()], t[m.start():]
    return t, ""


def tokens_of(text):
    names, fields = set(), set()
    for m in TOKEN.finditer(text):
        t = m.group(1)
        if t is None:
            continue
        s = m.start(1)
        if s > 0 and text[s - 1] == ".":
            fields.update(t.split("."))
        elif t not in KEYWORDS:
            names.add(t)
    return names, fields


def header_binders(sig, whole=False):
    """The names bound in a declaration's header: the bracketed groups before its first colon at depth 0, or
    all through the text if `whole`. Only the groups that no bracket encloses: `(hE : (divCycle P s E : ℤ) = 1)`
    binds `hE`, and the group inside it is a term with its type, not a binder."""
    depth, starts = 0, []
    for m in B_HEAD.finditer(sig):
        c = m.group()[0]
        if c in "([{⟨⦃":
            if depth == 0:
                starts.append(m.start())
            depth += 1
        elif c in ")]}⟩⦄":
            depth -= 1
        elif c == ":" and depth <= 0 and not whole:
            sig = sig[:m.start()]
            break
    out = set()
    for s0 in starts:
        m = B_GROUP.match(sig, s0)
        if m:
            out.update(m.group(1).split())
    return out


def cut_closed(part):
    """`part` up to the first bracket that closes one opened before it. The names that a binder word introduces
    end there: in `(congrArg g (funext hxs)).trans (psum_one t.G I)` the word `funext` is a function, and what
    follows the bracket around it is not bound."""
    depth = 0
    for i, c in enumerate(part):
        if c in "([{⟨⦃":
            depth += 1
        elif c in ")]}⟩⦄":
            if depth == 0:
                return part[:i]
            depth -= 1
    return part


def bound_names(text, tactics=True):
    """The names that the binders of a piece of source introduce, by pattern. The patterns of tactics are for a
    body only: in a statement a line may begin with a function named `ext` or `case`, and what follows it is not
    bound (`ext (fsj N r j0) φ (glAct p L J c d x) = …`)."""
    out = set()
    # the bracketed groups that follow a binder word, one after another, over lines and with brackets inside:
    # `∀ (p : ℕ) [Fact p.Prime] (K : F ℚ_[p] (G p))` and, lines below, `(A T' G : Type)`
    for m in B_QWORD.finditer(text):
        pos, n = m.end(), len(text)
        while True:
            while pos < n and text[pos] in " \t\n":
                pos += 1
            if pos >= n or text[pos] not in "([{⦃":
                break
            g = B_GROUP.match(text, pos)
            if g:
                out.update(g.group(1).split())
            depth = 0
            while pos < n:
                c = text[pos]
                if c in "([{⦃⟨":
                    depth += 1
                elif c in ")]}⦄⟩":
                    depth -= 1
                    if depth == 0:
                        pos += 1
                        break
                pos += 1
            else:
                break
    for rx in ((B_FUN, B_QUANT, B_TAC, B_WITH, B_ALT, B_HAVE) if tactics else (B_FUN, B_QUANT)):
        for m in rx.finditer(text):
            part = cut_closed(B_CUT.split(m.group(1), maxsplit=1)[0])
            out.update(SIMPLE.findall(part))
    out.update(B_SET.findall(text))
    # (the name of a field in `{ x := v }`, or of an argument in `(x := v)`, is not bound: `vol := vol` gives
    # the field the constant `vol`. `Bundle.lean` knows the name of a field from the use of a constant)
    out.update(where_fields(text))
    return out


def attr_names(attrs):
    """The attribute names of `@[a, b c, local d]` texts, and whether any is local or scoped."""
    names, local, scoped = [], False, False
    for a in attrs:
        for entry in a.split(","):
            w = entry.split()
            if not w:
                continue
            if w[0] == "local":
                local, w = True, w[1:]
            elif w[0] == "scoped":
                scoped, w = True, w[1:]
            if w:
                names.append(w[0].lstrip("-"))
    return names, local, scoped


class Scope:
    __slots__ = ("kind", "ns", "opens", "vars", "bound", "written")

    def __init__(self, kind, ns):
        self.kind, self.ns, self.opens, self.vars, self.bound = kind, ns, [], set(), set()
        self.written = []       # the namespaces of its `open`s, as written


def chain_of(ns):
    """`A.B.C` -> (`A.B.C.`, `A.B.`, `A.`): the namespaces around a declaration, innermost first."""
    out, parts = [], ns.split(".") if ns else []
    for k in range(len(parts), 0, -1):
        out.append(".".join(parts[:k]) + ".")
    return tuple(out)


def open_candidates(text, chain, written):
    """What the names of an `open` may be: each inside the namespaces around it, inside a namespace that an
    earlier `open` names (`open A.B C` opens `A.B.C` if there is one), or at the root. `written` holds the names
    of the earlier `open`s as they were written, and gets those of this one."""
    # `open N (a b)` shows `N.a` and `N.b` and nothing else of `N`: such an entry is written `N.| a b `.
    # `open N hiding a b` shows all of `N` but `N.a` and `N.b`: such an entry is written `N.|~ a b `
    m = re.search(r"\(([^)]*)\)", text)
    only = ""
    if m and not re.search(r"\b(?:hiding|renaming)\b", text):
        only = "| " + " ".join(m.group(1).split()) + " "
    m = re.search(r"\bhiding\b(.*)$", text, re.S)
    hidden = ("|~ " + " ".join(m.group(1).split()) + " ") if m and not only else ""
    text = re.sub(r"\([^)]*\)", " ", text)
    text = re.split(r"\b(?:hiding|renaming)\b", text)[0]
    out = []
    for name in text.split():
        if name == "scoped":
            continue
        if name.startswith("_root_."):
            # written from the root: that namespace and no other
            out.append(name[7:] + "." + (only or hidden))
            if not only:
                written.append(name[7:])
            continue
        for p in chain:
            out.append(p + name + "." + (only or hidden))
        for w in written:
            out.append(w + "." + name + "." + (only or hidden))
        out.append(name + "." + (only or hidden))
        if not only:
            written.append(name)
    return out


def parse_file(text):
    """The declarations of one file: a list of tuples (see `DECL_FIELDS`)."""
    if "--" in text or "/-" in text:
        text = strip_comments(text)
    decls = []
    stack = [Scope("root", "")]
    c_attrs, c_opens, c_mods, c_line, c_refs, c_pre = [], [], set(), None, [], []
    for l0, l1, chunk in split_commands(text):
        t = chunk
        attrs, opens_in, mods, refs, pre = c_attrs, c_opens, c_mods, c_refs, c_pre
        first = c_line if c_line is not None else l0
        while True:
            t = t.lstrip()
            if t.startswith("@["):
                j = close_bracket(t, 1)
                attrs.append(t[2:j])
                t = t[j + 1:]
                continue
            m = SETOPT_IN.match(t) or OTHER_IN.match(t)
            if m:
                if t.startswith("variable"):
                    # `variable (h : IsPlaceOver A w) in` / `def …`: binders of the declaration that follows
                    pre.append(t[len("variable"):m.end() - 2])
                t = t[m.end():]
                continue
            m = OPEN_IN.match(t)
            if m:
                opens_in.append(m.group(1))
                t = t[m.end():]
                continue
            m = ATTR_IN.match(t)
            if m:
                # the constants that it names are used by the command that follows, which the `open … in`
                # before it is for as well: `open A in` / `attribute [local instance] A.inst in` / `theorem …`
                refs.extend(m.group(1).split())
                t = t[m.end():]
                continue
            m = WORD.match(t)
            if m and m.group() in MODS:
                mods.add(m.group())
                t = t[m.end():]
                continue
            break
        if not t:
            c_attrs, c_opens, c_mods, c_line, c_refs, c_pre = attrs, opens_in, mods, first, refs, pre
            continue
        c_attrs, c_opens, c_mods, c_line, c_refs, c_pre = [], [], set(), None, [], []
        m = WORD.match(t)
        kw = m.group() if m else t[:1]
        rest = t[len(kw):]
        ns = stack[-1].ns
        if kw == "namespace":
            # `namespace A.B` opens two scopes: `end B` closes one of them
            name = rest.strip().split()[0] if rest.strip() else ""
            for part in name.split("."):
                ns = (ns + "." + part) if ns else part
                stack.append(Scope("ns", ns))
            continue
        if kw in ("section", "mutual"):
            stack.append(Scope(kw, ns))
            continue
        if kw == "end":
            name = rest.strip().split()[0] if rest.strip() else ""
            for _ in range(len(name.split(".")) if name else 1):
                if len(stack) > 1:
                    stack.pop()
            continue
        if kw == "open":
            if rest.lstrip().startswith("scoped"):
                continue
            written = [w for sc in stack for w in sc.written]
            n_before = len(written)
            stack[-1].opens.extend(open_candidates(rest, chain_of(ns), written))
            stack[-1].written.extend(written[n_before:])
            continue
        if kw in IGNORE_KW or kw.startswith("#"):
            continue
        if kw == "variable":
            names, _ = tokens_of(rest)
            bound = bound_names(chunk, tactics=False) | header_binders(chunk, whole=True)
            # a name that an earlier `variable` of the scope bound is that variable here too:
            # `variable {G C : Type}` … `variable (gl : G → Γ)`
            bound |= set().union(*(sc.bound for sc in stack))
            used = [n for n in names if n.split(".", 1)[0] not in bound]
            stack[-1].vars.update(used)
            stack[-1].bound.update(bound)
            # the command has an entry of its own, of kind `var` and with no name: Lean elaborates it whether
            # a declaration uses the variables or not, so what it names has to be there, and may need a pin
            # (`variable … (hI : SIso D.s (sOf hF))` at the end of a file)
            if used:
                var_opens = [o for sc in stack for o in sc.opens]
                written = [w for sc in stack for w in sc.written]
                for o in opens_in:
                    var_opens.extend(open_candidates(o, chain_of(ns), written))
                nb = sum(1 for line in chunk.split("\n") if line.strip()) + (l0 - first)
                decls.append(("var", (), 0, (), first, l1, nb, chain_of(ns), tuple(var_opens), tuple(used), (),
                              (), ()))
            continue
        nb = sum(1 for line in chunk.split("\n") if line.strip()) + (l0 - first)
        flags = (F_PRIVATE if "private" in mods else 0) | (F_LOCAL if "local" in mods else 0) | \
                (F_SCOPED if "scoped" in mods else 0) | (F_PROTECTED if "protected" in mods else 0)
        anames, a_local, a_scoped = attr_names(attrs)
        opens = [o for s in stack for o in s.opens]
        written = [w for sc in stack for w in sc.written]
        for o in opens_in:
            opens.extend(open_candidates(o, chain_of(ns), written))
        scope_vars = set().union(*(s.vars for s in stack))
        scope_bound = set().union(*(s.bound for s in stack))
        if kw == "attribute":
            i = rest.find("[")
            j = close_bracket(rest, i) if i >= 0 else -1
            anames, a_local, a_scoped = attr_names([rest[i + 1:j]]) if i >= 0 else ([], False, False)
            names, _ = tokens_of(rest[j + 1:])
            if a_local:
                stack[-1].vars.update(n for n in names if n.split(".", 1)[0] not in scope_bound)
                continue
            decls.append(("attr", (), flags | F_WEAK, tuple(anames), first, l1, nb, chain_of(ns), tuple(opens),
                          tuple(names), (), (), ()))
            continue
        if kw == "export":
            m = re.match(r"\s*(\S+)\s*\(([^)]*)\)", rest)
            if m:
                src = m.group(1)
                given = m.group(2).split()
                decls.append(("export", tuple((ns + "." + x) if ns else x for x in given), flags, (), first, l1, nb,
                              chain_of(ns), tuple(opens), tuple(src + "." + x for x in given), (), (), ()))
            continue
        if kw in SYN_KW:
            names, fields = tokens_of(rest)
            names -= bound_names(chunk)
            if "local" in mods:
                stack[-1].vars.update(n for n in names if n.split(".", 1)[0] not in scope_bound)
                continue
            atoms = tuple(a[1:-1] for a in re.findall(r'"(?:\\.|[^"\\])*"', rest) if len(a) > 2)
            decls.append(("syn", atoms, flags, (kw,), first, l1, nb, chain_of(ns), tuple(opens),
                          tuple(names), (), tuple(fields), ()))
            continue
        if kw not in DECL_KW:
            continue
        r = rest.lstrip()
        if kw == "class" and re.match(r"(abbrev|inductive)\b", r):
            r = re.sub(r"^(abbrev|inductive)\s*", "", r)
        given = []
        if kw == "instance":
            m = re.match(r"\(priority\s*:=[^)]*\)\s*", r)
            if m:
                r = r[m.end():]
            m = WORD.match(r)
            if m:
                given = [m.group()]
        elif kw == "alias":
            m = re.match(r"⟨([^⟩]*)⟩", r)
            if m:
                given = [x.strip() for x in m.group(1).split(",") if x.strip() and x.strip() != "_"]
            else:
                m = WORD.match(r)
                given = [m.group()] if m else []
        elif kw != "example":
            m = WORD.match(r)
            if m:
                given = [m.group()]
        fulls, decl_ns = [], ns
        for g in given:
            g = re.sub(r"\.\{.*$", "", g).rstrip(".")
            if g.startswith("_root_."):
                fulls.append(g[7:])
                flags |= F_ROOT
            else:
                full = (ns + "." + g) if ns else g
                fulls.append(full)
                decl_ns = full.rsplit(".", 1)[0] if "." in full else ""
        if kw in ("structure", "class", "inductive"):
            sig, body = r, ""
        else:
            sig, body = split_sig(r)
        # `open A B in` inside a proof or a term opens for what follows it there; the names after it resolve
        # through it, and the files that declare them are needed (taken for the whole declaration)
        for m in BODY_OPEN.finditer(r):
            opens.extend(open_candidates(m.group(1), chain_of(ns), list(written)))
        bound = bound_names(sig, tactics=False) | bound_names(body) | header_binders(sig) | scope_bound
        if kw in ("structure", "class"):
            # the fields it declares are names of its own, not references: from the field after the one that
            # declares the name. In its own type, and before, the name means what it means outside
            # (`twist : ∀ …, Nonempty (π'.π.Equiv (twist π.π χ)) → …`), and is kept as a name to look up
            found = sorted(list(B_SFIELD.finditer(r)) + list(B_SBRACK.finditer(r)), key=lambda m: m.start())
            for k, m in enumerate(found):
                end = found[k + 1].start() if k + 1 < len(found) else len(r)
                before = r[:m.start()] + " " + r[m.end():end]
                for f in m.group(1).split():
                    if not re.search(r"(?<![\w'.])" + re.escape(f) + r"(?![\w'.])", before):
                        bound.add(f)
        s_names, s_fields = tokens_of(sig)
        b_names, b_fields = tokens_of(body)
        for binders in pre:
            bound |= header_binders(binders, whole=True) | bound_names(binders, tactics=False)
            more, more_fields = tokens_of(binders)
            s_names |= more
            s_fields |= more_fields
        bound.update(g.rsplit(".", 1)[-1] for g in given)
        for group, fields in ((s_names, s_fields), (b_names, b_fields)):
            for name in [x for x in group if x.split(".", 1)[0] in bound]:
                group.discard(name)
                fields.update(name.split(".")[1:])
                if "." in name and not name.startswith("_root_."):
                    # `T.isTangent_constant_coords` beside a `T` that the declaration binds somewhere may
                    # still be the constant of a namespace `T`: kept, marked, to be looked up whole (`resolve`)
                    group.add("?" + name)
        s_names |= scope_vars
        s_names.update(refs)
        b_names -= s_names
        if any(a in WEAK_ATTRS for a in anames) and not a_local:
            flags |= F_WEAK
        if a_local:
            flags |= F_LOCAL
        if a_scoped:
            flags |= F_SCOPED
        if kw == "instance" and flags & F_LOCAL:
            # a local instance is in force for the rest of its section
            name = fulls[0] if fulls else "%s.inst@%d" % (ns, first)
            fulls = [name]
            flags |= F_PRIVATE
            stack[-1].vars.add("_root_." + name)
        decls.append((kw, tuple(fulls), flags, tuple(anames), first, l1, nb, chain_of(decl_ns), tuple(opens),
                      tuple(s_names), tuple(b_names), tuple(s_fields), tuple(b_fields - s_fields)))
    return decls


DECL_FIELDS = ("kind", "names", "flags", "attrs", "l0", "l1", "lines", "chain", "opens", "sig", "body", "sig_fields",
               "body_fields")


def worker1(job):
    """Parse a shard of files; keep the full records on disk and return the light ones."""
    idx, src, out, rels = job
    full, light, attrs = [], [], Counter()
    for rel in rels:
        with open(os.path.join(src, rel), encoding="utf-8", errors="replace") as f:
            text = f.read()
        decls = parse_file(text)
        full.append((rel, decls))
        light.append((rel, text.count("\n") + 1, [(d[0], d[1], d[2], d[3], d[4], d[5], d[6]) for d in decls]))
        for d in decls:
            attrs.update(d[3])
    with open(os.path.join(out, "shards", "%05d.pkl" % idx), "wb") as f:
        pickle.dump(full, f, protocol=pickle.HIGHEST_PROTOCOL)
    return idx, light, attrs


ARCH, MATH, NSSET, SIMPS = {}, set(), set(), set()
# the protected constants, of the archive and of Mathlib: `Matrix.sub_mul` is not what `sub_mul` means under
# `open Matrix`. Lean finds a protected `N.a` only under a name of two parts or more (`resolveQualifiedName`)
PROT = set()
COPY_SUFFIX = "Cpt"   # `cpt_copy_thms` copies declarations under their name with this suffix
COPY_IDS = []         # the places where that command is run


def resolve(tok, chain, opens, priv, memo):
    key = (tok, chain, opens)
    hit = memo.get(key)
    if hit is not None:
        return hit
    if tok.startswith("?"):
        # a dotted name whose first part the declaration binds: a constant only if the whole of it is one
        ids, fields = resolve(tok[1:], chain, opens, priv, memo)
        result = memo[key] = (ids if not fields else (), ())
        return result
    root_only = tok.startswith("_root_.")
    if root_only:
        tok, chain, opens = tok[7:], (), ()
    comps = tok.split(".")
    n = len(comps)
    result = None
    for k in range(n, 0, -1):
        t = tok if k == n else ".".join(comps[:k])
        fields = tuple(comps[k:])
        atom = k == 1
        for p in chain:
            c = p + t
            if atom and c in PROT:
                continue
            i = priv.get(c)
            if i is None:
                i = ARCH.get(c)
            if i is not None:
                result = ((i,), fields)
                break
            if c in MATH:
                result = ((), fields)
                break
        if result is not None:
            break
        found, in_math = [], t in MATH
        i = priv.get(t)
        if i is None:
            i = ARCH.get(t)
        if i is not None:
            found.append(i)
        for o in opens:
            named = False
            if "|" in o:
                o, only = o.split("|", 1)
                if only.startswith("~"):
                    if (" " + t + " ") in only:
                        continue        # `open N hiding t`
                else:
                    named = True
                    if (" " + comps[0] + " ") not in only:
                        continue
            c = o + t
            if atom and not named and c in PROT:
                continue        # `open N (a)` names `N.a` outright, protected or not
            i = priv.get(c)
            if i is None:
                i = ARCH.get(c)
            if i is not None:
                found.append(i)
            elif c in MATH:
                in_math = True
        if found:
            result = (tuple(found), fields)
            break
        if in_math:
            result = ((), fields)
            break
        if k == n and "_" in comps[-1] and SIMPS:
            # a name that an attribute makes from a declaration: `foo_apply` from `foo`
            last = comps[-1]
            head = ".".join(comps[:-1])
            pos = last.find("_", 1)
            while pos > 0 and result is None:
                base = (head + "." if head else "") + last[:pos]
                for p in chain + opens + ("",):
                    if p + base in SIMPS:
                        result = ((ARCH[p + base],), ())
                        break
                pos = last.find("_", pos + 1)
            if result is not None:
                break
    if result is None and COPY_IDS and comps[-1].endswith(COPY_SUFFIX) and len(comps[-1]) > len(COPY_SUFFIX):
        ids, fields = resolve(tok[:-len(COPY_SUFFIX)], chain, opens, priv, memo)
        if ids:
            result = (ids + tuple(COPY_IDS), fields)
    if result is None:
        result = ((), tuple(comps[1:]))
    memo[key] = result
    return result


def worker2(job):
    """Resolve a shard's identifiers against the tables that the parent built before forking."""
    idx, out, base = job
    with open(os.path.join(out, "shards", "%05d.pkl" % idx), "rb") as f:
        full = pickle.load(f)
    sig_e, sig_o, body_e, body_o = array("i"), array("i", [0]), array("i"), array("i", [0])
    sig_f, body_f = [], []
    d_id = base
    for rel, decls in full:
        priv, memo, open_memo = {}, {}, {}
        k = d_id
        for d in decls:
            if d[2] & F_PRIVATE:
                for name in d[1]:
                    priv[name] = k
            k += 1
        for d in decls:
            chain = d[7]
            # (by the chain too: an `open` of a namespace that is around one declaration is dropped for it,
            # and is needed for the next one outside that namespace)
            opens = open_memo.get((d[8], chain))
            if opens is None:
                seen = set(chain)
                opens = []
                for o in d[8]:
                    if o.split("|", 1)[0] in NSSET and o not in seen:
                        seen.add(o)
                        opens.append(o)
                opens = open_memo[(d[8], chain)] = tuple(opens)
            for toks, flds, edges, offs, fout in ((d[9], d[11], sig_e, sig_o, sig_f),
                                                  (d[10], d[12], body_e, body_o, body_f)):
                ids, fields = set(), set(flds)
                for tok in toks:
                    r_ids, r_fields = resolve(tok, chain, opens, priv, memo)
                    ids.update(r_ids)
                    fields.update(r_fields)
                ids.discard(d_id)
                edges.extend(sorted(ids))
                offs.append(len(edges))
                fout.append(tuple(fields))
            d_id += 1
    return idx, sig_e, sig_o, body_e, body_o, sig_f, body_f


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("src")
    ap.add_argument("out")
    ap.add_argument("--names", action="append", default=[])
    ap.add_argument("--protected", action="append", default=[],
                    help="the protected constants of Mathlib, a name a line (lean/DumpNames.lean)")
    ap.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 4) - 2))
    ap.add_argument("--only", default="", help="read only the files under this prefix (for testing)")
    ap.add_argument("--shard", type=int, default=400)
    args = ap.parse_args()
    t0 = time.time()
    os.makedirs(os.path.join(args.out, "shards"), exist_ok=True)
    rels = []
    for root, dirs, files in os.walk(args.src):
        dirs.sort()
        for name in sorted(files):
            if name.endswith(".lean"):
                rel = os.path.relpath(os.path.join(root, name), args.src)
                if rel.startswith(args.only):
                    rels.append(rel)
    jobs = [(i, args.src, args.out, rels[k:k + args.shard]) for i, k in enumerate(range(0, len(rels), args.shard))]
    ctx = mp.get_context("fork")
    light = [None] * len(jobs)
    attr_count = Counter()
    with ctx.Pool(args.jobs) as pool:
        for idx, rows, attrs in pool.imap_unordered(worker1, jobs):
            light[idx] = rows
            attr_count.update(attrs)
    print("parsed %d files in %.0f s" % (len(rels), time.time() - t0), flush=True)

    files, file_lines, base = [], [], []
    names, kinds, flags, d_file, d_l0, d_l1, d_lines, d_attrs = [], [], [], [], [], [], [], []
    dup = 0
    for rows in light:
        base.append(len(names))
        for rel, nlines, decls in rows:
            fid = len(files)
            files.append(rel)
            file_lines.append(nlines)
            for kind, dnames, fl, attrs, l0, l1, nb in decls:
                i = len(names)
                names.append(dnames)
                kinds.append(kind)
                flags.append(fl)
                d_file.append(fid)
                d_l0.append(l0)
                d_l1.append(l1)
                d_lines.append(nb)
                d_attrs.append(attrs)
                if kind == "syn" or fl & F_PRIVATE:
                    continue
                if fl & F_PROTECTED:
                    PROT.update(dnames)
                for name in dnames:
                    if name in ARCH:
                        dup += 1
                    else:
                        ARCH[name] = i
                    if MAKERS.intersection(attrs):
                        SIMPS.add(name)
    COPY_IDS.extend(i for i in range(len(names)) if kinds[i] == "syn" and d_attrs[i] == ("cpt_copy_thms",))
    for path in args.names:
        with open(path, encoding="utf-8") as f:
            for line in f:
                MATH.add(line.split("\t", 1)[0].rstrip("\n"))
    for path in args.protected:
        with open(path, encoding="utf-8") as f:
            PROT.update(line.rstrip("\n") for line in f if line.strip())
    for table in (ARCH, MATH):
        for name in table:
            parts = name.split(".")
            for k in range(1, len(parts)):
                NSSET.add(".".join(parts[:k]) + ".")
    for name in ARCH:
        NSSET.add(name + ".")
    n = len(names)
    print("%d declarations, %d public names (%d repeated), %d Mathlib names, %d namespaces, %.0f s"
          % (n, len(ARCH), dup, len(MATH), len(NSSET), time.time() - t0), flush=True)

    sig_e, sig_o, body_e, body_o = array("i"), array("i", [0]), array("i"), array("i", [0])
    field_id, sig_f, body_f = {}, [None] * n, [None] * n
    results = [None] * len(jobs)
    with ctx.Pool(args.jobs) as pool:
        for r in pool.imap_unordered(worker2, [(i, args.out, base[i]) for i in range(len(jobs))]):
            results[r[0]] = r[1:]
    for i, (se, so, be, bo, sf, bf) in enumerate(results):
        off = len(sig_e)
        sig_e.extend(se)
        sig_o.extend(x + off for x in so[1:])
        off = len(body_e)
        body_e.extend(be)
        body_o.extend(x + off for x in bo[1:])
        for k, (a, b) in enumerate(zip(sf, bf)):
            sig_f[base[i] + k] = array("i", [field_id.setdefault(x, len(field_id)) for x in a])
            body_f[base[i] + k] = array("i", [field_id.setdefault(x, len(field_id)) for x in b])
        results[i] = None
    print("resolved: %d signature edges, %d body edges, %d field names, %.0f s"
          % (len(sig_e), len(body_e), len(field_id), time.time() - t0), flush=True)
    graph = dict(files=files, file_lines=file_lines, names=names, kinds=kinds, flags=flags, d_file=d_file, d_l0=d_l0,
                 d_l1=d_l1, d_lines=d_lines, d_attrs=d_attrs, sig_e=sig_e, sig_o=sig_o, body_e=body_e, body_o=body_o,
                 sig_f=sig_f, body_f=body_f, field_id=field_id, arch=ARCH, math_ns=None, prot=PROT)
    with open(os.path.join(args.out, "graph.pkl"), "wb") as f:
        pickle.dump(graph, f, protocol=pickle.HIGHEST_PROTOCOL)
    with open(os.path.join(args.out, "mathnames.pkl"), "wb") as f:
        pickle.dump(MATH, f, protocol=pickle.HIGHEST_PROTOCOL)
    report = dict(files=len(files), declarations=n, public_names=len(ARCH), repeated_names=dup,
                  kinds=Counter(kinds).most_common(), attributes=attr_count.most_common(80),
                  signature_edges=len(sig_e), body_edges=len(body_e), seconds=round(time.time() - t0))
    with open(os.path.join(args.out, "report.json"), "w") as f:
        json.dump(report, f, indent=1, ensure_ascii=False)
    print(json.dumps(report, ensure_ascii=False)[:3000])


if __name__ == "__main__":
    main()
