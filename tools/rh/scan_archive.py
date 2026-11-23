#!/usr/bin/env python3
"""Read the extracted archive as text and report what is in it. Nothing in the archive is run.

    python3 -I tools/rh/scan_archive.py SRC OUT.json

SRC is the archive's source directory (external/alpoge-rh/extract/lean/src). The script reads every .lean file once
and writes to OUT.json:

* `modules`: for each module, its lines, bytes and the modules it imports;
* `external`: the imported modules that are not in the archive, with the number of files that import each;
* `missing`: imports that look like the archive's own modules (same top-level name) and do not exist;
* `levels`: the number of modules at each depth of the import graph (a module's level is one more than the highest
  level among the archive's modules it imports), and the graph's cycles, if any;
* `patterns`: for each pattern below, the number of occurrences, the number of files, and the first files;
* `commands`: the `#` commands, `set_option` names and declaration keywords of metaprogramming, with counts.

The patterns are the ones that matter for running the archive's code safely and for what its theorems rest on:
escape hatches (`sorry`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, ...), and code that runs
while a file is elaborated (`#eval`, `run_cmd`, `initialize`, `IO.` calls, `elab`, `macro`, `addDecl`, ...).
A match is a place to read, not a finding: the patterns are matched on text, and a word in a name also matches.
"""
import json
import os
import re
import sys
from collections import Counter, defaultdict

PATTERNS = {
    # what a theorem may rest on besides the three standard axioms
    "sorry": r"\bsorry\b",
    "admit": r"\badmit\b",
    "axiom (declaration)": r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe|public|meta)\s+)*axiom\b",
    "axiom (word)": r"\baxiom\b",
    "sorryAx": r"\bsorryAx\b",
    "native_decide": r"\bnative_decide\b",
    "ofReduceBool / reduceBool / trustCompiler": r"\b(?:ofReduceBool|reduceBool|reduceNat|trustCompiler)\b",
    "implemented_by / extern / export / csimp": r"\b(?:implemented_by|extern|csimp)\b|@\[[^\]]*\bexport\b",
    "unsafe": r"\bunsafe\b",
    "opaque (declaration)": r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe|public|meta)\s+)*opaque\b",
    "skipKernelTC / debug options": r"\bskipKernelTC\b|set_option\s+debug\.",
    "decide +kernel": r"decide\s*\+kernel|\+kernel\b",
    # code that runs while a file is compiled
    "#eval": r"#eval",
    "#exit": r"#exit",
    "run_cmd / run_elab / run_meta": r"\b(?:run_cmd|run_elab|run_meta)\b",
    "initialize": r"\b(?:builtin_)?initialize\b",
    "IO.": r"\bIO\.[A-Za-z_][\w.]*|\bSystem\.FilePath\b|\bIO\s+(?:Unit|String|Nat|Bool)\b",
    "process / file / network words": r"\b(?:Process\.spawn|Process\.output|Process\.run|readFile|writeFile|readBinFile|writeBinFile|createDir|removeFile|removeDirAll|getEnv|loadDynlib|loadPlugin|curl|wget|http://|https://)",
    "elab / macro / syntax (declaration)": r"^\s*(?:(?:scoped|local|private|public|meta)\s+)*(?:elab|elab_rules|macro|macro_rules|syntax|declare_syntax_cat|simproc|dsimproc)\b",
    "environment edits": r"\b(?:addDecl|addAndCompile|evalExpr|evalConst|evalDecl|modifyEnv|setEnv|compileDecl|Environment\.add\w*|Kernel\.\w+)\b",
    "open Lean": r"^\s*open\s+(?:[\w.]+\s+)*Lean\b",
}

COMMAND = re.compile(r"^\s*(#[A-Za-z_]\w*)")
SET_OPTION = re.compile(r"\bset_option\s+([\w.]+)\s+(\S+)")
IMPORT = re.compile(r"^\s*(?:public\s+|private\s+|meta\s+)*import\s+(?:all\s+|runtime\s+)?(.*)$")
TACTICS = ["simp", "simp only", "simpa", "grind", "omega", "aesop", "linarith", "nlinarith", "positivity", "norm_num",
           "ring", "ring_nf", "field_simp", "fun_prop", "decide", "bound", "gcongr", "tauto", "exact", "refine",
           "rw", "calc", "induction", "rcases", "obtain", "infer_instance", "rfl", "apply", "intro", "constructor",
           "exact?", "apply?", "rw?", "simp?", "aesop?", "continuity", "measurability", "polyrith", "norm_cast",
           "push_cast", "ext", "funext", "congr", "convert", "unfold", "show", "have", "native_decide", "bv_decide"]
TACTIC_RE = {t: re.compile(r"(?<![\w.?!'])" + re.escape(t) + r"(?![\w?!'])") for t in TACTICS}


def main():
    src, out = sys.argv[1], sys.argv[2]
    compiled = {k: re.compile(v, re.M) for k, v in PATTERNS.items()}
    modules = {}
    hits = {k: [0, 0, []] for k in PATTERNS}
    commands, options, tactics = Counter(), Counter(), Counter()
    option_values = defaultdict(Counter)
    odd_names, non_utf8 = [], []
    for root, dirs, files in os.walk(src):
        dirs.sort()
        for name in sorted(files):
            if not name.endswith(".lean"):
                continue
            path = os.path.join(root, name)
            rel = os.path.relpath(path, src)
            mod = rel[:-5].replace(os.sep, ".")
            if not re.fullmatch(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*", mod):
                odd_names.append(rel)
            with open(path, "rb") as f:
                raw = f.read()
            try:
                text = raw.decode("utf-8")
            except UnicodeDecodeError:
                non_utf8.append(rel)
                text = raw.decode("utf-8", "replace")
            lines = text.split("\n")
            imports, header_done = [], False
            for line in lines:
                s = line.strip()
                if not header_done:
                    m = IMPORT.match(line)
                    if m:
                        imports.extend(m.group(1).split())
                        continue
                    if s == "" or s == "module" or s.startswith("--") or s.startswith("prelude"):
                        continue
                    header_done = True
                m = COMMAND.match(line)
                if m:
                    commands[m.group(1)] += 1
            for m in SET_OPTION.finditer(text):
                options[m.group(1)] += 1
                option_values[m.group(1)][m.group(2)] += 1
            for k, rx in compiled.items():
                n = len(rx.findall(text))
                if n:
                    hits[k][0] += n
                    hits[k][1] += 1
                    if len(hits[k][2]) < 12:
                        hits[k][2].append(rel)
            for t, rx in TACTIC_RE.items():
                n = len(rx.findall(text))
                if n:
                    tactics[t] += n
            modules[mod] = {"lines": len(lines), "bytes": len(raw), "imports": imports}

    tops = {m.split(".")[0] for m in modules}
    external, missing = Counter(), Counter()
    for mod, info in modules.items():
        for i in info["imports"]:
            if i not in modules:
                (missing if i.split(".")[0] in tops else external)[i] += 1

    # levels by a depth-first search that also reports cycles
    level, state, cycles = {}, {}, []
    for start in modules:
        if start in level:
            continue
        stack = [(start, iter(modules[start]["imports"]))]
        state[start] = 1
        while stack:
            node, it = stack[-1]
            for i in it:
                if i not in modules:
                    continue
                if state.get(i) == 1:
                    cycles.append([node, i])
                elif i not in level:
                    state[i] = 1
                    stack.append((i, iter(modules[i]["imports"])))
                    break
            else:
                level[node] = 1 + max((level.get(i, 0) for i in modules[node]["imports"] if i in modules), default=0)
                state[node] = 2
                stack.pop()
    by_level = Counter(level.values())
    lines_by_level = Counter()
    for m, l in level.items():
        lines_by_level[l] += modules[m]["lines"]

    # what Main reaches
    reach, todo = set(), ["Main"] if "Main" in modules else []
    while todo:
        m = todo.pop()
        if m in reach:
            continue
        reach.add(m)
        todo.extend(i for i in modules[m]["imports"] if i in modules)

    by_top = defaultdict(lambda: [0, 0])
    for m, info in modules.items():
        t = m.split(".")[0]
        by_top[t][0] += 1
        by_top[t][1] += info["lines"]

    report = {
        "files": len(modules),
        "lines": sum(i["lines"] for i in modules.values()),
        "bytes": sum(i["bytes"] for i in modules.values()),
        "by_top": {k: v for k, v in sorted(by_top.items())},
        "odd_names": odd_names[:20],
        "non_utf8": non_utf8[:20],
        "external": dict(external.most_common()),
        "missing": dict(missing.most_common(50)),
        "cycles": cycles[:20],
        "levels": {str(k): [by_level[k], lines_by_level[k]] for k in sorted(by_level)},
        "reached_from_Main": len(reach),
        "patterns": {k: {"occurrences": v[0], "files": v[1], "first_files": v[2]} for k, v in hits.items()},
        "commands": dict(commands.most_common()),
        "set_option": dict(options.most_common()),
        "set_option_values": {k: dict(v.most_common(6)) for k, v in option_values.items()},
        "tactics": dict(tactics.most_common()),
        "largest": sorted(((i["lines"], m) for m, i in modules.items()), reverse=True)[:15],
        "modules": {m: {"lines": i["lines"], "bytes": i["bytes"], "imports": i["imports"], "level": level[m]}
                    for m, i in modules.items()},
    }
    with open(out, "w") as f:
        json.dump(report, f)
    summary = {k: v for k, v in report.items() if k != "modules"}
    print(json.dumps(summary, indent=1)[:200000])


if __name__ == "__main__":
    main()
