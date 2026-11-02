import ShortSieveCertSplit

/-!
# A cell's certificate as data: `cert_cell`

`cert_cell NAME k j r "…"` reads the certificate of the root cell `(k, j)` of region `r` (`true`: region C) from a
string: a skeleton of the certificate in a prefix form, compressed (DEFLATE) and written in base64. It rebuilds the
certificate, adds it as definitions (the subtrees below the cut points `NAME_0`, `NAME_1`, … and the top `NAME`), and
proves `NAME_run : run 1 NAME (.std 1) (cellCons k r) (cellBox k j) true = some L` by the node lemmas of
`ShortSieveCertSplit` down to the cut points, each cut point by `decide +kernel`, an auxiliary lemma with its own
kernel caches. Everything here runs at elaboration time; the kernel checks the definitions and the theorem as usual.

The skeleton leaves out what the checker's state determines: the new end of a range that `Cert.up` moves (the
constraint's bound on the box at that node, as `upOK` computes it) and the breakpoints of a chain drop (`chainBps` of
the node's box, as the encoder chose them). Rebuilding replays the checker's state (shape, constraints, box, sign)
node by node with the checker's own functions. The form, tokens separated by white space, after a header
`L total n L₀ … Lₙ₋₁` (the cell's loss and the losses of the cut points, in order):

* `o` `.out`; `C i` `.outC i`; `E j` `.outE j`; `T t` `.tighten t`; `w t` `.swap t`;
* `U j l i t` `.up j (l = 1) i v t` with `v` the bound; `u j l i v t` the same with `v` given;
* `m i j c t` `.comb i j c t`; `s C u w t₁ t₂` `.split C u w t₁ t₂`, with `C` as `c₀ n c₁ … cₙ cₑ s`;
* `c j p u w t₁ t₂` `.cut j p u w t₁ t₂`;
* `t A L ng` `.tii A L ng`; `g A L` `.g2 A L`; `d A L k t` `.dec A L k t`; `r A L k t` `.rev A L k t`;
* `x A N` `.drop A none`; `x A K` `.drop A (some bps)` with the node's breakpoints; `x A S B₁ B₂` with them given;
* lists as their length followed by their entries; `[` before a subtree: a cut point.

Each declaration here has a type in the namespace `Lean` (it belongs to the meta level).
-/

open Lean Elab Command

namespace ShortSieveCert.Data

/-- The bytes of a base64 text; other characters (white space, `=`) are skipped. -/
def base64Bytes (s : String) : CoreM ByteArray := do
  let mut out : ByteArray := .empty
  let mut acc := 0
  let mut bits := 0
  for c in s.toList do
    let v : Nat :=
      if 'A' ≤ c ∧ c ≤ 'Z' then c.toNat - 65 else if 'a' ≤ c ∧ c ≤ 'z' then c.toNat - 71
      else if '0' ≤ c ∧ c ≤ '9' then c.toNat + 4 else if c = '+' then 62 else if c = '/' then 63 else 64
    if v < 64 then
      acc := acc * 64 + v
      bits := bits + 6
      if 8 ≤ bits then
        bits := bits - 8
        out := out.push (acc / 2 ^ bits).toUInt8
        acc := acc % 2 ^ bits
  return out

/-- `n` bits of the input, least significant first (DEFLATE's order); the state is the next byte, the bits held and
their number. -/
def getBits (src : ByteArray) (n : Nat) : StateT (Nat × Nat × Nat) CoreM Nat := do
  let (pos, buf, cnt) ← get
  let mut pos := pos
  let mut buf := buf
  let mut cnt := cnt
  while cnt < n do
    if src.size ≤ pos then throwError "cert_cell: the compressed data ends early"
    buf := buf + src[pos]!.toNat * 2 ^ cnt
    pos := pos + 1
    cnt := cnt + 8
  set (pos, buf / 2 ^ n, cnt - n)
  return buf % 2 ^ n

/-- A canonical Huffman code from its code lengths: the number of codes of each length and the symbols in order. -/
def huffman (lens : Array Nat) : CoreM (Array Nat × Array Nat) := do
  let mut counts := Array.replicate 16 0
  for l in lens do counts := counts.modify l (· + 1)
  counts := counts.set! 0 0
  let mut offs := Array.replicate 17 0
  for l in [1:16] do offs := offs.set! (l + 1) (offs[l]! + counts[l]!)
  let mut syms := Array.replicate lens.size 0
  for s in [0:lens.size] do
    let l := lens[s]!
    if l ≠ 0 then
      syms := syms.set! offs[l]! s
      offs := offs.modify l (· + 1)
  return (counts, syms)

/-- One symbol of a canonical Huffman code, read a bit at a time. -/
def decodeSym (src : ByteArray) (code : Array Nat × Array Nat) : StateT (Nat × Nat × Nat) CoreM Nat := do
  let mut c := 0
  let mut first := 0
  let mut index := 0
  for len in [1:16] do
    c := c + (← getBits src 1)
    let count := code.1[len]!
    if c < first + count then return code.2[index + (c - first)]!
    index := index + count
    first := (first + count) * 2
    c := c * 2
  throwError "cert_cell: a bad Huffman code"

/-- The code lengths of a dynamic block's two codes. -/
def dynamicLens (src : ByteArray) : StateT (Nat × Nat × Nat) CoreM (Array Nat × Array Nat) := do
  let hlit := (← getBits src 5) + 257
  let hdist := (← getBits src 5) + 1
  let hclen := (← getBits src 4) + 4
  let order := #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]
  let mut clens := Array.replicate 19 0
  for i in [0:hclen] do clens := clens.set! order[i]! (← getBits src 3)
  let cc ← liftM (huffman clens)
  let mut lens : Array Nat := #[]
  while lens.size < hlit + hdist do
    let sym ← decodeSym src cc
    if sym < 16 then lens := lens.push sym
    else if sym = 16 then
      let prev := lens.back!
      for _ in [0:3 + (← getBits src 2)] do lens := lens.push prev
    else if sym = 17 then
      for _ in [0:3 + (← getBits src 3)] do lens := lens.push 0
    else
      for _ in [0:11 + (← getBits src 7)] do lens := lens.push 0
  return (lens.extract 0 hlit, lens.extract hlit (hlit + hdist))

/-- Raw DEFLATE (RFC 1951): stored, fixed and dynamic blocks. -/
def inflate (src : ByteArray) : CoreM ByteArray := do
  let lbase := #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163,
    195, 227, 258]
  let lext := #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0]
  let dbase := #[1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049,
    3073, 4097, 6145, 8193, 12289, 16385, 24577]
  let dext := #[0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13]
  let fixedL ← huffman (Array.replicate 144 8 ++ Array.replicate 112 9 ++ Array.replicate 24 7 ++
    Array.replicate 8 8)
  let fixedD ← huffman (Array.replicate 30 5)
  let go : StateT (Nat × Nat × Nat) CoreM ByteArray := do
    let mut out : ByteArray := .empty
    let mut fin := false
    while !fin do
      fin := (← getBits src 1) = 1
      let ty ← getBits src 2
      if ty = 0 then
        -- a stored block: drop the bits held (they belong to the last byte read), then LEN, NLEN, the bytes
        let (pos, _, _) ← get
        if src.size < pos + 4 then throwError "cert_cell: the compressed data ends early"
        let len := src[pos]!.toNat + 256 * src[pos + 1]!.toNat
        if src.size < pos + 4 + len then throwError "cert_cell: the compressed data ends early"
        for i in [0:len] do out := out.push src[pos + 4 + i]!
        set (pos + 4 + len, 0, 0)
      else
        let (lc, dc) ← if ty = 1 then pure (fixedL, fixedD) else do
          let (ll, dl) ← dynamicLens src
          pure (← liftM (huffman ll), ← liftM (huffman dl))
        let mut done := false
        while !done do
          let sym ← decodeSym src lc
          if sym < 256 then out := out.push sym.toUInt8
          else if sym = 256 then done := true
          else
            let li := sym - 257
            let len := lbase[li]! + (← getBits src lext[li]!)
            let di ← decodeSym src dc
            let dist := dbase[di]! + (← getBits src dext[di]!)
            if out.size < dist then throwError "cert_cell: a bad distance"
            for _ in [0:len] do out := out.push out[out.size - dist]!
    return out
  let (out, _) ← go.run (0, 0, 0)
  return out

/-- An integer as `Int.ofNat n` or `Int.negSucc n` on a raw literal. -/
def intE (v : Int) : Expr :=
  match v with
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (mkRawNatLit n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (mkRawNatLit n)

/-- A list of the type `ty`. -/
def listE (ty : Expr) (l : List Expr) : Expr :=
  l.foldr (fun a acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty a acc) (mkApp (mkConst ``List.nil [Level.zero]) ty)

/-- The next token. The state is the position in the tokens, the number of cut points so far, and the theorem's
tactic lines. -/
def tok (ts : Array String) : StateT (Nat × Nat × Array String) CoreM String := do
  let (i, c, ls) ← get
  if h : i < ts.size then
    set (i + 1, c, ls)
    return ts[i]
  else throwError "cert_cell: the skeleton ends early"

def natT (ts : Array String) : StateT (Nat × Nat × Array String) CoreM Nat := do
  let s ← tok ts
  match s.toNat? with
  | some n => return n
  | none => throwError "cert_cell: not a natural number: {s}"

def intT (ts : Array String) : StateT (Nat × Nat × Array String) CoreM Int := do
  let s ← tok ts
  match s.toInt? with
  | some n => return n
  | none => throwError "cert_cell: not an integer: {s}"

/-- A list of naturals: its value and its term. -/
def natsT (ts : Array String) : StateT (Nat × Nat × Array String) CoreM (List Nat × Expr) := do
  let n ← natT ts
  let mut l := #[]
  for _ in [0:n] do l := l.push (← natT ts)
  return (l.toList, listE (mkConst ``Nat) (l.toList.map mkRawNatLit))

/-- A list of integers: its value and its term. -/
def intsT (ts : Array String) : StateT (Nat × Nat × Array String) CoreM (List Int × Expr) := do
  let n ← natT ts
  let mut l := #[]
  for _ in [0:n] do l := l.push (← intT ts)
  return (l.toList, listE (mkConst ``Int) (l.toList.map intE))

/-- A constraint: its value and its term. -/
def conT (ts : Array String) : StateT (Nat × Nat × Array String) CoreM (Con × Expr) := do
  let c0 ← intT ts
  let (cs, csE) ← intsT ts
  let ce ← intT ts
  let st := (← natT ts) ≠ 0
  return (⟨⟨c0, cs, ce⟩, st⟩, mkApp2 (mkConst ``Con.mk) (mkApp3 (mkConst ``LF.mk) (intE c0) csE (intE ce))
    (if st then mkConst ``Bool.true else mkConst ``Bool.false))

/-- The breakpoints the encoder gives a chain drop: `chainBps` of the node's box (`dropStd`'s and `dropTwo`'s
chains). -/
def dropBpsE (S : Shp) (B : Box) : CoreM Expr := do
  let (b₁, b₂) : List ℤ × List ℤ := match S with
    | .std k => (chainBps (fun i => (B.getD i (0, 0)).1) (fun i => (B.getD i (0, 0)).2) (k + 1), [])
    | S =>
      let it := S.items
      let c₁ := S.chain 0
      let c₂ := S.chain 1
      (chainBps (fun i => loF it B 1 (c₁.getD i 0)) (fun i => hiF it B 1 (c₁.getD i 0)) c₁.length,
        chainBps (fun i => loF it B 1 (c₂.getD i 0)) (fun i => hiF it B 1 (c₂.getD i 0)) c₂.length)
  let li := mkApp (mkConst ``List [Level.zero]) (mkConst ``Int)
  return mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) li li (listE (mkConst ``Int) (b₁.map intE))
    (listE (mkConst ``Int) (b₂.map intE))

/-- The certificate of a node with shape `S`, constraints `Γ`, box `B` and sign `b`, replaying the checker's state.
In the top (`top`), a subtree marked `[` becomes the definition `base_i` (`i` the cut point's number), and each node
adds its tactic line: the node lemma, or `decide +kernel` for a cut point. -/
partial def certT (ts : Array String) (Ls : Array Nat) (base : Name) (top : Bool) (S : Shp) (Γ : List Con)
    (B : Box) (b : Bool) : StateT (Nat × Nat × Array String) CoreM Expr := do
  let c (n : Name) := mkConst (`ShortSieveCert.Cert ++ n)
  let line (s : String) : StateT (Nat × Nat × Array String) CoreM Nat := do
    let (i, k, ls) ← get
    set (i, k, ls.push s)
    return ls.size
  let lossFrom (k₀ : Nat) : StateT (Nat × Nat × Array String) CoreM Nat := do
    let (_, k, _) ← get
    return ((List.range (k - k₀)).map fun i => Ls[k₀ + i]!).sum
  let s ← tok ts
  match s with
  | "[" =>
    if !top then throwError "cert_cell: a cut point inside a cut point"
    let e ← certT ts Ls base false S Γ B b
    let (i, k, ls) ← get
    let n := base.appendIndexAfter k
    addDecl <| .defnDecl
      { name := n, levelParams := [], type := mkConst ``Cert, value := e, hints := .opaque, safety := .safe }
    modifyEnv (addNoncomputable · n)
    set (i, k + 1, ls.push "decide +kernel")
    return mkConst n
  | "o" =>
    if top then throwError "cert_cell: a leaf in the top"
    return c `out
  | "C" =>
    if top then throwError "cert_cell: a leaf in the top"
    return mkApp (c `outC) (mkRawNatLit (← natT ts))
  | "E" =>
    if top then throwError "cert_cell: a leaf in the top"
    return mkApp (c `outE) (mkRawNatLit (← natT ts))
  | "T" =>
    if top then throwError "cert_cell: a tightening in the top"
    return mkApp (c `tighten) (← certT ts Ls base top S Γ (tightenList 1 Γ B) b)
  | "w" =>
    if top then discard <| line "refine ShortSieveCert.run_swap_of (by decide +kernel) ?_"
    return mkApp (c `swap) (← certT ts Ls base top (.swap S) Γ B b)
  | "U" | "u" =>
    let j ← natT ts
    let l := (← natT ts) ≠ 0
    let i ← natT ts
    let v ← if s = "u" then intT ts else do
      let C := Γ.getD i ⟨LF.zero, false⟩
      let cj := C.L.c.getD j 0
      let r := (C.L.drop j).min B 1
      pure (if l then r / -cj else if C.strict then -(r / cj) else -r / cj + 1)
    if top then discard <| line "refine ShortSieveCert.run_up_of (by decide +kernel) ?_"
    let t ← certT ts Ls base top S Γ (cutAt B j l v) b
    return mkApp5 (c `up) (mkRawNatLit j) (if l then mkConst ``Bool.true else mkConst ``Bool.false)
      (mkRawNatLit i) (intE v) t
  | "m" =>
    let i ← natT ts
    let j ← natT ts
    let k ← natT ts
    if top then discard <| line "refine ShortSieveCert.run_comb_of (by decide +kernel) ?_"
    let C := combCon (Γ.getD i ⟨LF.zero, false⟩) (Γ.getD j ⟨LF.zero, false⟩) k
    let t ← certT ts Ls base top S (C :: Γ) B b
    return mkApp4 (c `comb) (mkRawNatLit i) (mkRawNatLit j) (mkRawNatLit k) t
  | "s" =>
    let (C, CE) ← conT ts
    let u ← natT ts
    let w ← natT ts
    let at_ ← if top then line "" else pure 0
    let (_, k₀, _) ← get
    let t₁ ← certT ts Ls base top S (C :: Γ) B b
    let L₁ ← lossFrom k₀
    let (_, k₁, _) ← get
    let t₂ ← certT ts Ls base top S (C.neg :: Γ) B b
    let L₂ ← lossFrom k₁
    if top then
      modify fun (i, k, ls) => (i, k, ls.set! at_ s!"refine ShortSieveCert.run_split_of (L₁ := {L₁}) (L₂ := {L₂}) \
        (by decide +kernel) ?_ ?_ rfl")
    return mkApp5 (c `split) CE (mkRawNatLit u) (mkRawNatLit w) t₁ t₂
  | "c" =>
    let j ← natT ts
    let p ← intT ts
    let u ← natT ts
    let w ← natT ts
    let at_ ← if top then line "" else pure 0
    let (_, k₀, _) ← get
    let t₁ ← certT ts Ls base top S Γ (B.modify j fun b' => (b'.1, min b'.2 p)) b
    let L₁ ← lossFrom k₀
    let (_, k₁, _) ← get
    let t₂ ← certT ts Ls base top S Γ (B.modify j fun b' => (max b'.1 p, b'.2)) b
    let L₂ ← lossFrom k₁
    if top then
      modify fun (i, k, ls) => (i, k, ls.set! at_ s!"refine ShortSieveCert.run_cut_of (L₁ := {L₁}) (L₂ := {L₂}) \
        (by decide +kernel) ?_ ?_ rfl")
    return mkApp6 (c `cut) (mkRawNatLit j) (intE p) (mkRawNatLit u) (mkRawNatLit w) t₁ t₂
  | "t" =>
    if top then throwError "cert_cell: a leaf in the top"
    let (_, a) ← natsT ts
    let (_, l) ← natsT ts
    return mkApp3 (c `tii) a l (mkRawNatLit (← natT ts))
  | "g" =>
    if top then throwError "cert_cell: a leaf in the top"
    let (_, a) ← natsT ts
    let (_, l) ← natsT ts
    return mkApp2 (c `g2) a l
  | "d" =>
    let (_, a) ← natsT ts
    let (_, l) ← natsT ts
    let kind ← natT ts
    let t ← match S with
      | .std k =>
        if top then discard <| line "refine ShortSieveCert.run_dec_std_of (by decide +kernel) ?_"
        certT ts Ls base top (.std (k + 1)) (geCon (k + 1) :: (Γ ++ [ordCon k])) (B ++ [(NU0, (B.getD k (0, 0)).2)])
          (!b)
      | S =>
        if top then
          discard <| line "refine ShortSieveCert.run_dec_two_of (by intro _ h; cases h) (by decide +kernel) ?_"
        certT ts Ls base top (.last S) (geL (S.items.getD (S.k + 1) LF.zero) B.length ::
          (Γ ++ [ordL (S.items.getD (S.sN 1) LF.zero) B.length]))
          (B ++ [(NU0, (S.items.getD (S.sN 1) LF.zero).maxB B 1)]) (!b)
    return mkApp4 (c `dec) a l (mkRawNatLit kind) t
  | "r" =>
    let (_, a) ← natsT ts
    let (_, l) ← natsT ts
    let kind ← natT ts
    let t ← match S with
      | .std (k + 1) =>
        if top then discard <| line "refine ShortSieveCert.run_rev_std_of (by decide +kernel) ?_"
        certT ts Ls base top (.rev k) (Γ ++ [halfCon k]) (B ++ [(NU0, (B.getD 0 (0, 0)).2)]) (!b)
      | _ => throwError "cert_cell: a role reversal of a node that is not standard"
    return mkApp4 (c `rev) a l (mkRawNatLit kind) t
  | "x" =>
    if top then throwError "cert_cell: a leaf in the top"
    let (_, a) ← natsT ts
    let li := mkApp (mkConst ``List [Level.zero]) (mkConst ``Int)
    let ty := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) li li
    match ← tok ts with
    | "N" => return mkApp2 (c `drop) a (mkApp (mkConst ``Option.none [Level.zero]) ty)
    | "K" => return mkApp2 (c `drop) a (mkApp2 (mkConst ``Option.some [Level.zero]) ty (← liftM (dropBpsE S B)))
    | "S" =>
      let (_, b₁) ← intsT ts
      let (_, b₂) ← intsT ts
      return mkApp2 (c `drop) a (mkApp2 (mkConst ``Option.some [Level.zero]) ty
        (mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) li li b₁ b₂))
    | s => throwError "cert_cell: a drop's breakpoints: N, K or S, not {s}"
  | s => throwError "cert_cell: unknown tag {s}"

/-- `cert_cell NAME k j r "…"`: the certificate of the root cell `(k, j)` of region `r`, its definitions and the
theorem `NAME_run`. -/
syntax (name := certCell) "cert_cell " ident num num ident str : command

@[command_elab certCell] def elabCertCell : CommandElab := fun stx => do
  match stx with
  | `(cert_cell $nm:ident $k:num $j:num $r:ident $s:str) =>
    let rb ← match r.getId with
      | `true => pure true
      | `false => pure false
      | _ => throwError "cert_cell: the region is true or false"
    let bytes ← liftCoreM (base64Bytes s.getString)
    let raw ← liftCoreM (inflate bytes)
    let some text := String.fromUTF8? raw | throwError "cert_cell: the data is not text"
    let ts := (((text.replace "\n" " ").splitOn " ").filter (· ≠ "")).toArray
    if ts.size < 3 || ts[0]! ≠ "L" then throwError "cert_cell: no header"
    let some total := ts[1]!.toNat? | throwError "cert_cell: a bad total"
    let some n := ts[2]!.toNat? | throwError "cert_cell: a bad number of cut points"
    let Ls := ((ts.extract 3 (3 + n)).map fun t => t.toNat?.getD 0)
    let base := (← getCurrNamespace) ++ nm.getId
    let kk := k.getNat
    let jj := j.getNat
    let (e, (i, cuts, lines)) ← liftCoreM <| (certT ts Ls base true (.std 1) (cellCons kk rb) (cellBox kk jj)
      true).run (3 + n, 0, #[])
    if i ≠ ts.size then throwError "cert_cell: {ts.size - i} tokens left over"
    if cuts ≠ n then throwError "cert_cell: {cuts} cut points, against {n} in the header"
    if Ls.toList.sum ≠ total then throwError "cert_cell: the cut points' losses do not add up to the total"
    liftCoreM <| addDecl <| .defnDecl
      { name := base, levelParams := [], type := mkConst ``Cert, value := e, hints := .regular 1, safety := .safe }
    modifyEnv (addNoncomputable · base)
    let thm := s!"set_option maxHeartbeats 0 in\nset_option Elab.async false in\n" ++
      s!"theorem {nm.getId}_run : ShortSieveCert.run 1 {nm.getId} (.std 1) (ShortSieveCert.cellCons {kk} {rb}) " ++
      s!"(ShortSieveCert.cellBox {kk} {jj}) true = some {total} := by\n" ++
      "\n".intercalate (lines.toList.map ("  " ++ ·))
    match Parser.runParserCategory (← getEnv) `command thm with
    | .ok cmd => elabCommand cmd
    | .error err => throwError "cert_cell: the theorem does not parse: {err}"
  | _ => throwUnsupportedSyntax

end ShortSieveCert.Data
