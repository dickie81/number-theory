import ShortSieveCertCheck

/-!
# The encoder: the generator's trees as certificates for `ShortSieveCert.run`

Reads a tree dumped by the generator (`cert4 tree=...`, converted by `tree2txt.py`), walks it with the Lean state of
the node (shape, constraints, box, sign), and turns each decision into the checker's decisions, using the checker's
own functions to choose the details (the constraint that moves an end, the constraint that fails, the labels, the
active constraints, the drop's bound). The result is checked by `run`.
-/

open ShortSieveCert

namespace Enc

instance : Inhabited Cert := ⟨.out⟩
instance : Inhabited LF := ⟨LF.zero⟩
instance : Inhabited Con := ⟨⟨LF.zero, false⟩⟩
instance : Inhabited Shp := ⟨.std 0⟩

/-! ## The generator's trees -/

structure GNode where
  ty : Nat
  dec : Nat
  sc : Nat
  k1 : Nat
  q2 : Nat
  k2 : Nat
  sp : Int
  w : Nat
deriving Inhabited

structure GTree where
  nodes : Array GNode
  forms : Array LF
deriving Inhabited

def trimZ (l : List Int) : List Int := (l.reverse.dropWhile (· == 0)).reverse

def strip (s : String) : String := String.ofList (s.toList.filter fun c => !c.isWhitespace)

def toInt (s : String) : Int := ((strip s).toInt?).getD 0

def parseTree (txt : String) : GTree := Id.run do
  let lines := ((txt.splitOn "\n").filter (fun l => strip l ≠ "")).toArray
  let hdr := ((lines[0]!).splitOn " ").map toInt
  let nT := (hdr[0]!).toNat
  let nF := (hdr[1]!).toNat
  let mut nodes : Array GNode := #[]
  for i in [0:nT] do
    let v := (((lines[1 + i]!).splitOn " ").map toInt).toArray
    nodes := nodes.push ⟨v[0]!.toNat, v[1]!.toNat, v[2]!.toNat, v[3]!.toNat, v[4]!.toNat, v[5]!.toNat, v[6]!,
      v[7]!.toNat⟩
  let mut forms : Array LF := #[]
  for i in [0:nF] do
    let v := ((lines[1 + nT + i]!).splitOn " ").map toInt
    forms := forms.push ⟨v.head!, trimZ v.tail, 0⟩
  return ⟨nodes, forms⟩

def intS (v : Int) : String := if v < 0 then s!"({v})" else s!"{v}"
def listS (l : List Nat) : String := "[" ++ ", ".intercalate (l.map toString) ++ "]"
def listIS (l : List Int) : String := "[" ++ ", ".intercalate (l.map toString) ++ "]"
def conS (C : Con) : String := s!"⟨⟨{intS C.L.c0}, {listIS C.L.c}, {intS C.L.ce}⟩, {C.strict}⟩"
def boxS (B : Box) : String := "[" ++ ", ".intercalate (B.map fun b => s!"({intS b.1}, {intS b.2})") ++ "]"


/-! ## The generator's node types -/

def gX (j : Nat) : LF := unitLF j
def gS (k : Nat) : LF := ⟨DEN, List.replicate k (-1), 0⟩
def gsub (a b : LF) : LF := a.add (b.smul (-1))

/-- The forms agree, ignoring the slack and trailing zeros. -/
def feq (a b : LF) : Bool := a.c0 == b.c0 && trimZ a.c == trimZ b.c

/-- The Type I requirements of a decomposition (generator's `ND[t].ch[c].req`). -/
def reqs : Nat → Nat → List (List LF)
  | 0, 5 => [[gX 0, gX 1]]
  | 1, 5 => [[gX 0, gX 1, gX 2]]
  | 1, 6 => [[gS 3, gX 1, gX 2]]
  | 2, 5 => [[gX 0, gX 1, gX 2, gX 3, gX 3]]
  | 2, 6 => [[gX 0, gX 1, gX 2, gX 3], [gS 4, gX 1, gX 2, gX 3]]
  | 3, 5 => [[gS 3, gX 1, gX 2, gX 3, gX 3]]
  | 3, 6 => [[gsub (gX 0) (gX 3), gX 1, gX 2, gX 3, gX 2]]
  | 8, 5 => [[gX 0, gX 1, gX 2, gX 3, gX 4, gX 5, gX 5]]
  | 9, 5 => [[gS 5, gX 1, gX 2, gX 3, gX 4, gX 5, gX 5]]
  | 9, 6 => [[gsub (gX 0) (gX 5), gX 1, gX 2, gX 3, gX 4, gX 5, gX 4]]
  | _, _ => []

inductive Op | dec | rev | swapdec
deriving Inhabited, BEq

/-- The decompositions: the child's type and the checker's decision. -/
def trans : Nat → Nat → Option (Nat × Op)
  | 0, 5 => some (1, .dec)
  | 1, 5 => some (2, .dec)
  | 1, 6 => some (3, .rev)
  | 2, 5 => some (4, .dec)
  | 2, 6 => some (5, .dec)
  | 3, 5 => some (6, .dec)
  | 3, 6 => some (7, .swapdec)
  | 4, 5 => some (8, .dec)
  | 5, 5 => some (9, .rev)
  | 6, 5 => some (10, .dec)
  | 7, 5 => some (11, .dec)
  | 8, 5 => some (12, .dec)
  | 9, 5 => some (14, .dec)
  | 9, 6 => some (16, .swapdec)
  | 12, 5 => some (13, .dec)
  | 14, 5 => some (15, .dec)
  | 16, 5 => some (17, .dec)
  | _, _ => none

def xs (a b : Nat) : List LF := (List.range (b - a)).map fun i => gX (a + i)

/-- The generator's items of each node type (forms only). -/
def gitems : Nat → List LF
  | 0 => [gX 0, gX 1, gS 2]
  | 1 => xs 0 3 ++ [gS 3]
  | 2 => xs 0 4 ++ [gS 4]
  | 3 => [gS 3] ++ xs 1 4 ++ [gsub (gX 0) (gX 3)]
  | 4 => xs 0 5 ++ [gS 5]
  | 5 => xs 0 5 ++ [gS 5]
  | 6 => [gS 3] ++ xs 1 5 ++ [gsub (gsub (gX 0) (gX 3)) (gX 4)]
  | 7 => [gsub (gX 0) (gX 3)] ++ xs 1 5 ++ [gsub (gS 3) (gX 4)]
  | 8 => xs 0 6 ++ [gS 6]
  | 9 => [gS 5] ++ xs 1 6 ++ [gsub (gX 0) (gX 5)]
  | 10 => [gS 3] ++ xs 1 6 ++ [gsub (gsub (gsub (gX 0) (gX 3)) (gX 4)) (gX 5)]
  | 11 => [gsub (gX 0) (gX 3)] ++ xs 1 6 ++ [gsub (gsub (gS 3) (gX 4)) (gX 5)]
  | 12 => xs 0 7 ++ [gS 7]
  | 13 => xs 0 8 ++ [gS 8]
  | 14 => [gS 5] ++ xs 1 7 ++ [gsub (gsub (gX 0) (gX 5)) (gX 6)]
  | 15 => [gS 5] ++ xs 1 8 ++ [gsub (gsub (gsub (gX 0) (gX 5)) (gX 6)) (gX 7)]
  | 16 => [gsub (gX 0) (gX 5)] ++ xs 1 7 ++ [gsub (gS 5) (gX 6)]
  | 17 => [gsub (gX 0) (gX 5)] ++ xs 1 8 ++ [gsub (gsub (gS 5) (gX 6)) (gX 7)]
  | _ => [gX 0, gX 1, gS 2]

/-- The canonical positions of the generator's items in the shape's items. -/
def canonOf (S : Shp) (gi : List LF) : Option (List Nat) :=
  let its := S.items
  gi.mapM fun g => (List.range its.length).find? fun p => feq (its.getD p LF.zero) g

/-! ## Labels from the generator's witnesses -/

/-- Labels for a Type I check on `items` with cofactor `c0`, from the generator's variables and roles: by form; then a
single leftover item takes the single leftover variable (the next prime, below the variable's prime); then leftover
items whose forms add up to a leftover variable take its role. -/
def matchLabels (items : List LF) (c0 : Nat) (vars : List LF) (roles : List Nat) : Option (List Nat) := Id.run do
  let n := items.length
  let mut used : Array Bool := Array.replicate vars.length false
  let mut lab : Array (Option Nat) := Array.replicate n none
  for p in [0:n] do
    if p == c0 then
      lab := lab.set! p (some 3)
    else
      let it := items.getD p LF.zero
      match (List.range vars.length).find? (fun i => !used[i]! && feq it (vars.getD i LF.zero)) with
      | some i =>
        used := used.set! i true
        lab := lab.set! p (some (roles.getD i 0))
      | none => pure ()
  let leftI := (List.range n).filter fun p => lab[p]!.isNone
  let leftV := (List.range vars.length).filter fun i => !used[i]!
  if leftI.isEmpty then return some (lab.toList.map (·.getD 0))
  if leftI.length == 1 && leftV.length == 1 then
    lab := lab.set! leftI.head! (some (roles.getD leftV.head! 0))
    return some (lab.toList.map (·.getD 0))
  let sum := leftI.foldl (fun acc p => acc.add (items.getD p LF.zero)) LF.zero
  match leftV.find? (fun i => feq sum (vars.getD i LF.zero)) with
  | some i =>
    for p in leftI do lab := lab.set! p (some (roles.getD i 0))
    return some (lab.toList.map (·.getD 0))
  | none => return none

/-- The generator's Type I code: the kind and the roles; kind `0` (all) is the checker's kind `1` with every
variable in group `0`. -/
def decodeTI (code : Nat) (nv : Nat) : Nat × List Nat :=
  let kind := code % 4
  if kind == 0 then (1, List.replicate nv 0)
  else (kind, (List.range nv).map fun i => (code / 4 ^ (i + 1)) % 4)

/-! ## The checker's boxes -/

def coordUp (C : Con) (E : Int) (B : Box) (j : Nat) : Option (Bool × Int) :=
  let cj := C.L.c.getD j 0
  let r := (C.L.drop j).min B E
  if 0 < cj then some (false, if C.strict then -(r / cj) else -r / cj + 1)
  else if cj < 0 then some (true, r / -cj)
  else none

structure Up where
  j : Nat
  lower : Bool
  i : Nat
  v : Int

/-- One round of moving the ends: for each coordinate, the best constraint for each end, applied at once, when it
moves the end by at least `minGain/1024` of the range. -/
def upRoundG (minGain : Nat) (E : Int) (Γ : List Con) (B : Box) : List Up × Box := Id.run do
  let mut B := B
  let mut ups : List Up := []
  for j in [0:B.length] do
    for lower in [true, false] do
      let mut best : Option (Nat × Int) := none
      for i in [0:Γ.length] do
        match coordUp (Γ.getD i ⟨LF.zero, false⟩) E B j with
        | some (l, v) =>
          if l == lower then
            match best with
            | none => best := some (i, v)
            | some (_, v') => if (lower && v > v') || (!lower && v < v') then best := some (i, v)
        | none => pure ()
      match best with
      | some (i, v) =>
        let b := B.getD j (0, 0)
        let gain := if lower then v - b.1 else b.2 - v
        if gain > 0 && gain * 1024 ≥ (minGain : Int) * (b.2 - b.1) then
          ups := ⟨j, lower, i, v⟩ :: ups
          B := cutAt B j lower v
      | none => pure ()
  return (ups.reverse, B)

def upRound (E : Int) (Γ : List Con) (B : Box) : List Up × Box := upRoundG 0 E Γ B

/-- Rounds until nothing moves (at most `n`). -/
def upRoundsG (minGain : Nat) (E : Int) (Γ : List Con) (B : Box) : Nat → List Up × Box
  | 0 => ([], B)
  | n + 1 =>
    let (u, B') := upRoundG minGain E Γ B
    if u.isEmpty then ([], B) else
      let (u', B'') := upRoundsG minGain E Γ B' n
      (u ++ u', B'')

def upRounds (E : Int) (Γ : List Con) (B : Box) (n : Nat) : List Up × Box := upRoundsG 0 E Γ B n

def wrapUps (ups : List Up) (t : Cert) : Cert := ups.foldr (fun u acc => .up u.j u.lower u.i u.v acc) t

def isEmptyAt (B : Box) : Option Nat := (List.range B.length).find? fun j => (B.getD j (0, 0)).2 ≤ (B.getD j (0, 0)).1

def failsAt (E : Int) (Γ : List Con) (B : Box) : Option Nat :=
  (List.range Γ.length).find? fun i => (Γ.getD i ⟨LF.zero, false⟩).fails B E

/-- The constraints that cut the box (two or more coordinates, neither true nor false on all of it). -/
def activesOf (E : Int) (Γ : List Con) (B : Box) : List Nat :=
  (List.range Γ.length).filter fun i =>
    let C := Γ.getD i ⟨LF.zero, false⟩
    (C.L.c.filter (· ≠ 0)).length ≥ 2 && C.L.min B E < 0 && 0 < -((C.L.smul (-1)).min B E)

/-- Orders of the active constraints to try (the checker's multiplier search is greedy, in order). -/
def actCands (E : Int) (Γ : List Con) (B : Box) : List (List Nat) :=
  let A := activesOf E Γ B
  let isOrd := fun i => let C := Γ.getD i ⟨LF.zero, false⟩
    C.L.c0 == 0 && (C.L.c.filter (· ≠ 0)).length == 2
  let ords := A.filter isOrd
  let rest := A.filter (fun i => !isOrd i)
  let perms := if A.length ≤ 4 then A.permutations else []
  [[], A, A.reverse, ords ++ rest, rest ++ ords, ords.reverse ++ rest] ++ perms

/-- The first passing list of active constraints: none, then ordered lists of one, two and three, then the longer
candidate orders (shrunk). -/
def findActs (E : Int) (Γ : List Con) (B : Box) (ok : List Nat → Bool) : Option (List Nat) := Id.run do
  if ok [] then return some []
  let A := activesOf E Γ B
  for a in A do
    if ok [a] then return some [a]
  for a in A do
    for b in A do
      if a != b && ok [a, b] then return some [a, b]
  if A.length ≤ 10 then
    for a in A do
      for b in A do
        for c in A do
          if a != b && b != c && a != c && ok [a, b, c] then return some [a, b, c]
  for cand in actCands E Γ B do
    if ok cand then
      let mut cur := cand
      for x in cand do
        let c := cur.filter (· ≠ x)
        if ok c then cur := c
      return some cur
  return none

/-- A passing list of active constraints, shrunk greedily: each constraint is dropped when the check still passes. -/
def shrinkActs (ok : List Nat → Bool) (acts : List Nat) : List Nat := Id.run do
  let mut cur := acts
  for a in acts do
    let c := cur.filter (· ≠ a)
    if ok c then cur := c
  return cur

/-- Two positions whose weights in the form differ (the split's condition is not degenerate). -/
def findUW (S : Shp) (L : LF) : Option (Nat × Nat) :=
  let n := S.k + S.m
  let ps := (List.range n).flatMap fun u => (List.range n).map fun w => (u, w)
  ps.find? fun (u, w) => wtN S L u ≠ wtN S L w

/-! ## The walk -/

structure Opt where
  tol : Nat := 0          -- the product bound is kept when it exceeds the chain bound by at most this (units 1/SC)
  rounds : Nat := 3       -- rounds of moving the ends at every node
  partRounds : Nat := 3   -- ... and at every part of a drop
  lit : Bool := false     -- a literal box after the moved ends
  prune : Nat := 0        -- breakpoints are dropped while each costs at most prune/10000 of the bound
  minGain : Nat := 0      -- an end is moved only by at least minGain/1024 of its range
deriving Inhabited

structure St where
  pos : Nat := 0
  chainExtra : Nat := 0   -- the loss the product bounds add over the chain bounds
  ups : Nat := 0
  nodes : Nat := 0
  fails : Array String := #[]
  drops : Nat := 0
  prodDrops : Nat := 0
deriving Inhabited

abbrev M := StateM St

def failM (msg : String) : M Cert := do
  modify fun s => { s with fails := s.fails.push msg }
  return .out

def next (tr : GTree) : M GNode := do
  let s ← get
  set { s with pos := s.pos + 1 }
  return tr.nodes[s.pos]!

/-- A pending Type I requirement for the child's decomposition: variables, roles, kind. -/
structure Pend where
  vars : List LF
  roles : List Nat
  kind : Nat
deriving Inhabited

/-- The moved ends, then (with `lit`) the box as a literal. -/
def wrapUpsL (o : Opt) (ups : List Up) (B : Box) (t : Cert) : Cert :=
  let _ := o.lit
  let _ := B
  wrapUps ups t

/-- The breakpoints of a drop's chains, as the checker would compute them. -/
def dropBps (E : Int) (S : Shp) (B : Box) : List Int × List Int :=
  match S with
  | .std k => (chainBps (fun i => (B.getD i (0, 0)).1) (fun i => (B.getD i (0, 0)).2) (k + 1), [])
  | S =>
    let it := S.items
    let c₁ := S.chain 0
    let c₂ := S.chain 1
    (chainBps (fun i => loF it B E (c₁.getD i 0)) (fun i => hiF it B E (c₁.getD i 0)) c₁.length,
      chainBps (fun i => loF it B E (c₂.getD i 0)) (fun i => hiF it B E (c₂.getD i 0)) c₂.length)

/-- The best drop of a box (product or chain bound, with or without the active constraints). -/
def bestDrop (o : Opt) (E : Int) (S : Shp) (Γ : List Con) (B : Box) : Option (Cert × Nat × Nat) := Id.run do
  let acts := activesOf E Γ B
  let bp0 := some (dropBps E S B)
  -- the best product bound and the best chain bound
  let mut bp : Option (List Nat × Nat) := none
  let mut bc : Option (List Nat × Nat) := none
  for a in [[], acts] do
    match run E (.drop a none) S Γ B true with
    | some L => if bp.all (fun x => L < x.2) then bp := some (a, L)
    | none => pure ()
    match run E (.drop a bp0) S Γ B true with
    | some L => if bc.all (fun x => L < x.2) then bc := some (a, L)
    | none => pure ()
  let shrinkD := fun (c : Option (List Int × List Int)) (a : List Nat) (L : Nat) =>
    shrinkActs (fun a' => (run E (.drop a' c) S Γ B true).all (· ≤ L)) a
  let bp' := bp.map fun (a, L) => (shrinkD none a L, L)
  let bc' := bc.map fun (a, L) => (shrinkD bp0 a L, L)
  -- drop interior breakpoints while each removal costs at most prune/10000 of the bound
  let (bp0, bc') := Id.run do
    match bc', bp0 with
    | some (a, L), some (b₁, b₂) =>
      if o.prune == 0 then return (bp0, bc')
      let mut cur := (b₁, b₂)
      let mut curL := L
      let mut changed := true
      while changed do
        changed := false
        for side in [0, 1] do
          let bs := if side == 0 then cur.1 else cur.2
          for idx in (List.range bs.length).reverse do
            if idx == 0 || idx + 1 ≥ bs.length then continue
            let bs' := bs.eraseIdx idx
            let cand := if side == 0 then (bs', cur.2) else (cur.1, bs')
            match run E (.drop a (some cand)) S Γ B true with
            | some L' =>
              if L' * 10000 ≤ curL * (10000 + o.prune) then
                cur := cand
                curL := L'
                changed := true
                break
            | none => pure ()
          if changed then break
      return (some cur, some (a, curL))
    | _, _ => return (bp0, bc')
  match bp', bc' with
  | some (a, L), some (a', L') =>
    if L ≤ L' + o.tol then return some (.drop a none, L, L - min L L') else return some (.drop a' bp0, L', 0)
  | some (a, L), none => return some (.drop a none, L, 0)
  | none, some (a, L) => return some (.drop a bp0, L, 0)
  | none, none => return none

/-- Close an empty box (after moving its ends), or `none`. -/
def closeEmpty (E : Int) (Γ : List Con) (B : Box) : Option Cert :=
  match isEmptyAt B with
  | some j => some (.outE j)
  | none => match failsAt E Γ B with
    | some i => some (.outC i)
    | none => none

/-- A virtual split's parts along `q`, `k` equal parts, as the generator's `dropCostVS`. -/
def parts (lo hi : Int) (k : Nat) : List (Int × Int) :=
  (List.range k).filterMap fun i =>
    let a := lo + (hi - lo) * i / k
    let b := lo + (hi - lo) * (i + 1) / k
    if a < b then some (a, b) else none

/-- A part of a drop: move the ends, close it if empty, else drop it. -/
def dropPart (o : Opt) (E : Int) (S : Shp) (Γ : List Con) (B : Box) : M Cert := do
  let (ups, B') := upRoundsG o.minGain E Γ B o.partRounds
  modify fun s => { s with ups := s.ups + ups.length, nodes := s.nodes + 1 }
  match closeEmpty E Γ B' with
  | some c => return wrapUps ups c
  | none =>
    let wrapUps := fun (u : List Up) (c : Cert) => wrapUpsL o u B' c
    match bestDrop o E S Γ B' with
    | some (c, _, extra) =>
      let isProd : Nat := match c with
        | .drop _ none => 1
        | _ => 0
      modify fun s => { s with drops := s.drops + 1, prodDrops := s.prodDrops + isProd, chainExtra := s.chainExtra + extra }
      return wrapUps ups c
    | none => failM s!"drop fails on {repr B'}"

/-- Cut the coordinate `q` of the box at the parts' ends (a balanced tree of cuts) and finish each part with `f`. -/
partial def cutParts (S : Shp) (q : Nat) (B : Box) (ps : List (Int × Int)) (f : Box → M Cert) : M Cert := do
  match ps with
  | [] => failM "no parts"
  | [_] => f B
  | _ =>
    let h := ps.length / 2
    let left := ps.take h
    let right := ps.drop h
    let p := right.head!.1
    match findUW S (ltCon q p).L with
    | none => failM "degenerate cut"
    | some (u, w) =>
      let t1 ← cutParts S q (B.modify q fun b => (b.1, min b.2 p)) left f
      let t2 ← cutParts S q (B.modify q fun b => (max b.1 p, b.2)) right f
      modify fun s => { s with nodes := s.nodes + 1 }
      return .cut q p u w t1 t2

/-- A leaf check that may need the box cut: try it; if it fails, cut the widest coordinate at its midpoint, move the
ends of each half, and try again on each (to `depth` levels). -/
partial def repairLeaf (o : Opt) (E : Int) (S : Shp) (Γ : List Con) (B : Box) (depth : Nat)
    (try_ : Box → Option Cert) : M (Option Cert) := do
  match try_ B with
  | some c => return some c
  | none =>
    if depth == 0 then return none
    let ws := (List.range B.length).map fun j => ((B.getD j (0, 0)).2 - (B.getD j (0, 0)).1, j)
    let (w, q) := ws.foldl (fun acc x => if x.1 > acc.1 then x else acc) (0, 0)
    if w < 2 then return none
    let lo := (B.getD q (0, 0)).1
    let p := lo + w / 2
    match findUW S (ltCon q p).L with
    | none => return none
    | some (u, w') =>
      let half := fun (B1 : Box) => do
        let (ups, B2) := upRounds E Γ B1 o.partRounds
        modify fun s => { s with ups := s.ups + ups.length, nodes := s.nodes + 1 }
        match closeEmpty E Γ B2 with
        | some c => return some (wrapUps ups c)
        | none => return (← repairLeaf o E S Γ B2 (depth - 1) try_).map (wrapUps ups)
      let c1 ← half (B.modify q fun b => (b.1, min b.2 p))
      let c2 ← half (B.modify q fun b => (max b.1 p, b.2))
      match c1, c2 with
      | some c1, some c2 =>
        modify fun s => { s with nodes := s.nodes + 1 }
        return some (.cut q p u w' c1 c2)
      | _, _ => return none

/-- The checker's next node for a decomposition. -/
def child (E : Int) (op : Op) (S : Shp) (Γ : List Con) (B : Box) : Option (Shp × List Con × Box × List LF × Nat) :=
  match op, S with
  | .dec, .std k => some (.std (k + 1), geCon (k + 1) :: (Γ ++ [ordCon k]), B ++ [(NU0, (B.getD k (0, 0)).2)],
      stdItems (k + 1), k + 1)
  | .dec, S => some (.last S, geL (S.items.getD (S.k + 1) LF.zero) B.length ::
      (Γ ++ [ordL (S.items.getD (S.sN 1) LF.zero) B.length]),
      B ++ [(NU0, (S.items.getD (S.sN 1) LF.zero).maxB B E)], S.items, S.k + 1)
  | .rev, .std (k + 1) => some (.rev k, Γ ++ [halfCon k], B ++ [(NU0, (B.getD 0 (0, 0)).2)], stdItems (k + 2), 0)
  | .swapdec, S => some (.last (.swap S), geL ((Shp.swap S).items.getD ((Shp.swap S).k + 1) LF.zero) B.length ::
      (Γ ++ [ordL ((Shp.swap S).items.getD ((Shp.swap S).sN 1) LF.zero) B.length]),
      B ++ [(NU0, ((Shp.swap S).items.getD ((Shp.swap S).sN 1) LF.zero).maxB B E)], (Shp.swap S).items,
      (Shp.swap S).k + 1)
  | _, _ => none

partial def walk (o : Opt) (tr : GTree) (E : Int) (t : Nat) (S : Shp) (Γ : List Con) (B0 : Box) (b : Bool)
    (pend : Option Pend) : M Cert := do
  let N ← next tr
  if N.ty != t then return ← failM s!"type mismatch {N.ty} {t}"
  -- move the ends, as the generator's tightening at every node
  let (ups, B) := upRoundsG o.minGain E Γ B0 o.rounds
  modify fun s => { s with ups := s.ups + ups.length, nodes := s.nodes + 1 }
  let body : M Cert := do
    match N.dec with
    | 0 =>
      match closeEmpty E Γ B with
      | some c => return c
      | none =>
        let (u2, B2) := upRounds E Γ B 3
        match closeEmpty E Γ B2 with
        | some c =>
          modify fun s => { s with ups := s.ups + u2.length }
          return wrapUps u2 c
        | none => if Out E Γ B then return .out else failM s!"out fails at type {t}"
    | 4 =>
      let j := N.sc
      let p := N.sp
      match findUW S (ltCon j p).L with
      | none => failM "degenerate cut"
      | some (u, w) =>
        let t1 ← walk o tr E t S Γ (B.modify j fun b' => (b'.1, min b'.2 p)) b pend
        let t2 ← walk o tr E t S Γ (B.modify j fun b' => (max b'.1 p, b'.2)) b pend
        return .cut j p u w t1 t2
    | 8 =>
      let F := tr.forms[N.w]!
      let C : Con := ⟨⟨F.c0, F.c, 0⟩, true⟩
      match findUW S C.L with
      | none =>
        let _ ← walk o tr E t S (C :: Γ) B b pend
        let _ ← walk o tr E t S (C.neg :: Γ) B b pend
        failM "degenerate split"
      | some (u, w) =>
        let t1 ← walk o tr E t S (C :: Γ) B b pend
        let t2 ← walk o tr E t S (C.neg :: Γ) B b pend
        return .split C u w t1 t2
    | 2 =>
      match canonOf S (gitems t) with
      | none => failM s!"no canonical map at type {t}"
      | some cp =>
        let gi := (gitems t).length
        let grp := fun i => (N.w / 16 ^ i) % 16
        let ng := ((List.range gi).map grp).foldl max 0 + 1
        let labels := (List.range (S.k + S.m)).map fun p =>
          match (List.range gi).find? (fun i => cp.getD i 0 == p) with
          | some i => grp i
          | none => 0
        let chk : Box → List Nat → Bool := fun B' a => (run E (.tii a labels ng) S Γ B' b).isSome
        match ← repairLeaf o E S Γ B 4 (fun B' => match (findActs E Γ B' (chk B')).map fun a => Cert.tii a labels ng with
            | some c => some c
            | none => let (u2, B2) := upRounds E Γ B' 3
              (findActs E Γ B2 (chk B2)).map fun a => wrapUps u2 (Cert.tii a labels ng)) with
        | some c => return c
        | none => failM s!"tii fails at type {t}"
    | 1 =>
      match canonOf S (gitems t) with
      | none => failM s!"no canonical map at type {t}"
      | some cp =>
        let Mm := N.w % 65536
        let Rm := (N.w / 65536) % 65536
        let gi := (gitems t).length
        let labels := (List.range (S.k + S.m)).map fun p =>
          match (List.range gi).find? (fun i => cp.getD i 0 == p) with
          | some i => if (Mm / 2 ^ i) % 2 == 1 then 0 else if (Rm / 2 ^ i) % 2 == 1 then 2 else 1
          | none => 1
        let chk : Box → List Nat → Bool := fun B' a => (run E (.g2 a labels) S Γ B' b).isSome
        match ← repairLeaf o E S Γ B 4 (fun B' => match (findActs E Γ B' (chk B')).map fun a => Cert.g2 a labels with
            | some c => some c
            | none => let (u2, B2) := upRounds E Γ B' 3
              (findActs E Γ B2 (chk B2)).map fun a => wrapUps u2 (Cert.g2 a labels)) with
        | some c => return c
        | none =>
          let acts := actsOf Γ (activesOf E Γ B)
          let LM := grpLF S.items labels 0
          let LN := grpLF S.items labels 1
          let v1 := -(LN.add (LM.smul (-1))).minD B E acts
          let v2 := -(LM.add (LN.smul (-1))).minD B E acts
          let v3 := (LM.add LN).minD B E acts
          failM s!"g2 fails at type {t}: labels {labels} M {Mm} R {Rm} maxes {v1} {v2} (< {g2D1}) min {v3} (> {g2D2}) box {repr B}"
    | 3 =>
      if !b then return ← failM "drop of a - node"
      let q1 := N.sc
      let lo1 := (B.getD q1 (0, 0)).1
      let hi1 := (B.getD q1 (0, 0)).2
      let ps1 := if N.k1 ≤ 1 then [(lo1, hi1)] else parts lo1 hi1 N.k1
      cutParts S q1 B ps1 fun B1 => do
        let q2 := N.q2
        let lo2 := (B1.getD q2 (0, 0)).1
        let hi2 := (B1.getD q2 (0, 0)).2
        let ps2 := if N.k2 ≤ 1 then [(lo2, hi2)] else parts lo2 hi2 N.k2
        cutParts S q2 B1 ps2 fun B2 => dropPart o E S Γ B2
    | 5 | 6 =>
      match trans t N.dec with
      | none => failM s!"no decomposition {t} {N.dec}"
      | some (t', op) =>
        match child E op S Γ B with
        | none => failM "no child"
        | some (S', Γ', B', items, c0) =>
          let rq := reqs t N.dec
          -- the current check's variables, roles and kind; and the child's pending requirement
          let (cur, pend') : Option Pend × Option Pend :=
            match rq with
            | [] => (pend, none)
            | [vs] =>
              let (kind, roles) := decodeTI (N.w % 2 ^ 32) vs.length
              (some ⟨vs, roles, kind⟩, if vs.length > items.length - 1 then some ⟨vs, roles, kind⟩ else none)
            | vs :: ws :: _ =>
              let (kind, roles) := decodeTI (N.w % 2 ^ 32) vs.length
              let (kind', roles') := decodeTI ((N.w / 2 ^ 32) % 2 ^ 32) ws.length
              (some ⟨vs, roles, kind⟩, some ⟨ws, roles', kind'⟩)
          match cur with
          | none =>
            let _ ← walk o tr E t' S' Γ' B' (!b) pend'
            failM s!"no Type I requirement at {t}"
          | some P =>
            match matchLabels items c0 P.vars P.roles with
            | none =>
              let _ ← walk o tr E t' S' Γ' B' (!b) pend'
              failM s!"no labels at {t}"
            | some labels =>
              let mk := fun (a : List Nat) (tc : Cert) => match op with
                | .dec => Cert.dec a labels P.kind tc
                | .rev => Cert.rev a labels P.kind tc
                | .swapdec => Cert.swap (Cert.dec a labels P.kind tc)
              -- the check alone, on the constraints `Γc`
              let chkB := fun (Bx : Box) (Γc : List Con) (a : List Nat) =>
                actsOK Γc a Bx.length && typeICheck items c0 E Bx (actsOf Γc a) labels P.kind
              -- the constraints for the check: `Γ`, or `Γ` with a combination of two active constraints in front
              let findOn := fun (B : Box) => Id.run do
                let chk := chkB B
                let res : Option (Option (Nat × Nat × Nat) × List Nat) :=
                match findActs E Γ B (chk Γ) with
                | some a => some (none, a)
                | none => Id.run do
                  let A := activesOf E Γ B
                  for i in A do
                    for j in A do
                      for c in [1, 2] do
                        if i != j then
                          let Γc := combCon (Γ.getD i ⟨LF.zero, false⟩) (Γ.getD j ⟨LF.zero, false⟩) c :: Γ
                          let ok := fun a => chk Γc a
                          if ok [0] then return some (some (i, j, c), [0])
                          for a in A do
                            if ok [0, a + 1] then return some (some (i, j, c), [0, a + 1])
                            if ok [a + 1, 0] then return some (some (i, j, c), [a + 1, 0])
                  return none
                return res
              -- on the box, or else after moving every end that moves
              let (u2, B2) := upRounds E Γ B 3
              let (found, B, wrapU) : Option (Option (Nat × Nat × Nat) × List Nat) × Box × List Up :=
                match findOn B with
                | some r => (some r, B, [])
                | none => (findOn B2, B2, u2)
              match found with
              | some (cb, a) =>
                let Γc := match cb with
                  | some (i, j, c) => combCon (Γ.getD i ⟨LF.zero, false⟩) (Γ.getD j ⟨LF.zero, false⟩) c :: Γ
                  | none => Γ
                match child E op S Γc B with
                | none => failM "no child"
                | some (S'', Γ'', B'', _, _) =>
                  let tc ← walk o tr E t' S'' Γ'' B'' (!b) pend'
                  modify fun s => { s with ups := s.ups + wrapU.length }
                  match cb with
                  | some (i, j, c) => return wrapUps wrapU (.comb i j c (mk a tc))
                  | none => return wrapUps wrapU (mk a tc)
              | none =>
                let _ ← walk o tr E t' S' Γ' B' (!b) pend'
                let acts := actsOf Γ (activesOf E Γ B)
                let g := fun i => grpLF items labels i
                let mx := fun (L : LF) => L.maxD B E acts
                let A := activesOf E Γ B
                let actStr := ", ".intercalate (A.map fun i => s!"{i}:{conS (Γ.getD i ⟨LF.zero, false⟩)}")
                failM s!"Type I fails at {t} (op {if op == .dec then "dec" else "rev/swap"}): actives {actStr} labels {labels} kind {P.kind} \
                  mx g0 {mx (g 0)} (2x <= {DEN}) tot {mx (((g 0).add (g 1)).add (g 2))} g1 {mx (g 1)} g2 {mx (g 2)} \
                  box {repr B}"
    | d => failM s!"decision {d}"
  let c ← body
  return wrapUpsL o ups B c

/-! ## Output -/

partial def certS : Cert → String
  | .out => ".out"
  | .outC i => s!"(.outC {i})"
  | .outE j => s!"(.outE {j})"
  | .tighten t => s!"(.tighten {certS t})"
  | .up j l i v t => s!"(.up {j} {l} {i} {intS v} {certS t})"
  | .comb i j c t => s!"(.comb {i} {j} {c} {certS t})"
  | .split C u w t1 t2 => s!"(.split {conS C} {u} {w} {certS t1} {certS t2})"
  | .cut j p u w t1 t2 => s!"(.cut {j} {intS p} {u} {w} {certS t1} {certS t2})"
  | .tii a l ng => s!"(.tii {listS a} {listS l} {ng})"
  | .g2 a l => s!"(.g2 {listS a} {listS l})"
  | .dec a l k t => s!"(.dec {listS a} {listS l} {k} {certS t})"
  | .rev a l k t => s!"(.rev {listS a} {listS l} {k} {certS t})"
  | .swap t => s!"(.swap {certS t})"
  | .drop a none => s!"(.drop {listS a} none)"
  | .drop a (some (b₁, b₂)) => s!"(.drop {listS a} (some ({listIS b₁}, {listIS b₂})))"

partial def shpS : Shp → String
  | .std k => s!"(.std {k})"
  | .rev k => s!"(.rev {k})"
  | .last S => s!"(.last {shpS S})"
  | .swap S => s!"(.swap {shpS S})"

def consS (Γ : List Con) : String := "[" ++ ", ".intercalate (Γ.map conS) ++ "]"

def kindS : Cert → String
  | .out => "out" | .outC _ => "outC" | .outE _ => "outE" | .tighten _ => "tighten" | .up .. => "up" | .comb .. => "comb"
  | .split .. => "split" | .cut .. => "cut" | .tii .. => "tii" | .g2 .. => "g2" | .dec .. => "dec" | .rev .. => "rev"
  | .swap _ => "swap" | .drop _ c => if c.isSome then "dropC" else "dropP"

/-- Every node of a certificate with the checker's state there, in preorder, and the indices of its children. -/
partial def enumStates (E : Int) (acc : Array (Shp × List Con × Box × Bool × Cert × List Nat))
    (c : Cert) (S : Shp) (Γ : List Con) (B : Box) (b : Bool) : Array (Shp × List Con × Box × Bool × Cert × List Nat) :=
  let me := acc.size
  let acc := acc.push (S, Γ, B, b, c, [])
  let setCh (a : Array (Shp × List Con × Box × Bool × Cert × List Nat)) (ch : List Nat) :=
    a.modify me fun (S, Γ, B, b, c, _) => (S, Γ, B, b, c, ch)
  match c with
  | .up j l _ v t =>
    let a := enumStates E acc t S Γ (cutAt B j l v) b
    setCh a [me + 1]
  | .tighten t =>
    let a := enumStates E acc t S Γ (tightenList E Γ B) b
    setCh a [me + 1]
  | .comb i j c t => setCh (enumStates E acc t S (combCon (Γ.getD i ⟨LF.zero, false⟩) (Γ.getD j ⟨LF.zero, false⟩) c :: Γ) B b)
      [me + 1]
  | .split C _ _ t1 t2 =>
    let a := enumStates E acc t1 S (C :: Γ) B b
    let k2 := a.size
    let a := enumStates E a t2 S (C.neg :: Γ) B b
    setCh a [me + 1, k2]
  | .cut j p _ _ t1 t2 =>
    let a := enumStates E acc t1 S Γ (B.modify j fun b' => (b'.1, min b'.2 p)) b
    let k2 := a.size
    let a := enumStates E a t2 S Γ (B.modify j fun b' => (max b'.1 p, b'.2)) b
    setCh a [me + 1, k2]
  | .swap t => setCh (enumStates E acc t (.swap S) Γ B b) [me + 1]
  | .dec _ _ _ t =>
    match S with
    | .std k => setCh (enumStates E acc t (.std (k + 1)) (geCon (k + 1) :: (Γ ++ [ordCon k]))
        (B ++ [(NU0, (B.getD k (0, 0)).2)]) (!b)) [me + 1]
    | S => setCh (enumStates E acc t (.last S) (geL (S.items.getD (S.k + 1) LF.zero) B.length ::
          (Γ ++ [ordL (S.items.getD (S.sN 1) LF.zero) B.length]))
        (B ++ [(NU0, (S.items.getD (S.sN 1) LF.zero).maxB B E)]) (!b)) [me + 1]
  | .rev _ _ _ t =>
    match S with
    | .std (k + 1) => setCh (enumStates E acc t (.rev k) (Γ ++ [halfCon k]) (B ++ [(NU0, (B.getD 0 (0, 0)).2)]) (!b))
        [me + 1]
    | _ => acc
  | _ => acc

partial def certSize : Cert → Nat
  | .up _ _ _ _ t | .tighten t | .swap t | .dec _ _ _ t | .rev _ _ _ t | .comb _ _ _ t => 1 + certSize t
  | .split _ _ _ t1 t2 | .cut _ _ _ _ t1 t2 => 1 + certSize t1 + certSize t2
  | _ => 1

end Enc

open Enc in
def profMain (args : List String) : IO Unit := do
  -- prof CERTFILE-is-not-needed: re-encode and write one theorem per node
  let path := args.getD 1 ""
  let k := (args.getD 2 "0").toNat!
  let j := (args.getD 3 "0").toNat!
  let r := args.getD 4 "1" == "1"
  let out := args.getD 5 ""
  let o : Opt := { tol := (args.getD 6 "0").toNat!, rounds := (args.getD 7 "3").toNat!, partRounds := (args.getD 8 "3").toNat!, lit := args.getD 9 "0" == "1" }
  let tr := parseTree (← IO.FS.readFile path)
  let (c, _) := (walk o tr 1 0 (.std 1) (cellCons k r) (cellBox k j) true none).run {}
  let st := enumStates 1 #[] c (.std 1) (cellCons k r) (cellBox k j) true
  let mut txt := "import ShortSieveCertCheck\nopen ShortSieveCert\nset_option maxRecDepth 100000\nset_option Elab.async false\n" ++
    "set_option profiler true\nset_option profiler.threshold 0\n"
  let mut info := ""
  for i in [0:st.size] do
    let (S, Γ, B, b, ci, ch) := st[i]!
    match run 1 ci S Γ B b with
    | some L =>
      txt := txt ++ s!"#eval IO.println \"== node {i}\"\ntheorem n{i} : run 1 {certS ci} {shpS S} {consS Γ} {boxS B} {b} = some {L} := by decide +kernel\n"
      info := info ++ s!"{i} {kindS ci} {B.length} {Γ.length} {ch}\n"
    | none => info := info ++ s!"{i} {kindS ci} FAIL\n"
  IO.FS.writeFile out txt
  IO.FS.writeFile (out ++ ".meta") info
  IO.println s!"{st.size} nodes"

open Enc in
/-- dropbench TREE k j r OUT N: the first N chain drops' states, as product and chain decisions. -/
def dropBench (args : List String) : IO Unit := do
  let path := args.getD 1 ""
  let k := (args.getD 2 "0").toNat!
  let j := (args.getD 3 "0").toNat!
  let r := args.getD 4 "1" == "1"
  let out := args.getD 5 ""
  let nmax := (args.getD 6 "20").toNat!
  let tr := parseTree (← IO.FS.readFile path)
  let (c, _) := (walk {} tr 1 0 (.std 1) (cellCons k r) (cellBox k j) true none).run {}
  let st := enumStates 1 #[] c (.std 1) (cellCons k r) (cellBox k j) true
  let mut txt := "import ShortSieveCertCheck\nopen ShortSieveCert\nset_option maxRecDepth 100000\nset_option Elab.async false\n" ++
    "set_option profiler true\nset_option profiler.threshold 0\n"
  let mut n := 0
  for i in [0:st.size] do
    let (S, Γ, B, _, ci, _) := st[i]!
    match ci with
    | .drop a (some bp) =>
      if n < nmax then
        n := n + 1
        let Lc := (run 1 ci S Γ B true).getD 0
        let Lp := (run 1 (.drop a none) S Γ B true).getD 0
        let Lk := (run 1 (.drop a (some ([], []))) S Γ B true).getD 0
        let st := s!"{shpS S} {consS Γ} {boxS B} true"
        txt := txt ++ s!"#eval IO.println \"== P {i} n={B.length} g={Γ.length}\"\ntheorem p{i} : run 1 (.drop {listS a} none) {st} = some {Lp} := by decide +kernel\n"
        txt := txt ++ s!"#eval IO.println \"== C {i}\"\ntheorem c{i} : run 1 {certS ci} {st} = some {Lc} := by decide +kernel\n"
        txt := txt ++ s!"#eval IO.println \"== K {i}\"\ntheorem k{i} : run 1 (.drop {listS a} (some ([], []))) {st} = some {Lk} := by decide +kernel\n"
    | _ => pure ()
  IO.FS.writeFile out txt

open Enc in
def main (args : List String) : IO Unit := do
  if args.head? == some "prof" then return ← profMain args
  if args.head? == some "dropbench" then return ← dropBench args
  let path := args.getD 0 ""
  let k := (args.getD 1 "0").toNat!
  let j := (args.getD 2 "0").toNat!
  let r := args.getD 3 "1" == "1"
  let out := args.getD 4 ""
  let o : Opt := { tol := (args.getD 5 "0").toNat!, rounds := (args.getD 6 "3").toNat!, partRounds := (args.getD 7 "3").toNat!, lit := args.getD 8 "0" == "1", prune := (args.getD 9 "0").toNat!, minGain := (args.getD 10 "0").toNat! }
  let txt ← IO.FS.readFile path
  let tr := parseTree txt
  let (c, st) := (walk o tr 1 0 (.std 1) (cellCons k r) (cellBox k j) true none).run {}
  IO.println s!"nodes read {st.pos}/{tr.nodes.size}, cert size {certSize c}, ups {st.ups}, drops {st.drops} \
    (product {st.prodDrops}, adding {st.chainExtra}), failures {st.fails.size}"
  for f in st.fails.toList.take 20 do IO.println s!"  {f}"
  match run 1 c (.std 1) (cellCons k r) (cellBox k j) true with
  | some L => IO.println s!"run: some {L} = {(L.toFloat) / (2 ^ 50 : Float)}"
  | none => IO.println "run: none"
  if out ≠ "" then
    IO.FS.writeFile out (certS c)
