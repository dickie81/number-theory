import ShortSieveCertCheck

/-!
# Certificates as data: `cert_data% "…"`

A certificate written in a compact prefix form inside one string literal; the term elaborator builds the `Cert`
directly (constructors applied to raw literals), so a large certificate costs the elaborator one string and the kernel
the usual check of the definition. The form, tokens separated by spaces:

* `o` `.out`; `C i` `.outC i`; `E j` `.outE j`; `T t` `.tighten t`;
* `u j l i v t` `.up j (l = 1) i v t`; `m i j c t` `.comb i j c t`;
* `s C u w t₁ t₂` `.split C u w t₁ t₂`, with `C` as `c₀ n c₁ … cₙ cₑ s` (`s = 1` strict);
* `c j p u w t₁ t₂` `.cut j p u w t₁ t₂`;
* `t A L ng` `.tii A L ng`; `g A L` `.g2 A L`; `d A L k t` `.dec A L k t`; `r A L k t` `.rev A L k t`; `w t` `.swap t`;
* `x A N` `.drop A none`, `x A S B₁ B₂` `.drop A (some (B₁, B₂))`;
* lists as their length followed by their entries; `@n` the constant named `n` (a sub-certificate).
-/

open Lean Elab Term Meta

open Lean (mkConst mkApp mkApp2 mkApp3 mkApp4 mkApp5 mkApp6 mkRawNatLit)

namespace ShortSieveCert.Data

/-- An integer as `Int.ofNat n` or `Int.negSucc n` on a raw literal. -/
def intE (v : Int) : Expr :=
  match v with
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (mkRawNatLit n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (mkRawNatLit n)

def listE (ty : Expr) (l : List Expr) : Expr :=
  l.foldr (fun a acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty a acc) (mkApp (mkConst ``List.nil [Level.zero]) ty)

abbrev P := StateT Nat (Except String)

def tok (ts : Array String) : P String := do
  let i ← get
  if h : i < ts.size then
    set (i + 1)
    return ts[i]
  else throw "certificate data ends early"

def natP (ts : Array String) : P Nat := do
  let s ← tok ts
  match s.toNat? with
  | some n => return n
  | none => throw s!"not a natural number: {s}"

def intP (ts : Array String) : P Int := do
  let s ← tok ts
  match s.toInt? with
  | some n => return n
  | none => throw s!"not an integer: {s}"

def natLP (ts : Array String) : P Expr := do
  let n ← natP ts
  let mut l := #[]
  for _ in [0:n] do l := l.push (mkRawNatLit (← natP ts))
  return listE (mkConst ``Nat) l.toList

def intLP (ts : Array String) : P Expr := do
  let n ← natP ts
  let mut l := #[]
  for _ in [0:n] do l := l.push (intE (← intP ts))
  return listE (mkConst ``Int) l.toList

def boolP (ts : Array String) : P Expr := do
  match ← natP ts with
  | 0 => return mkConst ``Bool.false
  | _ => return mkConst ``Bool.true

def conP (ts : Array String) : P Expr := do
  let c0 ← intP ts
  let c ← intLP ts
  let ce ← intP ts
  let s ← boolP ts
  return mkApp2 (mkConst ``Con.mk) (mkApp3 (mkConst ``LF.mk) (intE c0) c (intE ce)) s

partial def certP (ts : Array String) : P Expr := do
  let c (n : Name) := Lean.mkConst (`ShortSieveCert.Cert ++ n)
  let s ← tok ts
  match s with
  | "o" => return c `out
  | "C" => return mkApp (c `outC) (mkRawNatLit (← natP ts))
  | "E" => return mkApp (c `outE) (mkRawNatLit (← natP ts))
  | "T" => return mkApp (c `tighten) (← certP ts)
  | "u" =>
    let j ← natP ts; let l ← boolP ts; let i ← natP ts; let v ← intP ts
    return mkApp5 (c `up) (mkRawNatLit j) l (mkRawNatLit i) (intE v) (← certP ts)
  | "m" =>
    let i ← natP ts; let j ← natP ts; let k ← natP ts
    return mkApp4 (c `comb) (mkRawNatLit i) (mkRawNatLit j) (mkRawNatLit k) (← certP ts)
  | "s" =>
    let C ← conP ts; let u ← natP ts; let w ← natP ts
    let t₁ ← certP ts
    return mkApp5 (c `split) C (mkRawNatLit u) (mkRawNatLit w) t₁ (← certP ts)
  | "c" =>
    let j ← natP ts; let p ← intP ts; let u ← natP ts; let w ← natP ts
    let t₁ ← certP ts
    return mkApp6 (c `cut) (mkRawNatLit j) (intE p) (mkRawNatLit u) (mkRawNatLit w) t₁ (← certP ts)
  | "t" =>
    let a ← natLP ts; let l ← natLP ts
    return mkApp3 (c `tii) a l (mkRawNatLit (← natP ts))
  | "g" =>
    let a ← natLP ts
    return mkApp2 (c `g2) a (← natLP ts)
  | "d" =>
    let a ← natLP ts; let l ← natLP ts; let k ← natP ts
    return mkApp4 (c `dec) a l (mkRawNatLit k) (← certP ts)
  | "r" =>
    let a ← natLP ts; let l ← natLP ts; let k ← natP ts
    return mkApp4 (c `rev) a l (mkRawNatLit k) (← certP ts)
  | "w" => return mkApp (c `swap) (← certP ts)
  | "x" =>
    let a ← natLP ts
    let li := mkApp (mkConst ``List [Level.zero]) (mkConst ``Int)
    let ty := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) li li
    match ← tok ts with
    | "N" => return mkApp2 (c `drop) a (mkApp (mkConst ``Option.none [Level.zero]) ty)
    | "S" =>
      let b₁ ← intLP ts
      let b₂ ← intLP ts
      return mkApp2 (c `drop) a (mkApp2 (mkConst ``Option.some [Level.zero]) ty
        (mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) li li b₁ b₂))
    | s => throw s!"drop: expected N or S, got {s}"
  | s =>
    if s.startsWith "@" then return Lean.mkConst (s.drop 1).toName
    else throw s!"unknown certificate tag {s}"

/-- `cert_data% "…"`: the certificate written in the compact form. -/
syntax (name := certData) "cert_data% " str : term

@[term_elab certData] def elabCertData : TermElab := fun stx _ => do
  match stx with
  | `(cert_data% $s:str) =>
    let ts := (((s.getString.replace "\n" " ").splitOn " ").filter (· ≠ "")).toArray
    match (certP ts).run 0 with
    | .ok (e, n) =>
      if n ≠ ts.size then throwError "certificate data: {ts.size - n} tokens left over"
      return e
    | .error msg => throwError "certificate data: {msg}"
  | _ => throwUnsupportedSyntax

end ShortSieveCert.Data
namespace ShortSieveCert

variable {E : ℤ} {S : Shp} {Γ : List Con} {B : Box} {b : Bool} {L : ℕ}

theorem run_up_of {j : ℕ} {lower : Bool} {i : ℕ} {v : ℤ} {t : Cert}
    (h : i < Γ.length ∧ upOK (Γ.getD i ⟨LF.zero, false⟩) E B j lower v = true)
    (ht : run E t S Γ (cutAt B j lower v) b = some L) : run E (.up j lower i v t) S Γ B b = some L := by
  rw [run, if_pos h, ht]

theorem run_comb_of {i j c : ℕ} {t : Cert} (h : i < Γ.length ∧ j < Γ.length)
    (ht : run E t S (combCon (Γ.getD i ⟨LF.zero, false⟩) (Γ.getD j ⟨LF.zero, false⟩) c :: Γ) B b = some L) :
    run E (.comb i j c t) S Γ B b = some L := by
  rw [run, if_pos h, ht]

theorem run_split_of {C : Con} {u w : ℕ} {t₁ t₂ : Cert} {L₁ L₂ : ℕ}
    (h : fits [C] S.n = true ∧ u < S.k + S.m ∧ w < S.k + S.m ∧ wtN S C.L u ≠ wtN S C.L w)
    (h₁ : run E t₁ S (C :: Γ) B b = some L₁) (h₂ : run E t₂ S (C.neg :: Γ) B b = some L₂) (hL : L₁ + L₂ = L) :
    run E (.split C u w t₁ t₂) S Γ B b = some L := by
  rw [run, if_pos h, h₁, h₂, ← hL]
  rfl

theorem run_cut_of {j : ℕ} {p : ℤ} {u w : ℕ} {t₁ t₂ : Cert} {L₁ L₂ : ℕ}
    (h : u < S.k + S.m ∧ w < S.k + S.m ∧ wtN S (ltCon j p).L u ≠ wtN S (ltCon j p).L w)
    (h₁ : run E t₁ S Γ (B.modify j fun b' => (b'.1, min b'.2 p)) b = some L₁)
    (h₂ : run E t₂ S Γ (B.modify j fun b' => (max b'.1 p, b'.2)) b = some L₂) (hL : L₁ + L₂ = L) :
    run E (.cut j p u w t₁ t₂) S Γ B b = some L := by
  rw [run, if_pos h, h₁, h₂, ← hL]
  rfl

theorem run_dec_std_of {k : ℕ} {acts labels : List ℕ} {kind : ℕ} {t : Cert}
    (h : actsOK Γ acts B.length = true ∧
      typeICheck (stdItems (k + 1)) (k + 1) E B (actsOf Γ acts) labels kind = true)
    (ht : run E t (.std (k + 1)) (geCon (k + 1) :: (Γ ++ [ordCon k])) (B ++ [(NU0, (B.getD k (0, 0)).2)]) (!b) =
      some L) :
    run E (.dec acts labels kind t) (.std k) Γ B b = some L := by
  rw [run, if_pos h, ht]

theorem run_rev_std_of {k : ℕ} {acts labels : List ℕ} {kind : ℕ} {t : Cert}
    (h : actsOK Γ acts B.length = true ∧ typeICheck (stdItems (k + 2)) 0 E B (actsOf Γ acts) labels kind = true)
    (ht : run E t (.rev k) (Γ ++ [halfCon k]) (B ++ [(NU0, (B.getD 0 (0, 0)).2)]) (!b) = some L) :
    run E (.rev acts labels kind t) (.std (k + 1)) Γ B b = some L := by
  rw [run, if_pos h, ht]

end ShortSieveCert
