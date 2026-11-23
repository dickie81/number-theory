import Mathlib
open Lean Elab Command

/-!
A fingerprint of every constant of the environment, to compare two environments at the level of the kernel.

`#fingerprint "FILE"` writes one line for each constant: its name, its kind, the number of its universe parameters,
a few numbers of its shape, and for its type and for its value a hash and the constants named, in the order of
their first occurrence. The hash does not see the names of those constants, only their places in that list; nor
binder names, binder annotations, metadata or the names of universe parameters, which the kernel ignores. So two
constants whose lines agree, once the names in the lists are matched, are the same term over matched constants:
`fp_compare.py` does the matching.

The hash is written out here, so that two versions of Lean give the same number for the same term.
-/

namespace FP

@[inline] def mix (h x : UInt64) : UInt64 := (h ^^^ x) * 1099511628211 + 0x9e3779b97f4a7c15

def strHash (s : String) : UInt64 :=
  s.foldl (fun h c => mix h c.toNat.toUInt64) 14695981039346656037

structure St where
  refs : Array Name := #[]
  idx : Std.HashMap Name Nat := {}
  exprs : Std.HashMap Expr UInt64 := {}

abbrev M := StateM St

def refIdx (n : Name) : M UInt64 := do
  let s ← get
  match s.idx[n]? with
  | some i => return i.toUInt64
  | none =>
    let i := s.refs.size
    set { s with refs := s.refs.push n, idx := s.idx.insert n i }
    return i.toUInt64

partial def levelH (ps : List Name) : Level → UInt64
  | .zero => 5
  | .succ l => mix 7 (levelH ps l)
  | .max a b => mix (mix 11 (levelH ps a)) (levelH ps b)
  | .imax a b => mix (mix 13 (levelH ps a)) (levelH ps b)
  | .param n => mix 17 (ps.idxOf n).toUInt64
  | .mvar _ => 19

partial def exprH (ps : List Name) (e : Expr) : M UInt64 := do
  match e with
  | .bvar i => return mix 23 i.toUInt64
  | .sort l => return mix 29 (levelH ps l)
  | .lit (.natVal n) => return mix 31 (strHash (toString n))
  | .lit (.strVal s) => return mix 37 (strHash s)
  | .mdata _ b => exprH ps b
  | _ =>
    if let some h := (← get).exprs[e]? then return h
    let h ← match e with
      | .const n ls => do
          let mut h := mix 41 (← refIdx n)
          for l in ls do h := mix h (levelH ps l)
          pure h
      | .app f a => do pure (mix (mix 43 (← exprH ps f)) (← exprH ps a))
      | .lam _ t b _ => do pure (mix (mix 47 (← exprH ps t)) (← exprH ps b))
      | .forallE _ t b _ => do pure (mix (mix 53 (← exprH ps t)) (← exprH ps b))
      | .letE _ t v b _ => do pure (mix (mix (mix 59 (← exprH ps t)) (← exprH ps v)) (← exprH ps b))
      | .proj s i b => do pure (mix (mix (mix 61 (← refIdx s)) i.toUInt64) (← exprH ps b))
      | _ => pure 67
    modify fun s => { s with exprs := s.exprs.insert e h }
    return h

def names (xs : Array Name) : String := "\x1f".intercalate (xs.toList.map toString)

/-- The line of one constant. -/
def line (n : Name) (ci : ConstantInfo) : String := Id.run do
  let ps := ci.levelParams
  let (tyH, tySt) := (exprH ps ci.type).run {}
  let mut kind := "?"
  let mut extra := ""
  let mut valH : UInt64 := 0
  let mut valRefs : Array Name := #[]
  match ci with
  | .defnInfo v =>
    kind := "d"
    let (x, s) := (exprH ps v.value).run {}
    valH := x
    valRefs := s.refs
  | .thmInfo _ => kind := "t"
  | .axiomInfo _ => kind := "a"
  | .opaqueInfo _ => kind := "o"
  | .quotInfo _ => kind := "q"
  | .inductInfo v =>
    kind := "i"
    extra := s!"{v.numParams}.{v.numIndices}.{v.ctors.length}.{v.all.length}"
    valRefs := v.ctors.toArray ++ v.all.toArray
  | .ctorInfo v =>
    kind := "c"
    extra := s!"{v.cidx}.{v.numParams}.{v.numFields}"
    valRefs := #[v.induct]
  | .recInfo v =>
    kind := "r"
    extra := s!"{v.numParams}.{v.numIndices}.{v.numMotives}.{v.numMinors}.{v.rules.length}"
    let mut st : St := {}
    let mut x : UInt64 := 0
    for r in v.rules do
      let (i, s1) := (refIdx r.ctor).run st
      let (y, s2) := (exprH ps r.rhs).run s1
      st := s2
      x := mix (mix (mix x i) r.nfields.toUInt64) y
    let (_, s3) := (v.all.forM fun a => do let _ ← refIdx a).run st
    valH := x
    valRefs := s3.refs
  return s!"{n}\t{kind}\t{ps.length}\t{extra}\t{tyH}\t{names tySt.refs}\t{valH}\t{names valRefs}"

end FP

elab "#fingerprint " path:str : command => do
  let env ← getEnv
  let h ← IO.FS.Handle.mk path.getString .write
  for (n, ci) in env.constants.map₁.toList do
    h.putStrLn (FP.line n ci)
  for (n, ci) in env.constants.map₂.toList do
    h.putStrLn (FP.line n ci)
  h.flush
