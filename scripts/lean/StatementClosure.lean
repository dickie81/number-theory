import Lean

/-!
# What a theorem's statement depends on, and what only its proof adds

`lean --run scripts/lean/StatementClosure.lean MODULE THEOREM` (under `lake env`; by default `LinnikCGLDensity` and
`LinnikCGLDensity.cglDensity`) imports `MODULE` and walks from `THEOREM` twice.

1. The statement's closure: from the theorem's type, through the type of every constant reached and the value of
   every definition and opaque, but never the proof of a theorem. Only these constants can change what the theorem
   says. It prints how many there are, and each that is not from Mathlib, Lean, Std, Batteries or Aesop.
2. The full closure: types and every value, proofs included, as `lib/check/CheckAll.lean`'s walk. It prints the
   constants of PrimeNumberTheoremAnd that a constant from outside it names, with the constants that name them.

It then lists the constants of the full closure that more than one imported module declares. Lean generates
equation and congruence lemmas (`.eq_n`, `.congr_simp`, `.hcongr_n`) where they are first needed, so several modules
can declare one; import accepts the copies of a theorem with the same name, type and universe parameters, and
attributes the constant to the first module in import order. So the number of modules the closure spans depends on
the import order, and the constants do not: it prints the modules counted only through such a copy.

Last, it counts the recursors of the proof's inductive types. An export (`scripts/kernel_check.sh`) carries every
recursor of each inductive type, not only those a proof uses, so a checker that counts recursors counts more than the
closure.
-/

open Lean

/-- Roots of the modules that are not this repository's or PrimeNumberTheoremAnd's. -/
def foreign : List String :=
  ["Mathlib", "Init", "Lean", "Std", "Batteries", "Aesop", "Qq", "Plausible", "ImportGraph", "ProofWidgets",
    "LeanSearchClient"]

def kind : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
  | .opaqueInfo _ => "opaque" | .recInfo _ => "recursor" | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"

/-- Beyond its type, what a constant contributes to the statement: a definition's or opaque's value, an inductive's
constructors. Never a theorem's proof. -/
def statementPart : ConstantInfo → Array Name
  | .defnInfo v => v.value.getUsedConstants
  | .opaqueInfo v => v.value.getUsedConstants
  | .inductInfo v => v.ctors.toArray
  | _ => #[]

/-- Beyond its type, everything a constant mentions: its value, proofs included, and an inductive's constructors. -/
def everything (ci : ConstantInfo) : Array Name :=
  let v := match ci.value? (allowOpaque := true) with
    | some e => e.getUsedConstants
    | none => #[]
  match ci with
  | .inductInfo i => v ++ i.ctors.toArray
  | _ => v

/-- The constants reachable from `start`; `values ci` gives the constants of `ci` to follow beyond its type. -/
def walk (env : Environment) (start : Array Name) (values : ConstantInfo → Array Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut stack := start
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    stack := stack ++ ci.type.getUsedConstants ++ values ci
  return seen

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let modName := (args[0]?.getD "LinnikCGLDensity").toName
  let root := (args[1]?.getD "LinnikCGLDensity.cglDensity").toName
  let env ← importModules #[{ module := modName }] {}
  let out ← IO.getStdout
  let some rci := env.find? root | throw <| IO.userError s!"{root} is not in {modName}"
  let names := env.header.moduleNames
  -- 0: Mathlib, Lean and the like; 1: PrimeNumberTheoremAnd; 2: this repository.
  let cls : Array Nat := names.map fun m =>
    let r := m.getRoot.toString
    if foreign.contains r then 0 else if r == "PrimeNumberTheoremAnd" then 1 else 2
  let clsOf (c : Name) : Nat := match env.getModuleIdxFor? c with | some i => cls[i.toNat]! | none => 3
  let modOf (c : Name) : Name := match env.getModuleIdxFor? c with | some i => names[i.toNat]! | none => .anonymous
  -- 1. The statement's closure.
  let stmt : Std.HashSet Name := walk env rci.type.getUsedConstants statementPart
  let own := stmt.toArray.filter (clsOf · != 0) |>.qsort (·.toString < ·.toString)
  out.putStrLn s!"The statement of {root}: {stmt.size} constants, {stmt.size - own.size} of them from Mathlib, Lean, \
    Std, Batteries or Aesop. The others:"
  for c in own do
    out.putStrLn s!"  {modOf c}  {c}  ({(env.find? c).map kind |>.getD "?"})"
  -- 2. The full closure, and PrimeNumberTheoremAnd's constants named from outside it.
  let full : Std.HashSet Name := walk env #[root] everything
  let mut named : Std.HashMap Name (Array Name) := {}
  for c in full do
    if clsOf c == 1 then continue
    let some ci := env.find? c | continue
    for u in ci.type.getUsedConstants ++ everything ci do
      if clsOf u == 1 then named := named.insert u ((named.getD u #[]).push c)
  let pnt := full.toArray.filter (clsOf · == 1)
  out.putStrLn s!"\nThe proof: {full.size} constants, {pnt.size} of them from PrimeNumberTheoremAnd, of which \
    {named.size} are named from outside it:"
  for (u, by_) in named.toArray.qsort (·.1.toString < ·.1.toString) do
    out.putStrLn s!"  {modOf u}  {u}  <-  {by_.toList.eraseDups}"
  -- 3. Constants of the full closure declared by more than one module.
  let mut decl : Std.HashMap Name (Array Nat) := {}
  for i in [0:env.header.moduleData.size] do
    for n in env.header.moduleData[i]!.constNames do
      if full.contains n then decl := decl.insert n ((decl.getD n #[]).push i)
  let dups := decl.toArray.filter (·.2.size > 1)
  let mut alone : Std.HashSet Name := {}
  let mut viaDup : Array (Name × Name × List Name) := #[]
  for c in full do
    if (decl.getD c #[]).size ≤ 1 then alone := alone.insert (modOf c)
  for (c, is) in dups do
    unless alone.contains (modOf c) do
      viaDup := viaDup.push (modOf c, c, (is.toList.map (names[·]!)).filter (· != modOf c))
  let mods : Std.HashSet Name := full.fold (fun s c => s.insert (modOf c)) {}
  out.putStrLn s!"\nModules: {mods.size}. {dups.size} constants are declared by more than one module \
    ({dups.filter (fun d => (env.find? d.1).any (·.isTheorem)) |>.size} of them theorems); \
    {viaDup.size} modules are counted only through such a constant:"
  for (m, c, others) in viaDup.qsort (·.1.toString < ·.1.toString) do
    out.putStrLn s!"  {m}, through {c}; also declared by {others.filter alone.contains}, counted anyway, and by \
      {others.filter (!alone.contains ·)}, not"
  -- 4. What the external checkers of `scripts/kernel_check.sh` count: an export carries every recursor of each
  -- inductive type, including the auxiliary ones of nested inductives, not only those a proof uses.
  let mut inds := 0
  let mut recsIn := 0
  let mut aux : Array Name := #[]
  for c in full do
    if let some (.inductInfo _) := env.find? c then
      inds := inds + 1
      if full.contains (mkRecName c) then recsIn := recsIn + 1
      let mut i := 1
      while env.contains (c.str s!"rec_{i}") do
        aux := aux.push (c.str s!"rec_{i}")
        i := i + 1
  out.putStrLn s!"\nThe proof's {inds} inductive types have {inds} recursors, {recsIn} of them in the closure, and \
    the auxiliary recursors {aux}: with all of them, {full.size - recsIn + inds + aux.size} constants."
  out.flush
