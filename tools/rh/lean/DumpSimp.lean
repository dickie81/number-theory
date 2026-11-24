import Lean
open Lean Elab Command Meta

/-!
`#dump_simp "FILE"` writes the simp set of the environment at hand: one line a lemma, `name`, then `1` if it
is used after the subterms are simplified (the default) and `0` if before (`simp↓`), then `1` if it is used from
right to left (`simp ←`). Run it in a file that imports what is to be listed:

    import Mathlib
    import «DumpSimp»      -- or paste the command's definition
    #dump_simp "/path/simp.tsv"

Two such lists, of two versions of Mathlib, say which lemmas one version has in its simp set and the other has
not (`tools/rh/simp_diff.py`).
-/

elab "#dump_simp " path:str : command => do
  let env ← getEnv
  let mut out := ""
  let mut n : Nat := 0
  for o in (simpExtension.getState env).lemmaNames do
    if let .decl name post inv := o then
      out := out ++ s!"{name}\t{if post then 1 else 0}\t{if inv then 1 else 0}\n"
      n := n + 1
  IO.FS.writeFile path.getString out
  logInfo m!"{n} simp lemmas"
