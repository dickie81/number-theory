/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 214–224 of 5066

File 15 of 387: the parts `rows22240R_214` … `rows22240R_224` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 94590 in units of a depth-4 test: row 35 columns 34–34, row 35 columns
35–339, row 36 columns 0–13, row 36 columns 14–16, row 36 columns 17–18, row 36 columns 19–20, row 36 columns 21–22,
row 36 columns 23–24, row 36 columns 25–25, row 36 columns 26–26, row 36 columns 27–27), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R
-- exclusive-heavy: a part of this file can use over 7 GiB; scripts/lean-slots.sh runs it alone among the parts

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_214 : rowsJ2 35 36 34 35 ≤ 979149689931 := by decide +kernel

theorem rows22240R_215 : rowsJ2 35 36 35 340 ≤ 1014766422242 := by decide +kernel

theorem rows22240R_216 : rowsJ2 36 37 0 14 ≤ 707022158154 := by decide +kernel

theorem rows22240R_217 : rowsJ2 36 37 14 17 ≤ 1702092590688 := by decide +kernel

theorem rows22240R_218 : rowsJ2 36 37 17 19 ≤ 2003688891657 := by decide +kernel

theorem rows22240R_219 : rowsJ2 36 37 19 21 ≤ 2410029463031 := by decide +kernel

theorem rows22240R_220 : rowsJ2 36 37 21 23 ≤ 2559081141848 := by decide +kernel

theorem rows22240R_221 : rowsJ2 36 37 23 25 ≤ 2481682828474 := by decide +kernel

theorem rows22240R_222 : rowsJ2 36 37 25 26 ≤ 1155740822286 := by decide +kernel

theorem rows22240R_223 : rowsJ2 36 37 26 27 ≤ 1087783634473 := by decide +kernel

theorem rows22240R_224 : rowsJ2 36 37 27 28 ≤ 1009835977724 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_214
#print axioms SieveCert.rows22240R_224
