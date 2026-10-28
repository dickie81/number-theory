/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 216–224 of 4715

File 16 of 351: the parts `rows22250R_216` … `rows22250R_224` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, work 96653 in units of a depth-4 test: row 36 columns 34–34, row 36 columns
35–35, row 36 columns 36–339, row 37 columns 0–13, row 37 columns 14–16, row 37 columns 17–19, row 37 columns 20–21,
row 37 columns 22–23, row 37 columns 24–25), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R
-- exclusive-heavy: a part of this file can use over 7 GiB; scripts/lean-slots.sh runs it alone among the parts

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_216 : rowsJ2 36 37 34 35 ≤ 768480871375 := by decide +kernel

theorem rows22250R_217 : rowsJ2 36 37 35 36 ≤ 749421937469 := by decide +kernel

theorem rows22250R_218 : rowsJ2 36 37 36 340 ≤ 712884021053 := by decide +kernel

theorem rows22250R_219 : rowsJ2 37 38 0 14 ≤ 944390786850 := by decide +kernel

theorem rows22250R_220 : rowsJ2 37 38 14 17 ≤ 2354137508624 := by decide +kernel

theorem rows22250R_221 : rowsJ2 37 38 17 20 ≤ 3190242169073 := by decide +kernel

theorem rows22250R_222 : rowsJ2 37 38 20 22 ≤ 2147276291231 := by decide +kernel

theorem rows22250R_223 : rowsJ2 37 38 22 24 ≤ 1933573504092 := by decide +kernel

theorem rows22250R_224 : rowsJ2 37 38 24 26 ≤ 1647297177411 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_216
#print axioms SieveCert.rows22250R_224
