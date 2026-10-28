/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 196–203 of 4715

File 14 of 351: the parts `rows22250R_196` … `rows22250R_203` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, work 97678 in units of a depth-4 test: row 35 columns 31–31, row 35 columns
32–32, row 35 columns 33–33, row 35 columns 34–34, row 35 columns 35–339, row 36 columns 0–13, row 36 columns 14–16,
row 36 columns 17–18), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

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

theorem rows22250R_196 : rowsJ2 35 36 31 32 ≤ 684248227597 := by decide +kernel

theorem rows22250R_197 : rowsJ2 35 36 32 33 ≤ 743526997324 := by decide +kernel

theorem rows22250R_198 : rowsJ2 35 36 33 34 ≤ 798817635716 := by decide +kernel

theorem rows22250R_199 : rowsJ2 35 36 34 35 ≤ 820626324638 := by decide +kernel

theorem rows22250R_200 : rowsJ2 35 36 35 340 ≤ 811016457288 := by decide +kernel

theorem rows22250R_201 : rowsJ2 36 37 0 14 ≤ 865974862700 := by decide +kernel

theorem rows22250R_202 : rowsJ2 36 37 14 17 ≤ 2297728772333 := by decide +kernel

theorem rows22250R_203 : rowsJ2 36 37 17 19 ≤ 2136970394484 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_196
#print axioms SieveCert.rows22250R_203
