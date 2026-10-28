/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 385–395 of 4715

File 37 of 351: the parts `rows22250R_385` … `rows22250R_395` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, work 88391 in units of a depth-4 test: row 44 columns 43–43, row 44 columns
44–339, row 45 columns 0–13, row 45 columns 14–17, row 45 columns 18–21, row 45 columns 22–23, row 45 columns 24–25,
row 45 columns 26–26, row 45 columns 27–27, row 45 columns 28–28, row 45 columns 29–29), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_385 : rowsJ2 44 45 43 44 ≤ 14603768433 := by decide +kernel

theorem rows22250R_386 : rowsJ2 44 45 44 340 ≤ 92787151252 := by decide +kernel

theorem rows22250R_387 : rowsJ2 45 46 0 14 ≤ 1826783353886 := by decide +kernel

theorem rows22250R_388 : rowsJ2 45 46 14 18 ≤ 2858904868755 := by decide +kernel

theorem rows22250R_389 : rowsJ2 45 46 18 22 ≤ 2472931948473 := by decide +kernel

theorem rows22250R_390 : rowsJ2 45 46 22 24 ≤ 904591208372 := by decide +kernel

theorem rows22250R_391 : rowsJ2 45 46 24 26 ≤ 708584066821 := by decide +kernel

theorem rows22250R_392 : rowsJ2 45 46 26 27 ≤ 294248184208 := by decide +kernel

theorem rows22250R_393 : rowsJ2 45 46 27 28 ≤ 260216676315 := by decide +kernel

theorem rows22250R_394 : rowsJ2 45 46 28 29 ≤ 243525574005 := by decide +kernel

theorem rows22250R_395 : rowsJ2 45 46 29 30 ≤ 240815913671 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_385
#print axioms SieveCert.rows22250R_395
