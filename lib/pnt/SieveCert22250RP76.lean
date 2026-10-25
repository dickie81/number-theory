/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 803–814 of 4715

File 76 of 351: the parts `rows22250R_803` … `rows22250R_814` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 97090 tests: row 58 columns 27–27, row 58 columns 28–28, row 58 columns
29–29, row 58 columns 30–30, row 58 columns 31–31, row 58 columns 32–32, row 58 columns 33–33, row 58 columns 34–34,
row 58 columns 35–35, row 58 columns 36–36, row 58 columns 37–37, row 58 columns 38–38), each a sum of refined costs
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

theorem rows22250R_803 : rowsJ2 58 59 27 28 ≤ 4530545309 := by decide +kernel

theorem rows22250R_804 : rowsJ2 58 59 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_805 : rowsJ2 58 59 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_806 : rowsJ2 58 59 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_807 : rowsJ2 58 59 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_808 : rowsJ2 58 59 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_809 : rowsJ2 58 59 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_810 : rowsJ2 58 59 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_811 : rowsJ2 58 59 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_812 : rowsJ2 58 59 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_813 : rowsJ2 58 59 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_814 : rowsJ2 58 59 38 39 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_803
#print axioms SieveCert.rows22250R_814
