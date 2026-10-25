/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 761–771 of 5796

File 82 of 465: the parts `rows22250R_761` … `rows22250R_771` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 97993 tests: row 56 columns 45–45, row 56 columns 46–46, row 56 columns
47–47, row 56 columns 48–48, row 56 columns 49–49, row 56 columns 50–50, row 56 columns 51–51, row 56 columns 52–52,
row 56 columns 53–53, row 56 columns 54–54, row 56 columns 55–55), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_761 : rowsJ2 56 57 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_762 : rowsJ2 56 57 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_763 : rowsJ2 56 57 47 48 ≤ 116727878191 := by decide +kernel

theorem rows22250R_764 : rowsJ2 56 57 48 49 ≤ 523155550945 := by decide +kernel

theorem rows22250R_765 : rowsJ2 56 57 49 50 ≤ 974183979157 := by decide +kernel

theorem rows22250R_766 : rowsJ2 56 57 50 51 ≤ 1465201502530 := by decide +kernel

theorem rows22250R_767 : rowsJ2 56 57 51 52 ≤ 2109152738880 := by decide +kernel

theorem rows22250R_768 : rowsJ2 56 57 52 53 ≤ 3022855737577 := by decide +kernel

theorem rows22250R_769 : rowsJ2 56 57 53 54 ≤ 3960178949101 := by decide +kernel

theorem rows22250R_770 : rowsJ2 56 57 54 55 ≤ 4918579626261 := by decide +kernel

theorem rows22250R_771 : rowsJ2 56 57 55 56 ≤ 6073565719840 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_761
#print axioms SieveCert.rows22250R_771
