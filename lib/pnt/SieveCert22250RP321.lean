/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3776–3789 of 5796

File 321 of 465: the parts `rows22250R_3776` … `rows22250R_3789` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 97947 tests: row 122 columns 39–41, row 122 columns 42–45, row 122 columns
46–54, row 122 columns 55–63, row 122 columns 64–66, row 122 columns 67–68, row 122 columns 69–70, row 122 columns
71–72, row 122 columns 73–75, row 122 columns 76–78, row 122 columns 79–81, row 122 columns 82–84, row 122 columns
85–87, row 122 columns 88–90), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3776 : rowsJ2 122 123 39 42 ≤ 12387720068349 := by decide +kernel

theorem rows22250R_3777 : rowsJ2 122 123 42 46 ≤ 5905232842505 := by decide +kernel

theorem rows22250R_3778 : rowsJ2 122 123 46 55 ≤ 454608458065 := by decide +kernel

theorem rows22250R_3779 : rowsJ2 122 123 55 64 ≤ 1985201003127 := by decide +kernel

theorem rows22250R_3780 : rowsJ2 122 123 64 67 ≤ 3457134237163 := by decide +kernel

theorem rows22250R_3781 : rowsJ2 122 123 67 69 ≤ 2743987770491 := by decide +kernel

theorem rows22250R_3782 : rowsJ2 122 123 69 71 ≤ 2615055406730 := by decide +kernel

theorem rows22250R_3783 : rowsJ2 122 123 71 73 ≤ 2057051105138 := by decide +kernel

theorem rows22250R_3784 : rowsJ2 122 123 73 76 ≤ 1051365393020 := by decide +kernel

theorem rows22250R_3785 : rowsJ2 122 123 76 79 ≤ 0 := by decide +kernel

theorem rows22250R_3786 : rowsJ2 122 123 79 82 ≤ 0 := by decide +kernel

theorem rows22250R_3787 : rowsJ2 122 123 82 85 ≤ 0 := by decide +kernel

theorem rows22250R_3788 : rowsJ2 122 123 85 88 ≤ 240343228841 := by decide +kernel

theorem rows22250R_3789 : rowsJ2 122 123 88 91 ≤ 2729279301716 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3776
#print axioms SieveCert.rows22250R_3789
