/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2882–2898 of 5066

File 242 of 387: the parts `rows22240R_2882` … `rows22240R_2898` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 98387 in units of a depth-4 test: row 102 columns 90–90, row 102
columns 91–91, row 102 columns 92–92, row 102 columns 93–93, row 102 columns 94–94, row 102 columns 95–95, row 102
columns 96–96, row 102 columns 97–97, row 102 columns 98–98, row 102 columns 99–99, row 102 columns 100–100, row 102
columns 101–101, row 102 columns 102–339, row 103 columns 0–17, row 103 columns 18–29, row 103 columns 30–33, row
103 columns 34–35), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at
a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2882 : rowsJ2 102 103 90 91 ≤ 2627028946101 := by decide +kernel

theorem rows22240R_2883 : rowsJ2 102 103 91 92 ≤ 3086816521694 := by decide +kernel

theorem rows22240R_2884 : rowsJ2 102 103 92 93 ≤ 3608457345940 := by decide +kernel

theorem rows22240R_2885 : rowsJ2 102 103 93 94 ≤ 4223477427330 := by decide +kernel

theorem rows22240R_2886 : rowsJ2 102 103 94 95 ≤ 4903963697850 := by decide +kernel

theorem rows22240R_2887 : rowsJ2 102 103 95 96 ≤ 5682515624312 := by decide +kernel

theorem rows22240R_2888 : rowsJ2 102 103 96 97 ≤ 6530682854248 := by decide +kernel

theorem rows22240R_2889 : rowsJ2 102 103 97 98 ≤ 7482217611922 := by decide +kernel

theorem rows22240R_2890 : rowsJ2 102 103 98 99 ≤ 8508117080842 := by decide +kernel

theorem rows22240R_2891 : rowsJ2 102 103 99 100 ≤ 9643374235376 := by decide +kernel

theorem rows22240R_2892 : rowsJ2 102 103 100 101 ≤ 10858420726652 := by decide +kernel

theorem rows22240R_2893 : rowsJ2 102 103 101 102 ≤ 12189589216442 := by decide +kernel

theorem rows22240R_2894 : rowsJ2 102 103 102 340 ≤ 13606736960985 := by decide +kernel

theorem rows22240R_2895 : rowsJ2 103 104 0 18 ≤ 0 := by decide +kernel

theorem rows22240R_2896 : rowsJ2 103 104 18 30 ≤ 423803957062 := by decide +kernel

theorem rows22240R_2897 : rowsJ2 103 104 30 34 ≤ 10939206463989 := by decide +kernel

theorem rows22240R_2898 : rowsJ2 103 104 34 36 ≤ 14339175867046 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2882
#print axioms SieveCert.rows22240R_2898
