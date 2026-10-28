/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 881–892 of 5066

File 88 of 387: the parts `rows22240R_881` … `rows22240R_892` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 93374 in units of a depth-4 test: row 59 columns 42–42, row 59 columns
43–43, row 59 columns 44–44, row 59 columns 45–45, row 59 columns 46–46, row 59 columns 47–47, row 59 columns 48–48,
row 59 columns 49–49, row 59 columns 50–50, row 59 columns 51–51, row 59 columns 52–52, row 59 columns 53–53), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_881 : rowsJ2 59 60 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_882 : rowsJ2 59 60 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_883 : rowsJ2 59 60 44 45 ≤ 70625366589 := by decide +kernel

theorem rows22240R_884 : rowsJ2 59 60 45 46 ≤ 206539796408 := by decide +kernel

theorem rows22240R_885 : rowsJ2 59 60 46 47 ≤ 402781546578 := by decide +kernel

theorem rows22240R_886 : rowsJ2 59 60 47 48 ≤ 859972104261 := by decide +kernel

theorem rows22240R_887 : rowsJ2 59 60 48 49 ≤ 1642976494053 := by decide +kernel

theorem rows22240R_888 : rowsJ2 59 60 49 50 ≤ 2533685380045 := by decide +kernel

theorem rows22240R_889 : rowsJ2 59 60 50 51 ≤ 3457194592887 := by decide +kernel

theorem rows22240R_890 : rowsJ2 59 60 51 52 ≤ 4548802099407 := by decide +kernel

theorem rows22240R_891 : rowsJ2 59 60 52 53 ≤ 5945484796868 := by decide +kernel

theorem rows22240R_892 : rowsJ2 59 60 53 54 ≤ 7359121891853 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_881
#print axioms SieveCert.rows22240R_892
