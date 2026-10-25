/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2990–3003 of 4715

File 236 of 351: the parts `rows22250R_2990` … `rows22250R_3003` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 98796 tests: row 111 columns 35–36, row 111 columns 37–38, row 111 columns
39–41, row 111 columns 42–45, row 111 columns 46–54, row 111 columns 55–63, row 111 columns 64–69, row 111 columns
70–73, row 111 columns 74–76, row 111 columns 77–79, row 111 columns 80–82, row 111 columns 83–85, row 111 columns
86–88, row 111 columns 89–90), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_2990 : rowsJ2 111 112 35 37 ≤ 22185162002928 := by decide +kernel

theorem rows22250R_2991 : rowsJ2 111 112 37 39 ≤ 17271449499488 := by decide +kernel

theorem rows22250R_2992 : rowsJ2 111 112 39 42 ≤ 14732673633884 := by decide +kernel

theorem rows22250R_2993 : rowsJ2 111 112 42 46 ≤ 7027325331364 := by decide +kernel

theorem rows22250R_2994 : rowsJ2 111 112 46 55 ≤ 541482289473 := by decide +kernel

theorem rows22250R_2995 : rowsJ2 111 112 55 64 ≤ 2287115897162 := by decide +kernel

theorem rows22250R_2996 : rowsJ2 111 112 64 70 ≤ 634827924608 := by decide +kernel

theorem rows22250R_2997 : rowsJ2 111 112 70 74 ≤ 0 := by decide +kernel

theorem rows22250R_2998 : rowsJ2 111 112 74 77 ≤ 100755481822 := by decide +kernel

theorem rows22250R_2999 : rowsJ2 111 112 77 80 ≤ 273904755133 := by decide +kernel

theorem rows22250R_3000 : rowsJ2 111 112 80 83 ≤ 186190946226 := by decide +kernel

theorem rows22250R_3001 : rowsJ2 111 112 83 86 ≤ 1921506227176 := by decide +kernel

theorem rows22250R_3002 : rowsJ2 111 112 86 89 ≤ 5828694555912 := by decide +kernel

theorem rows22250R_3003 : rowsJ2 111 112 89 91 ≤ 7127034228374 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2990
#print axioms SieveCert.rows22250R_3003
