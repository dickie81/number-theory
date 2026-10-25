/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5208–5221 of 5796

File 427 of 465: the parts `rows22250R_5208` … `rows22250R_5221` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 97088 tests: row 170 columns 68–359, row 171 columns 0–41, row 171 columns
42–43, row 171 columns 44–45, row 171 columns 46–46, row 171 columns 47–47, row 171 columns 48–48, row 171 columns
49–49, row 171 columns 50–50, row 171 columns 51–51, row 171 columns 52–52, row 171 columns 53–53, row 171 columns
54–54, row 171 columns 55–55), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_5208 : rowsJ2 170 171 68 360 ≤ 2528896873227444 := by decide +kernel

theorem rows22250R_5209 : rowsJ2 171 172 0 42 ≤ 9435217297987 := by decide +kernel

theorem rows22250R_5210 : rowsJ2 171 172 42 44 ≤ 8541287089684 := by decide +kernel

theorem rows22250R_5211 : rowsJ2 171 172 44 46 ≤ 11904442444346 := by decide +kernel

theorem rows22250R_5212 : rowsJ2 171 172 46 47 ≤ 7350686693192 := by decide +kernel

theorem rows22250R_5213 : rowsJ2 171 172 47 48 ≤ 8351569420060 := by decide +kernel

theorem rows22250R_5214 : rowsJ2 171 172 48 49 ≤ 9401318572549 := by decide +kernel

theorem rows22250R_5215 : rowsJ2 171 172 49 50 ≤ 10498099629737 := by decide +kernel

theorem rows22250R_5216 : rowsJ2 171 172 50 51 ≤ 11640246703740 := by decide +kernel

theorem rows22250R_5217 : rowsJ2 171 172 51 52 ≤ 12826254004409 := by decide +kernel

theorem rows22250R_5218 : rowsJ2 171 172 52 53 ≤ 14054768161438 := by decide +kernel

theorem rows22250R_5219 : rowsJ2 171 172 53 54 ≤ 15324581352192 := by decide +kernel

theorem rows22250R_5220 : rowsJ2 171 172 54 55 ≤ 16634625191730 := by decide +kernel

theorem rows22250R_5221 : rowsJ2 171 172 55 56 ≤ 16475895948706 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5208
#print axioms SieveCert.rows22250R_5221
