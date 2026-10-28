/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4694–4710 of 5066

File 365 of 387: the parts `rows22240R_4694` … `rows22240R_4710` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 97274 in units of a depth-4 test: row 168 columns 52–52, row 168
columns 53–53, row 168 columns 54–54, row 168 columns 55–55, row 168 columns 56–57, row 168 columns 58–59, row 168
columns 60–339, row 169 columns 0–37, row 169 columns 38–39, row 169 columns 40–41, row 169 columns 42–42, row 169
columns 43–43, row 169 columns 44–44, row 169 columns 45–45, row 169 columns 46–46, row 169 columns 47–47, row 169
columns 48–48), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4694 : rowsJ2 168 169 52 53 ≤ 15938270316334 := by decide +kernel

theorem rows22240R_4695 : rowsJ2 168 169 53 54 ≤ 14135562216048 := by decide +kernel

theorem rows22240R_4696 : rowsJ2 168 169 54 55 ≤ 12454590077344 := by decide +kernel

theorem rows22240R_4697 : rowsJ2 168 169 55 56 ≤ 10891794924145 := by decide +kernel

theorem rows22240R_4698 : rowsJ2 168 169 56 58 ≤ 17551929214194 := by decide +kernel

theorem rows22240R_4699 : rowsJ2 168 169 58 60 ≤ 12642678453813 := by decide +kernel

theorem rows22240R_4700 : rowsJ2 168 169 60 340 ≤ 2642787097469724 := by decide +kernel

theorem rows22240R_4701 : rowsJ2 169 170 0 38 ≤ 14654273955165 := by decide +kernel

theorem rows22240R_4702 : rowsJ2 169 170 38 40 ≤ 14498105223436 := by decide +kernel

theorem rows22240R_4703 : rowsJ2 169 170 40 42 ≤ 19560381599279 := by decide +kernel

theorem rows22240R_4704 : rowsJ2 169 170 42 43 ≤ 11858873735971 := by decide +kernel

theorem rows22240R_4705 : rowsJ2 169 170 43 44 ≤ 13334828761127 := by decide +kernel

theorem rows22240R_4706 : rowsJ2 169 170 44 45 ≤ 14875180874416 := by decide +kernel

theorem rows22240R_4707 : rowsJ2 169 170 45 46 ≤ 16477683263591 := by decide +kernel

theorem rows22240R_4708 : rowsJ2 169 170 46 47 ≤ 18140351874823 := by decide +kernel

theorem rows22240R_4709 : rowsJ2 169 170 47 48 ≤ 19861528610540 := by decide +kernel

theorem rows22240R_4710 : rowsJ2 169 170 48 49 ≤ 21639786454215 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4694
#print axioms SieveCert.rows22240R_4710
