/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4758–4773 of 5066

File 369 of 387: the parts `rows22240R_4758` … `rows22240R_4773` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 97844 in units of a depth-4 test: row 172 columns 41–41, row 172
columns 42–42, row 172 columns 43–43, row 172 columns 44–44, row 172 columns 45–45, row 172 columns 46–46, row 172
columns 47–47, row 172 columns 48–48, row 172 columns 49–49, row 172 columns 50–50, row 172 columns 51–51, row 172
columns 52–52, row 172 columns 53–54, row 172 columns 55–339, row 173 columns 0–36, row 173 columns 37–38), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22240R_4758 : rowsJ2 172 173 41 42 ≤ 13413723516152 := by decide +kernel

theorem rows22240R_4759 : rowsJ2 172 173 42 43 ≤ 15015750757997 := by decide +kernel

theorem rows22240R_4760 : rowsJ2 172 173 43 44 ≤ 16684639446811 := by decide +kernel

theorem rows22240R_4761 : rowsJ2 172 173 44 45 ≤ 18418177846416 := by decide +kernel

theorem rows22240R_4762 : rowsJ2 172 173 45 46 ≤ 20214435089655 := by decide +kernel

theorem rows22240R_4763 : rowsJ2 172 173 46 47 ≤ 22071775873838 := by decide +kernel

theorem rows22240R_4764 : rowsJ2 172 173 47 48 ≤ 23988876219560 := by decide +kernel

theorem rows22240R_4765 : rowsJ2 172 173 48 49 ≤ 21605359173538 := by decide +kernel

theorem rows22240R_4766 : rowsJ2 172 173 49 50 ≤ 19368993337956 := by decide +kernel

theorem rows22240R_4767 : rowsJ2 172 173 50 51 ≤ 17274652032417 := by decide +kernel

theorem rows22240R_4768 : rowsJ2 172 173 51 52 ≤ 15317590729314 := by decide +kernel

theorem rows22240R_4769 : rowsJ2 172 173 52 53 ≤ 13493455442538 := by decide +kernel

theorem rows22240R_4770 : rowsJ2 172 173 53 55 ≤ 22026517553851 := by decide +kernel

theorem rows22240R_4771 : rowsJ2 172 173 55 340 ≤ 2726665454322914 := by decide +kernel

theorem rows22240R_4772 : rowsJ2 173 174 0 37 ≤ 17807507810791 := by decide +kernel

theorem rows22240R_4773 : rowsJ2 173 174 37 39 ≤ 18446173959380 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4758
#print axioms SieveCert.rows22240R_4773
