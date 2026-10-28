/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4632–4646 of 5066

File 361 of 387: the parts `rows22240R_4632` … `rows22240R_4646` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 97302 in units of a depth-4 test: row 165 columns 50–50, row 165
columns 51–51, row 165 columns 52–52, row 165 columns 53–53, row 165 columns 54–54, row 165 columns 55–55, row 165
columns 56–56, row 165 columns 57–57, row 165 columns 58–59, row 165 columns 60–61, row 165 columns 62–339, row 166
columns 0–38, row 166 columns 39–41, row 166 columns 42–43, row 166 columns 44–44), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4632 : rowsJ2 165 166 50 51 ≤ 19992713415056 := by decide +kernel

theorem rows22240R_4633 : rowsJ2 165 166 51 52 ≤ 19788051643631 := by decide +kernel

theorem rows22240R_4634 : rowsJ2 165 166 52 53 ≤ 17788412127235 := by decide +kernel

theorem rows22240R_4635 : rowsJ2 165 166 53 54 ≤ 15912249762769 := by decide +kernel

theorem rows22240R_4636 : rowsJ2 165 166 54 55 ≤ 14155650165958 := by decide +kernel

theorem rows22240R_4637 : rowsJ2 165 166 55 56 ≤ 12514983594341 := by decide +kernel

theorem rows22240R_4638 : rowsJ2 165 166 56 57 ≤ 10986888940662 := by decide +kernel

theorem rows22240R_4639 : rowsJ2 165 166 57 58 ≤ 9568252450343 := by decide +kernel

theorem rows22240R_4640 : rowsJ2 165 166 58 60 ≤ 15304334134167 := by decide +kernel

theorem rows22240R_4641 : rowsJ2 165 166 60 62 ≤ 10876288169452 := by decide +kernel

theorem rows22240R_4642 : rowsJ2 165 166 62 340 ≤ 2611770558180897 := by decide +kernel

theorem rows22240R_4643 : rowsJ2 166 167 0 39 ≤ 13514653232797 := by decide +kernel

theorem rows22240R_4644 : rowsJ2 166 167 39 42 ≤ 20540952375381 := by decide +kernel

theorem rows22240R_4645 : rowsJ2 166 167 42 44 ≤ 19710298084164 := by decide +kernel

theorem rows22240R_4646 : rowsJ2 166 167 44 45 ≤ 11862949650457 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4632
#print axioms SieveCert.rows22240R_4646
