/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4742–4757 of 5066

File 368 of 387: the parts `rows22240R_4742` … `rows22240R_4757` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 99763 in units of a depth-4 test: row 171 columns 43–43, row 171
columns 44–44, row 171 columns 45–45, row 171 columns 46–46, row 171 columns 47–47, row 171 columns 48–48, row 171
columns 49–49, row 171 columns 50–50, row 171 columns 51–51, row 171 columns 52–52, row 171 columns 53–53, row 171
columns 54–55, row 171 columns 56–339, row 172 columns 0–36, row 172 columns 37–38, row 172 columns 39–40), each a
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

theorem rows22240R_4742 : rowsJ2 171 172 43 44 ≤ 15499430440307 := by decide +kernel

theorem rows22240R_4743 : rowsJ2 171 172 44 45 ≤ 17167066634251 := by decide +kernel

theorem rows22240R_4744 : rowsJ2 171 172 45 46 ≤ 18897154640456 := by decide +kernel

theorem rows22240R_4745 : rowsJ2 171 172 46 47 ≤ 20687936674814 := by decide +kernel

theorem rows22240R_4746 : rowsJ2 171 172 47 48 ≤ 22537972731847 := by decide +kernel

theorem rows22240R_4747 : rowsJ2 171 172 48 49 ≤ 22299857714319 := by decide +kernel

theorem rows22240R_4748 : rowsJ2 171 172 49 50 ≤ 20039032989173 := by decide +kernel

theorem rows22240R_4749 : rowsJ2 171 172 50 51 ≤ 17919441489806 := by decide +kernel

theorem rows22240R_4750 : rowsJ2 171 172 51 52 ≤ 15936312864123 := by decide +kernel

theorem rows22240R_4751 : rowsJ2 171 172 52 53 ≤ 14085233249232 := by decide +kernel

theorem rows22240R_4752 : rowsJ2 171 172 53 54 ≤ 12362155681715 := by decide +kernel

theorem rows22240R_4753 : rowsJ2 171 172 54 56 ≤ 20048802972062 := by decide +kernel

theorem rows22240R_4754 : rowsJ2 171 172 56 340 ≤ 2703971018337487 := by decide +kernel

theorem rows22240R_4755 : rowsJ2 172 173 0 37 ≤ 15216636141722 := by decide +kernel

theorem rows22240R_4756 : rowsJ2 172 173 37 39 ≤ 16764612048836 := by decide +kernel

theorem rows22240R_4757 : rowsJ2 172 173 39 41 ≤ 22301657538396 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4742
#print axioms SieveCert.rows22240R_4757
