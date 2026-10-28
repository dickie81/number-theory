/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4790–4805 of 5066

File 371 of 387: the parts `rows22240R_4790` … `rows22240R_4805` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 97377 in units of a depth-4 test: row 174 columns 36–38, row 174
columns 39–40, row 174 columns 41–41, row 174 columns 42–42, row 174 columns 43–43, row 174 columns 44–44, row 174
columns 45–45, row 174 columns 46–46, row 174 columns 47–47, row 174 columns 48–48, row 174 columns 49–49, row 174
columns 50–50, row 174 columns 51–51, row 174 columns 52–53, row 174 columns 54–339, row 175 columns 0–35), each a
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

theorem rows22240R_4790 : rowsJ2 174 175 36 39 ≤ 27518016855691 := by decide +kernel

theorem rows22240R_4791 : rowsJ2 174 175 39 41 ≤ 26393184494928 := by decide +kernel

theorem rows22240R_4792 : rowsJ2 174 175 41 42 ≤ 15664472152642 := by decide +kernel

theorem rows22240R_4793 : rowsJ2 174 175 42 43 ≤ 17403194192554 := by decide +kernel

theorem rows22240R_4794 : rowsJ2 174 175 43 44 ≤ 19209090983221 := by decide +kernel

theorem rows22240R_4795 : rowsJ2 174 175 44 45 ≤ 21080182788024 := by decide +kernel

theorem rows22240R_4796 : rowsJ2 174 175 45 46 ≤ 23014775618826 := by decide +kernel

theorem rows22240R_4797 : rowsJ2 174 175 46 47 ≤ 25011502530502 := by decide +kernel

theorem rows22240R_4798 : rowsJ2 174 175 47 48 ≤ 22523217503425 := by decide +kernel

theorem rows22240R_4799 : rowsJ2 174 175 48 49 ≤ 20189208913475 := by decide +kernel

theorem rows22240R_4800 : rowsJ2 174 175 49 50 ≤ 18003989023712 := by decide +kernel

theorem rows22240R_4801 : rowsJ2 174 175 50 51 ≤ 15962514969035 := by decide +kernel

theorem rows22240R_4802 : rowsJ2 174 175 51 52 ≤ 14060143917740 := by decide +kernel

theorem rows22240R_4803 : rowsJ2 174 175 52 54 ≤ 22948575237043 := by decide +kernel

theorem rows22240R_4804 : rowsJ2 174 175 54 340 ≤ 2767931165655779 := by decide +kernel

theorem rows22240R_4805 : rowsJ2 175 176 0 36 ≤ 15814215887305 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4790
#print axioms SieveCert.rows22240R_4805
