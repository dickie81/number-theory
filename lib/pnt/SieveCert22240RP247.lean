/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2966–2985 of 5066

File 247 of 387: the parts `rows22240R_2966` … `rows22240R_2985` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (20 parts, work 94628 in units of a depth-4 test: row 104 columns 82–82, row 104
columns 83–83, row 104 columns 84–84, row 104 columns 85–85, row 104 columns 86–86, row 104 columns 87–87, row 104
columns 88–88, row 104 columns 89–89, row 104 columns 90–90, row 104 columns 91–91, row 104 columns 92–92, row 104
columns 93–93, row 104 columns 94–94, row 104 columns 95–95, row 104 columns 96–96, row 104 columns 97–97, row 104
columns 98–98, row 104 columns 99–99, row 104 columns 100–100, row 104 columns 101–101), each a sum of refined costs
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

theorem rows22240R_2966 : rowsJ2 104 105 82 83 ≤ 1133212510030 := by decide +kernel

theorem rows22240R_2967 : rowsJ2 104 105 83 84 ≤ 1056994505168 := by decide +kernel

theorem rows22240R_2968 : rowsJ2 104 105 84 85 ≤ 1077583061029 := by decide +kernel

theorem rows22240R_2969 : rowsJ2 104 105 85 86 ≤ 1182141317129 := by decide +kernel

theorem rows22240R_2970 : rowsJ2 104 105 86 87 ≤ 1343356128130 := by decide +kernel

theorem rows22240R_2971 : rowsJ2 104 105 87 88 ≤ 1591092615266 := by decide +kernel

theorem rows22240R_2972 : rowsJ2 104 105 88 89 ≤ 1897623932905 := by decide +kernel

theorem rows22240R_2973 : rowsJ2 104 105 89 90 ≤ 2293817816651 := by decide +kernel

theorem rows22240R_2974 : rowsJ2 104 105 90 91 ≤ 2751643614997 := by decide +kernel

theorem rows22240R_2975 : rowsJ2 104 105 91 92 ≤ 3303128040019 := by decide +kernel

theorem rows22240R_2976 : rowsJ2 104 105 92 93 ≤ 3919720265084 := by decide +kernel

theorem rows22240R_2977 : rowsJ2 104 105 93 94 ≤ 4634518272298 := by decide +kernel

theorem rows22240R_2978 : rowsJ2 104 105 94 95 ≤ 5418432058795 := by decide +kernel

theorem rows22240R_2979 : rowsJ2 104 105 95 96 ≤ 6305709404344 := by decide +kernel

theorem rows22240R_2980 : rowsJ2 104 105 96 97 ≤ 7266704407030 := by decide +kernel

theorem rows22240R_2981 : rowsJ2 104 105 97 98 ≤ 8336902844254 := by decide +kernel

theorem rows22240R_2982 : rowsJ2 104 105 98 99 ≤ 9486088461784 := by decide +kernel

theorem rows22240R_2983 : rowsJ2 104 105 99 100 ≤ 10751082694409 := by decide +kernel

theorem rows22240R_2984 : rowsJ2 104 105 100 101 ≤ 12101089429899 := by decide +kernel

theorem rows22240R_2985 : rowsJ2 104 105 101 102 ≤ 13574373561562 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2966
#print axioms SieveCert.rows22240R_2985
