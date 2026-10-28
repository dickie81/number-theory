/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3943–3959 of 4715

File 302 of 351: the parts `rows22250R_3943` … `rows22250R_3959` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, work 98128 in units of a depth-4 test: row 148 columns 63–63, row 148
columns 64–64, row 148 columns 65–65, row 148 columns 66–66, row 148 columns 67–68, row 148 columns 69–71, row 148
columns 72–77, row 148 columns 78–339, row 149 columns 0–43, row 149 columns 44–46, row 149 columns 47–48, row 149
columns 49–49, row 149 columns 50–50, row 149 columns 51–51, row 149 columns 52–52, row 149 columns 53–53, row 149
columns 54–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3943 : rowsJ2 148 149 63 64 ≤ 8267591803996 := by decide +kernel

theorem rows22250R_3944 : rowsJ2 148 149 64 65 ≤ 7203516651042 := by decide +kernel

theorem rows22250R_3945 : rowsJ2 148 149 65 66 ≤ 6218345245199 := by decide +kernel

theorem rows22250R_3946 : rowsJ2 148 149 66 67 ≤ 5310389112130 := by decide +kernel

theorem rows22250R_3947 : rowsJ2 148 149 67 69 ≤ 8198155534896 := by decide +kernel

theorem rows22250R_3948 : rowsJ2 148 149 69 72 ≤ 7335863000624 := by decide +kernel

theorem rows22250R_3949 : rowsJ2 148 149 72 78 ≤ 3743418723506 := by decide +kernel

theorem rows22250R_3950 : rowsJ2 148 149 78 340 ≤ 1753829894453961 := by decide +kernel

theorem rows22250R_3951 : rowsJ2 149 150 0 44 ≤ 4181636849558 := by decide +kernel

theorem rows22250R_3952 : rowsJ2 149 150 44 47 ≤ 8405327322108 := by decide +kernel

theorem rows22250R_3953 : rowsJ2 149 150 47 49 ≤ 9201004134932 := by decide +kernel

theorem rows22250R_3954 : rowsJ2 149 150 49 50 ≤ 5856509306120 := by decide +kernel

theorem rows22250R_3955 : rowsJ2 149 150 50 51 ≤ 6766292898362 := by decide +kernel

theorem rows22250R_3956 : rowsJ2 149 150 51 52 ≤ 7727542517768 := by decide +kernel

theorem rows22250R_3957 : rowsJ2 149 150 52 53 ≤ 8738188348200 := by decide +kernel

theorem rows22250R_3958 : rowsJ2 149 150 53 54 ≤ 9796335519815 := by decide +kernel

theorem rows22250R_3959 : rowsJ2 149 150 54 55 ≤ 10900254699451 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3943
#print axioms SieveCert.rows22250R_3959
