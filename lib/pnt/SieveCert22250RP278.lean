/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3617–3631 of 4715

File 278 of 351: the parts `rows22250R_3617` … `rows22250R_3631` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 94371 in units of a depth-4 test: row 135 columns 74–75, row 135
columns 76–77, row 135 columns 78–81, row 135 columns 82–90, row 135 columns 91–339, row 136 columns 0–23, row 136
columns 24–47, row 136 columns 48–52, row 136 columns 53–54, row 136 columns 55–55, row 136 columns 56–56, row 136
columns 57–57, row 136 columns 58–58, row 136 columns 59–59, row 136 columns 60–60), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3617 : rowsJ2 135 136 74 76 ≤ 5768774041723 := by decide +kernel

theorem rows22250R_3618 : rowsJ2 135 136 76 78 ≤ 3849267781475 := by decide +kernel

theorem rows22250R_3619 : rowsJ2 135 136 78 82 ≤ 3424533320002 := by decide +kernel

theorem rows22250R_3620 : rowsJ2 135 136 82 91 ≤ 380819077490923 := by decide +kernel

theorem rows22250R_3621 : rowsJ2 135 136 91 340 ≤ 168692118596946 := by decide +kernel

theorem rows22250R_3622 : rowsJ2 136 137 0 24 ≤ 5933914253046 := by decide +kernel

theorem rows22250R_3623 : rowsJ2 136 137 24 48 ≤ 3238684179796 := by decide +kernel

theorem rows22250R_3624 : rowsJ2 136 137 48 53 ≤ 7804925180127 := by decide +kernel

theorem rows22250R_3625 : rowsJ2 136 137 53 55 ≤ 6767065952090 := by decide +kernel

theorem rows22250R_3626 : rowsJ2 136 137 55 56 ≤ 4368195881944 := by decide +kernel

theorem rows22250R_3627 : rowsJ2 136 137 56 57 ≤ 5085870220056 := by decide +kernel

theorem rows22250R_3628 : rowsJ2 136 137 57 58 ≤ 5847098354217 := by decide +kernel

theorem rows22250R_3629 : rowsJ2 136 137 58 59 ≤ 6650151517895 := by decide +kernel

theorem rows22250R_3630 : rowsJ2 136 137 59 60 ≤ 7493431747169 := by decide +kernel

theorem rows22250R_3631 : rowsJ2 136 137 60 61 ≤ 8354370784716 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3617
#print axioms SieveCert.rows22250R_3631
