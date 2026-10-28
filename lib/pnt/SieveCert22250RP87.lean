/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 937–949 of 4715

File 87 of 351: the parts `rows22250R_937` … `rows22250R_949` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 92111 in units of a depth-4 test: row 61 columns 41–41, row 61 columns
42–42, row 61 columns 43–43, row 61 columns 44–44, row 61 columns 45–45, row 61 columns 46–46, row 61 columns 47–47,
row 61 columns 48–48, row 61 columns 49–49, row 61 columns 50–50, row 61 columns 51–51, row 61 columns 52–52, row 61
columns 53–53), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22250R_937 : rowsJ2 61 62 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_938 : rowsJ2 61 62 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_939 : rowsJ2 61 62 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_940 : rowsJ2 61 62 44 45 ≤ 68299093062 := by decide +kernel

theorem rows22250R_941 : rowsJ2 61 62 45 46 ≤ 268074100574 := by decide +kernel

theorem rows22250R_942 : rowsJ2 61 62 46 47 ≤ 799758513238 := by decide +kernel

theorem rows22250R_943 : rowsJ2 61 62 47 48 ≤ 1588196351756 := by decide +kernel

theorem rows22250R_944 : rowsJ2 61 62 48 49 ≤ 2346797890168 := by decide +kernel

theorem rows22250R_945 : rowsJ2 61 62 49 50 ≤ 3209942257307 := by decide +kernel

theorem rows22250R_946 : rowsJ2 61 62 50 51 ≤ 4312135940591 := by decide +kernel

theorem rows22250R_947 : rowsJ2 61 62 51 52 ≤ 5649868284376 := by decide +kernel

theorem rows22250R_948 : rowsJ2 61 62 52 53 ≤ 6934062270009 := by decide +kernel

theorem rows22250R_949 : rowsJ2 61 62 53 54 ≤ 8111376423005 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_937
#print axioms SieveCert.rows22250R_949
