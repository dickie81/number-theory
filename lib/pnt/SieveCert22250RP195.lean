/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2035–2043 of 5796

File 195 of 465: the parts `rows22250R_2035` … `rows22250R_2043` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 97820 tests: row 83 columns 51–51, row 83 columns 52–52, row 83 columns
53–53, row 83 columns 54–54, row 83 columns 55–55, row 83 columns 56–56, row 83 columns 57–57, row 83 columns 58–58,
row 83 columns 59–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2035 : rowsJ2 83 84 51 52 ≤ 1182919021999 := by decide +kernel

theorem rows22250R_2036 : rowsJ2 83 84 52 53 ≤ 1375701995123 := by decide +kernel

theorem rows22250R_2037 : rowsJ2 83 84 53 54 ≤ 1426887455108 := by decide +kernel

theorem rows22250R_2038 : rowsJ2 83 84 54 55 ≤ 1292633861433 := by decide +kernel

theorem rows22250R_2039 : rowsJ2 83 84 55 56 ≤ 1156205448302 := by decide +kernel

theorem rows22250R_2040 : rowsJ2 83 84 56 57 ≤ 1021161546826 := by decide +kernel

theorem rows22250R_2041 : rowsJ2 83 84 57 58 ≤ 930919969123 := by decide +kernel

theorem rows22250R_2042 : rowsJ2 83 84 58 59 ≤ 841592946904 := by decide +kernel

theorem rows22250R_2043 : rowsJ2 83 84 59 60 ≤ 750220197396 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2035
#print axioms SieveCert.rows22250R_2043
