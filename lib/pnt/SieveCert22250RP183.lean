/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1881–1888 of 5796

File 183 of 465: the parts `rows22250R_1881` … `rows22250R_1888` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 91859 tests: row 80 columns 50–50, row 80 columns 51–51, row 80 columns
52–52, row 80 columns 53–53, row 80 columns 54–54, row 80 columns 55–55, row 80 columns 56–56, row 80 columns
57–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1881 : rowsJ2 80 81 50 51 ≤ 1194283347448 := by decide +kernel

theorem rows22250R_1882 : rowsJ2 80 81 51 52 ≤ 1555352727361 := by decide +kernel

theorem rows22250R_1883 : rowsJ2 80 81 52 53 ≤ 1975003846768 := by decide +kernel

theorem rows22250R_1884 : rowsJ2 80 81 53 54 ≤ 2212973316676 := by decide +kernel

theorem rows22250R_1885 : rowsJ2 80 81 54 55 ≤ 2310416470601 := by decide +kernel

theorem rows22250R_1886 : rowsJ2 80 81 55 56 ≤ 2369309829332 := by decide +kernel

theorem rows22250R_1887 : rowsJ2 80 81 56 57 ≤ 2188164373502 := by decide +kernel

theorem rows22250R_1888 : rowsJ2 80 81 57 58 ≤ 2008957524379 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1881
#print axioms SieveCert.rows22250R_1888
