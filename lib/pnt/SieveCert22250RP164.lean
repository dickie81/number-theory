/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1945–1957 of 4715

File 164 of 351: the parts `rows22250R_1945` … `rows22250R_1957` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 97386 in units of a depth-4 test: row 84 columns 44–44, row 84 columns
45–45, row 84 columns 46–46, row 84 columns 47–47, row 84 columns 48–48, row 84 columns 49–49, row 84 columns 50–50,
row 84 columns 51–51, row 84 columns 52–52, row 84 columns 53–53, row 84 columns 54–54, row 84 columns 55–55, row 84
columns 56–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22250R_1945 : rowsJ2 84 85 44 45 ≤ 56310591131 := by decide +kernel

theorem rows22250R_1946 : rowsJ2 84 85 45 46 ≤ 112022917220 := by decide +kernel

theorem rows22250R_1947 : rowsJ2 84 85 46 47 ≤ 170961095368 := by decide +kernel

theorem rows22250R_1948 : rowsJ2 84 85 47 48 ≤ 229359036709 := by decide +kernel

theorem rows22250R_1949 : rowsJ2 84 85 48 49 ≤ 173068224664 := by decide +kernel

theorem rows22250R_1950 : rowsJ2 84 85 49 50 ≤ 173168301781 := by decide +kernel

theorem rows22250R_1951 : rowsJ2 84 85 50 51 ≤ 116197764205 := by decide +kernel

theorem rows22250R_1952 : rowsJ2 84 85 51 52 ≤ 116311564086 := by decide +kernel

theorem rows22250R_1953 : rowsJ2 84 85 52 53 ≤ 58558823988 := by decide +kernel

theorem rows22250R_1954 : rowsJ2 84 85 53 54 ≤ 58639539000 := by decide +kernel

theorem rows22250R_1955 : rowsJ2 84 85 54 55 ≤ 0 := by decide +kernel

theorem rows22250R_1956 : rowsJ2 84 85 55 56 ≤ 0 := by decide +kernel

theorem rows22250R_1957 : rowsJ2 84 85 56 57 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1945
#print axioms SieveCert.rows22250R_1957
