/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2151–2165 of 4715

File 179 of 351: the parts `rows22250R_2151` … `rows22250R_2165` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 96693 in units of a depth-4 test: row 89 columns 43–43, row 89 columns
44–44, row 89 columns 45–45, row 89 columns 46–46, row 89 columns 47–47, row 89 columns 48–48, row 89 columns 49–49,
row 89 columns 50–50, row 89 columns 51–51, row 89 columns 52–52, row 89 columns 53–53, row 89 columns 54–54, row 89
columns 55–55, row 89 columns 56–57, row 89 columns 58–59), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2151 : rowsJ2 89 90 43 44 ≤ 14446493285827 := by decide +kernel

theorem rows22250R_2152 : rowsJ2 89 90 44 45 ≤ 15851215439052 := by decide +kernel

theorem rows22250R_2153 : rowsJ2 89 90 45 46 ≤ 16973175425881 := by decide +kernel

theorem rows22250R_2154 : rowsJ2 89 90 46 47 ≤ 11882983886478 := by decide +kernel

theorem rows22250R_2155 : rowsJ2 89 90 47 48 ≤ 7149180240488 := by decide +kernel

theorem rows22250R_2156 : rowsJ2 89 90 48 49 ≤ 3365331376141 := by decide +kernel

theorem rows22250R_2157 : rowsJ2 89 90 49 50 ≤ 0 := by decide +kernel

theorem rows22250R_2158 : rowsJ2 89 90 50 51 ≤ 0 := by decide +kernel

theorem rows22250R_2159 : rowsJ2 89 90 51 52 ≤ 0 := by decide +kernel

theorem rows22250R_2160 : rowsJ2 89 90 52 53 ≤ 0 := by decide +kernel

theorem rows22250R_2161 : rowsJ2 89 90 53 54 ≤ 0 := by decide +kernel

theorem rows22250R_2162 : rowsJ2 89 90 54 55 ≤ 0 := by decide +kernel

theorem rows22250R_2163 : rowsJ2 89 90 55 56 ≤ 0 := by decide +kernel

theorem rows22250R_2164 : rowsJ2 89 90 56 58 ≤ 0 := by decide +kernel

theorem rows22250R_2165 : rowsJ2 89 90 58 60 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2151
#print axioms SieveCert.rows22250R_2165
