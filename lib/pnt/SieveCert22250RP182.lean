/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2187–2202 of 4715

File 182 of 351: the parts `rows22250R_2187` … `rows22250R_2202` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 96581 tests: row 90 columns 36–37, row 90 columns 38–38, row 90 columns
39–39, row 90 columns 40–40, row 90 columns 41–41, row 90 columns 42–42, row 90 columns 43–43, row 90 columns 44–44,
row 90 columns 45–45, row 90 columns 46–46, row 90 columns 47–47, row 90 columns 48–48, row 90 columns 49–49, row 90
columns 50–50, row 90 columns 51–51, row 90 columns 52–52), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22250R_2187 : rowsJ2 90 91 36 38 ≤ 11913754866580 := by decide +kernel

theorem rows22250R_2188 : rowsJ2 90 91 38 39 ≤ 7940851640221 := by decide +kernel

theorem rows22250R_2189 : rowsJ2 90 91 39 40 ≤ 9158156083216 := by decide +kernel

theorem rows22250R_2190 : rowsJ2 90 91 40 41 ≤ 10496593581331 := by decide +kernel

theorem rows22250R_2191 : rowsJ2 90 91 41 42 ≤ 11950103024371 := by decide +kernel

theorem rows22250R_2192 : rowsJ2 90 91 42 43 ≤ 13513129921755 := by decide +kernel

theorem rows22250R_2193 : rowsJ2 90 91 43 44 ≤ 15066767057894 := by decide +kernel

theorem rows22250R_2194 : rowsJ2 90 91 44 45 ≤ 16335501839928 := by decide +kernel

theorem rows22250R_2195 : rowsJ2 90 91 45 46 ≤ 15981227032577 := by decide +kernel

theorem rows22250R_2196 : rowsJ2 90 91 46 47 ≤ 14174898007523 := by decide +kernel

theorem rows22250R_2197 : rowsJ2 90 91 47 48 ≤ 9493994410238 := by decide +kernel

theorem rows22250R_2198 : rowsJ2 90 91 48 49 ≤ 5702767766062 := by decide +kernel

theorem rows22250R_2199 : rowsJ2 90 91 49 50 ≤ 2390920266767 := by decide +kernel

theorem rows22250R_2200 : rowsJ2 90 91 50 51 ≤ 0 := by decide +kernel

theorem rows22250R_2201 : rowsJ2 90 91 51 52 ≤ 0 := by decide +kernel

theorem rows22250R_2202 : rowsJ2 90 91 52 53 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2187
#print axioms SieveCert.rows22250R_2202
