/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2437–2452 of 4715

File 201 of 351: the parts `rows22250R_2437` … `rows22250R_2452` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 97288 tests: row 96 columns 17–25, row 96 columns 26–32, row 96 columns
33–35, row 96 columns 36–37, row 96 columns 38–38, row 96 columns 39–39, row 96 columns 40–40, row 96 columns 41–41,
row 96 columns 42–42, row 96 columns 43–43, row 96 columns 44–44, row 96 columns 45–45, row 96 columns 46–46, row 96
columns 47–47, row 96 columns 48–48, row 96 columns 49–50), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22250R_2437 : rowsJ2 96 97 17 26 ≤ 0 := by decide +kernel

theorem rows22250R_2438 : rowsJ2 96 97 26 33 ≤ 3666472794984 := by decide +kernel

theorem rows22250R_2439 : rowsJ2 96 97 33 36 ≤ 13517773713003 := by decide +kernel

theorem rows22250R_2440 : rowsJ2 96 97 36 38 ≤ 17689024727729 := by decide +kernel

theorem rows22250R_2441 : rowsJ2 96 97 38 39 ≤ 11444402672439 := by decide +kernel

theorem rows22250R_2442 : rowsJ2 96 97 39 40 ≤ 12974000209777 := by decide +kernel

theorem rows22250R_2443 : rowsJ2 96 97 40 41 ≤ 14511307513915 := by decide +kernel

theorem rows22250R_2444 : rowsJ2 96 97 41 42 ≤ 15934400794801 := by decide +kernel

theorem rows22250R_2445 : rowsJ2 96 97 42 43 ≤ 15634003645987 := by decide +kernel

theorem rows22250R_2446 : rowsJ2 96 97 43 44 ≤ 13907001199333 := by decide +kernel

theorem rows22250R_2447 : rowsJ2 96 97 44 45 ≤ 12200281400698 := by decide +kernel

theorem rows22250R_2448 : rowsJ2 96 97 45 46 ≤ 10573937059953 := by decide +kernel

theorem rows22250R_2449 : rowsJ2 96 97 46 47 ≤ 8965177384912 := by decide +kernel

theorem rows22250R_2450 : rowsJ2 96 97 47 48 ≤ 7435036942612 := by decide +kernel

theorem rows22250R_2451 : rowsJ2 96 97 48 49 ≤ 6083493633950 := by decide +kernel

theorem rows22250R_2452 : rowsJ2 96 97 49 51 ≤ 8810026114072 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2437
#print axioms SieveCert.rows22250R_2452
