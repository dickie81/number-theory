/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2531–2546 of 5066

File 218 of 387: the parts `rows22240R_2531` … `rows22240R_2546` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 97027 in units of a depth-4 test: row 95 columns 26–32, row 95 columns
33–35, row 95 columns 36–37, row 95 columns 38–38, row 95 columns 39–39, row 95 columns 40–40, row 95 columns 41–41,
row 95 columns 42–42, row 95 columns 43–43, row 95 columns 44–44, row 95 columns 45–45, row 95 columns 46–46, row 95
columns 47–47, row 95 columns 48–48, row 95 columns 49–49, row 95 columns 50–50), each a sum of refined costs
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

theorem rows22240R_2531 : rowsJ2 95 96 26 33 ≤ 2022254927765 := by decide +kernel

theorem rows22240R_2532 : rowsJ2 95 96 33 36 ≤ 9318450061543 := by decide +kernel

theorem rows22240R_2533 : rowsJ2 95 96 36 38 ≤ 13347153276167 := by decide +kernel

theorem rows22240R_2534 : rowsJ2 95 96 38 39 ≤ 8711115313847 := by decide +kernel

theorem rows22240R_2535 : rowsJ2 95 96 39 40 ≤ 10095929742574 := by decide +kernel

theorem rows22240R_2536 : rowsJ2 95 96 40 41 ≤ 11598436601215 := by decide +kernel

theorem rows22240R_2537 : rowsJ2 95 96 41 42 ≤ 13212890717136 := by decide +kernel

theorem rows22240R_2538 : rowsJ2 95 96 42 43 ≤ 14771432478091 := by decide +kernel

theorem rows22240R_2539 : rowsJ2 95 96 43 44 ≤ 16101555173838 := by decide +kernel

theorem rows22240R_2540 : rowsJ2 95 96 44 45 ≤ 15747023334469 := by decide +kernel

theorem rows22240R_2541 : rowsJ2 95 96 45 46 ≤ 13996275363479 := by decide +kernel

theorem rows22240R_2542 : rowsJ2 95 96 46 47 ≤ 12265681394205 := by decide +kernel

theorem rows22240R_2543 : rowsJ2 95 96 47 48 ≤ 10613258726727 := by decide +kernel

theorem rows22240R_2544 : rowsJ2 95 96 48 49 ≤ 9076011035399 := by decide +kernel

theorem rows22240R_2545 : rowsJ2 95 96 49 50 ≤ 7709195593778 := by decide +kernel

theorem rows22240R_2546 : rowsJ2 95 96 50 51 ≤ 6448050674356 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2531
#print axioms SieveCert.rows22240R_2546
