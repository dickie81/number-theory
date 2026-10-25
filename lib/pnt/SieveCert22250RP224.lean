/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2423–2436 of 5796

File 224 of 465: the parts `rows22250R_2423` … `rows22250R_2436` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 93937 tests: row 91 columns 52–52, row 91 columns 53–53, row 91 columns
54–54, row 91 columns 55–55, row 91 columns 56–56, row 91 columns 57–57, row 91 columns 58–58, row 91 columns 59–59,
row 91 columns 60–60, row 91 columns 61–61, row 91 columns 62–62, row 91 columns 63–63, row 91 columns 64–64, row 91
columns 65–66), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22250R_2423 : rowsJ2 91 92 52 53 ≤ 0 := by decide +kernel

theorem rows22250R_2424 : rowsJ2 91 92 53 54 ≤ 0 := by decide +kernel

theorem rows22250R_2425 : rowsJ2 91 92 54 55 ≤ 0 := by decide +kernel

theorem rows22250R_2426 : rowsJ2 91 92 55 56 ≤ 0 := by decide +kernel

theorem rows22250R_2427 : rowsJ2 91 92 56 57 ≤ 0 := by decide +kernel

theorem rows22250R_2428 : rowsJ2 91 92 57 58 ≤ 0 := by decide +kernel

theorem rows22250R_2429 : rowsJ2 91 92 58 59 ≤ 0 := by decide +kernel

theorem rows22250R_2430 : rowsJ2 91 92 59 60 ≤ 0 := by decide +kernel

theorem rows22250R_2431 : rowsJ2 91 92 60 61 ≤ 0 := by decide +kernel

theorem rows22250R_2432 : rowsJ2 91 92 61 62 ≤ 0 := by decide +kernel

theorem rows22250R_2433 : rowsJ2 91 92 62 63 ≤ 0 := by decide +kernel

theorem rows22250R_2434 : rowsJ2 91 92 63 64 ≤ 0 := by decide +kernel

theorem rows22250R_2435 : rowsJ2 91 92 64 65 ≤ 0 := by decide +kernel

theorem rows22250R_2436 : rowsJ2 91 92 65 67 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2423
#print axioms SieveCert.rows22250R_2436
