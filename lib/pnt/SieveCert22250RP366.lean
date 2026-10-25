/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4423–4438 of 5796

File 366 of 465: the parts `rows22250R_4423` … `rows22250R_4438` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 99768 tests: row 142 columns 77–77, row 142 columns 78–78, row 142 columns
79–79, row 142 columns 80–80, row 142 columns 81–82, row 142 columns 83–85, row 142 columns 86–89, row 142 columns
90–359, row 143 columns 0–23, row 143 columns 24–30, row 143 columns 31–52, row 143 columns 53–55, row 143 columns
56–57, row 143 columns 58–58, row 143 columns 59–59, row 143 columns 60–60), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4423 : rowsJ2 142 143 77 78 ≤ 3845466489755 := by decide +kernel

theorem rows22250R_4424 : rowsJ2 142 143 78 79 ≤ 3328726762236 := by decide +kernel

theorem rows22250R_4425 : rowsJ2 142 143 79 80 ≤ 2843104200481 := by decide +kernel

theorem rows22250R_4426 : rowsJ2 142 143 80 81 ≤ 2406033383716 := by decide +kernel

theorem rows22250R_4427 : rowsJ2 142 143 81 83 ≤ 3635360662212 := by decide +kernel

theorem rows22250R_4428 : rowsJ2 142 143 83 86 ≤ 3073188264035 := by decide +kernel

theorem rows22250R_4429 : rowsJ2 142 143 86 90 ≤ 7091876976305 := by decide +kernel

theorem rows22250R_4430 : rowsJ2 142 143 90 360 ≤ 482752949297687 := by decide +kernel

theorem rows22250R_4431 : rowsJ2 143 144 0 24 ≤ 2517091953924 := by decide +kernel

theorem rows22250R_4432 : rowsJ2 143 144 24 31 ≤ 5500561498833 := by decide +kernel

theorem rows22250R_4433 : rowsJ2 143 144 31 53 ≤ 2048307097401 := by decide +kernel

theorem rows22250R_4434 : rowsJ2 143 144 53 56 ≤ 4732077510201 := by decide +kernel

theorem rows22250R_4435 : rowsJ2 143 144 56 58 ≤ 5372106587192 := by decide +kernel

theorem rows22250R_4436 : rowsJ2 143 144 58 59 ≤ 3471529920568 := by decide +kernel

theorem rows22250R_4437 : rowsJ2 143 144 59 60 ≤ 4044768232653 := by decide +kernel

theorem rows22250R_4438 : rowsJ2 143 144 60 61 ≤ 4653348764448 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4423
#print axioms SieveCert.rows22250R_4438
