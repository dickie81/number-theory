/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2495–2507 of 4715

File 205 of 351: the parts `rows22250R_2495` … `rows22250R_2507` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 92530 in units of a depth-4 test: row 97 columns 52–53, row 97 columns
54–56, row 97 columns 57–61, row 97 columns 62–68, row 97 columns 69–74, row 97 columns 75–77, row 97 columns 78–79,
row 97 columns 80–80, row 97 columns 81–81, row 97 columns 82–82, row 97 columns 83–83, row 97 columns 84–84, row 97
columns 85–85), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22250R_2495 : rowsJ2 97 98 52 54 ≤ 3226620126905 := by decide +kernel

theorem rows22250R_2496 : rowsJ2 97 98 54 57 ≤ 1058129659927 := by decide +kernel

theorem rows22250R_2497 : rowsJ2 97 98 57 62 ≤ 0 := by decide +kernel

theorem rows22250R_2498 : rowsJ2 97 98 62 69 ≤ 0 := by decide +kernel

theorem rows22250R_2499 : rowsJ2 97 98 69 75 ≤ 0 := by decide +kernel

theorem rows22250R_2500 : rowsJ2 97 98 75 78 ≤ 362234649371 := by decide +kernel

theorem rows22250R_2501 : rowsJ2 97 98 78 80 ≤ 1234763536641 := by decide +kernel

theorem rows22250R_2502 : rowsJ2 97 98 80 81 ≤ 1118610071729 := by decide +kernel

theorem rows22250R_2503 : rowsJ2 97 98 81 82 ≤ 1546266731890 := by decide +kernel

theorem rows22250R_2504 : rowsJ2 97 98 82 83 ≤ 2128574070558 := by decide +kernel

theorem rows22250R_2505 : rowsJ2 97 98 83 84 ≤ 2595989597282 := by decide +kernel

theorem rows22250R_2506 : rowsJ2 97 98 84 85 ≤ 2803539390976 := by decide +kernel

theorem rows22250R_2507 : rowsJ2 97 98 85 86 ≤ 2624946525416 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2495
#print axioms SieveCert.rows22250R_2507
