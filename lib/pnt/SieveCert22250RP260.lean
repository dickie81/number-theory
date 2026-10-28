/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3351–3366 of 4715

File 260 of 351: the parts `rows22250R_3351` … `rows22250R_3366` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 99614 in units of a depth-4 test: row 126 columns 61–61, row 126
columns 62–62, row 126 columns 63–63, row 126 columns 64–64, row 126 columns 65–65, row 126 columns 66–66, row 126
columns 67–67, row 126 columns 68–68, row 126 columns 69–69, row 126 columns 70–70, row 126 columns 71–71, row 126
columns 72–72, row 126 columns 73–73, row 126 columns 74–75, row 126 columns 76–77, row 126 columns 78–81), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3351 : rowsJ2 126 127 61 62 ≤ 4254522020242 := by decide +kernel

theorem rows22250R_3352 : rowsJ2 126 127 62 63 ≤ 4693689283227 := by decide +kernel

theorem rows22250R_3353 : rowsJ2 126 127 63 64 ≤ 5083354283523 := by decide +kernel

theorem rows22250R_3354 : rowsJ2 126 127 64 65 ≤ 5400147536696 := by decide +kernel

theorem rows22250R_3355 : rowsJ2 126 127 65 66 ≤ 5666068555287 := by decide +kernel

theorem rows22250R_3356 : rowsJ2 126 127 66 67 ≤ 5857230569079 := by decide +kernel

theorem rows22250R_3357 : rowsJ2 126 127 67 68 ≤ 5995584869571 := by decide +kernel

theorem rows22250R_3358 : rowsJ2 126 127 68 69 ≤ 6056677604474 := by decide +kernel

theorem rows22250R_3359 : rowsJ2 126 127 69 70 ≤ 6062390109262 := by decide +kernel

theorem rows22250R_3360 : rowsJ2 126 127 70 71 ≤ 5273748219025 := by decide +kernel

theorem rows22250R_3361 : rowsJ2 126 127 71 72 ≤ 4551839822374 := by decide +kernel

theorem rows22250R_3362 : rowsJ2 126 127 72 73 ≤ 3871415285645 := by decide +kernel

theorem rows22250R_3363 : rowsJ2 126 127 73 74 ≤ 3254950537882 := by decide +kernel

theorem rows22250R_3364 : rowsJ2 126 127 74 76 ≤ 4837709207001 := by decide +kernel

theorem rows22250R_3365 : rowsJ2 126 127 76 78 ≤ 2939295505100 := by decide +kernel

theorem rows22250R_3366 : rowsJ2 126 127 78 82 ≤ 1655852565649 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3351
#print axioms SieveCert.rows22250R_3366
