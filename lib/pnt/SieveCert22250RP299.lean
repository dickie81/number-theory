/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3434–3449 of 5796

File 299 of 465: the parts `rows22250R_3434` … `rows22250R_3449` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 99730 tests: row 112 columns 38–38, row 112 columns 39–39, row 112 columns
40–40, row 112 columns 41–41, row 112 columns 42–42, row 112 columns 43–43, row 112 columns 44–45, row 112 columns
46–47, row 112 columns 48–49, row 112 columns 50–52, row 112 columns 53–57, row 112 columns 58–66, row 112 columns
67–73, row 112 columns 74–77, row 112 columns 78–80, row 112 columns 81–82), each a sum of refined costs (`rows2` or
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

theorem rows22250R_3434 : rowsJ2 112 113 38 39 ≤ 11572080588343 := by decide +kernel

theorem rows22250R_3435 : rowsJ2 112 113 39 40 ≤ 13717754243898 := by decide +kernel

theorem rows22250R_3436 : rowsJ2 112 113 40 41 ≤ 11949605552309 := by decide +kernel

theorem rows22250R_3437 : rowsJ2 112 113 41 42 ≤ 10348172293832 := by decide +kernel

theorem rows22250R_3438 : rowsJ2 112 113 42 43 ≤ 8909396291196 := by decide +kernel

theorem rows22250R_3439 : rowsJ2 112 113 43 44 ≤ 7629602735497 := by decide +kernel

theorem rows22250R_3440 : rowsJ2 112 113 44 46 ≤ 11700390743726 := by decide +kernel

theorem rows22250R_3441 : rowsJ2 112 113 46 48 ≤ 7425057702404 := by decide +kernel

theorem rows22250R_3442 : rowsJ2 112 113 48 50 ≤ 4060960359169 := by decide +kernel

theorem rows22250R_3443 : rowsJ2 112 113 50 53 ≤ 2401918201404 := by decide +kernel

theorem rows22250R_3444 : rowsJ2 112 113 53 58 ≤ 315989664676 := by decide +kernel

theorem rows22250R_3445 : rowsJ2 112 113 58 67 ≤ 61270097103 := by decide +kernel

theorem rows22250R_3446 : rowsJ2 112 113 67 74 ≤ 0 := by decide +kernel

theorem rows22250R_3447 : rowsJ2 112 113 74 78 ≤ 0 := by decide +kernel

theorem rows22250R_3448 : rowsJ2 112 113 78 81 ≤ 47552420459 := by decide +kernel

theorem rows22250R_3449 : rowsJ2 112 113 81 83 ≤ 436150614193 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3434
#print axioms SieveCert.rows22250R_3449
