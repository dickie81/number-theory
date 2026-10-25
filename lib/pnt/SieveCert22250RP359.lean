/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4335–4347 of 5796

File 359 of 465: the parts `rows22250R_4335` … `rows22250R_4347` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 94486 tests: row 140 columns 25–29, row 140 columns 30–50, row 140 columns
51–55, row 140 columns 56–57, row 140 columns 58–59, row 140 columns 60–60, row 140 columns 61–61, row 140 columns
62–62, row 140 columns 63–63, row 140 columns 64–64, row 140 columns 65–65, row 140 columns 66–66, row 140 columns
67–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4335 : rowsJ2 140 141 25 30 ≤ 8909111843216 := by decide +kernel

theorem rows22250R_4336 : rowsJ2 140 141 30 51 ≤ 1586518117483 := by decide +kernel

theorem rows22250R_4337 : rowsJ2 140 141 51 56 ≤ 3706358823585 := by decide +kernel

theorem rows22250R_4338 : rowsJ2 140 141 56 58 ≤ 3812307120711 := by decide +kernel

theorem rows22250R_4339 : rowsJ2 140 141 58 60 ≤ 5643696956051 := by decide +kernel

theorem rows22250R_4340 : rowsJ2 140 141 60 61 ≤ 3601902151296 := by decide +kernel

theorem rows22250R_4341 : rowsJ2 140 141 61 62 ≤ 4168689647472 := by decide +kernel

theorem rows22250R_4342 : rowsJ2 140 141 62 63 ≤ 4768840414563 := by decide +kernel

theorem rows22250R_4343 : rowsJ2 140 141 63 64 ≤ 5401104851077 := by decide +kernel

theorem rows22250R_4344 : rowsJ2 140 141 64 65 ≤ 6030310095443 := by decide +kernel

theorem rows22250R_4345 : rowsJ2 140 141 65 66 ≤ 6604897004533 := by decide +kernel

theorem rows22250R_4346 : rowsJ2 140 141 66 67 ≤ 7141852771420 := by decide +kernel

theorem rows22250R_4347 : rowsJ2 140 141 67 68 ≤ 7623613221018 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4335
#print axioms SieveCert.rows22250R_4347
