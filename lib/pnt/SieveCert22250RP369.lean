/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4463–4475 of 5796

File 369 of 465: the parts `rows22250R_4463` … `rows22250R_4475` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 95388 tests: row 144 columns 0–23, row 144 columns 24–32, row 144 columns
33–53, row 144 columns 54–55, row 144 columns 56–57, row 144 columns 58–58, row 144 columns 59–59, row 144 columns
60–60, row 144 columns 61–61, row 144 columns 62–62, row 144 columns 63–63, row 144 columns 64–64, row 144 columns
65–65), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_4463 : rowsJ2 144 145 0 24 ≤ 2963325811937 := by decide +kernel

theorem rows22250R_4464 : rowsJ2 144 145 24 33 ≤ 3806386710408 := by decide +kernel

theorem rows22250R_4465 : rowsJ2 144 145 33 54 ≤ 4088714767516 := by decide +kernel

theorem rows22250R_4466 : rowsJ2 144 145 54 56 ≤ 4042466532567 := by decide +kernel

theorem rows22250R_4467 : rowsJ2 144 145 56 58 ≤ 5981359408971 := by decide +kernel

theorem rows22250R_4468 : rowsJ2 144 145 58 59 ≤ 3816059512805 := by decide +kernel

theorem rows22250R_4469 : rowsJ2 144 145 59 60 ≤ 4415531794866 := by decide +kernel

theorem rows22250R_4470 : rowsJ2 144 145 60 61 ≤ 5050105381521 := by decide +kernel

theorem rows22250R_4471 : rowsJ2 144 145 61 62 ≤ 5718450901802 := by decide +kernel

theorem rows22250R_4472 : rowsJ2 144 145 62 63 ≤ 6419333726647 := by decide +kernel

theorem rows22250R_4473 : rowsJ2 144 145 63 64 ≤ 7151609189171 := by decide +kernel

theorem rows22250R_4474 : rowsJ2 144 145 64 65 ≤ 7880910073793 := by decide +kernel

theorem rows22250R_4475 : rowsJ2 144 145 65 66 ≤ 8556821820218 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4463
#print axioms SieveCert.rows22250R_4475
