/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4439–4448 of 5796

File 367 of 465: the parts `rows22250R_4439` … `rows22250R_4448` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 97757 tests: row 143 columns 61–61, row 143 columns 62–62, row 143 columns
63–63, row 143 columns 64–64, row 143 columns 65–65, row 143 columns 66–66, row 143 columns 67–67, row 143 columns
68–68, row 143 columns 69–69, row 143 columns 70–70), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4439 : rowsJ2 143 144 61 62 ≤ 5295914577677 := by decide +kernel

theorem rows22250R_4440 : rowsJ2 143 144 62 63 ≤ 5971203881391 := by decide +kernel

theorem rows22250R_4441 : rowsJ2 143 144 63 64 ≤ 6678045178603 := by decide +kernel

theorem rows22250R_4442 : rowsJ2 143 144 64 65 ≤ 7381871921778 := by decide +kernel

theorem rows22250R_4443 : rowsJ2 143 144 65 66 ≤ 8031986748970 := by decide +kernel

theorem rows22250R_4444 : rowsJ2 143 144 66 67 ≤ 8645172668987 := by decide +kernel

theorem rows22250R_4445 : rowsJ2 143 144 67 68 ≤ 9204199731165 := by decide +kernel

theorem rows22250R_4446 : rowsJ2 143 144 68 69 ≤ 9725842232556 := by decide +kernel

theorem rows22250R_4447 : rowsJ2 143 144 69 70 ≤ 9501442461843 := by decide +kernel

theorem rows22250R_4448 : rowsJ2 143 144 70 71 ≤ 8621296793656 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4439
#print axioms SieveCert.rows22250R_4448
