/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4734–4746 of 5796

File 391 of 465: the parts `rows22250R_4734` … `rows22250R_4746` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 96168 tests: row 153 columns 0–27, row 153 columns 28–49, row 153 columns
50–51, row 153 columns 52–53, row 153 columns 54–54, row 153 columns 55–55, row 153 columns 56–56, row 153 columns
57–57, row 153 columns 58–58, row 153 columns 59–59, row 153 columns 60–60, row 153 columns 61–61, row 153 columns
62–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_4734 : rowsJ2 153 154 0 28 ≤ 502855377490 := by decide +kernel

theorem rows22250R_4735 : rowsJ2 153 154 28 50 ≤ 5613228049406 := by decide +kernel

theorem rows22250R_4736 : rowsJ2 153 154 50 52 ≤ 5150867129792 := by decide +kernel

theorem rows22250R_4737 : rowsJ2 153 154 52 54 ≤ 7462890749416 := by decide +kernel

theorem rows22250R_4738 : rowsJ2 153 154 54 55 ≤ 4707363176472 := by decide +kernel

theorem rows22250R_4739 : rowsJ2 153 154 55 56 ≤ 5412449346162 := by decide +kernel

theorem rows22250R_4740 : rowsJ2 153 154 56 57 ≤ 6156362597472 := by decide +kernel

theorem rows22250R_4741 : rowsJ2 153 154 57 58 ≤ 6937624916317 := by decide +kernel

theorem rows22250R_4742 : rowsJ2 153 154 58 59 ≤ 7754871608620 := by decide +kernel

theorem rows22250R_4743 : rowsJ2 153 154 59 60 ≤ 8606845529888 := by decide +kernel

theorem rows22250R_4744 : rowsJ2 153 154 60 61 ≤ 9492391800936 := by decide +kernel

theorem rows22250R_4745 : rowsJ2 153 154 61 62 ≤ 10410452978999 := by decide +kernel

theorem rows22250R_4746 : rowsJ2 153 154 62 63 ≤ 11360064657350 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4734
#print axioms SieveCert.rows22250R_4746
