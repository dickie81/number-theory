/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4586–4599 of 5796

File 379 of 465: the parts `rows22250R_4586` … `rows22250R_4599` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 99415 tests: row 148 columns 0–23, row 148 columns 24–49, row 148 columns
50–52, row 148 columns 53–54, row 148 columns 55–55, row 148 columns 56–56, row 148 columns 57–57, row 148 columns
58–58, row 148 columns 59–59, row 148 columns 60–60, row 148 columns 61–61, row 148 columns 62–62, row 148 columns
63–63, row 148 columns 64–64), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4586 : rowsJ2 148 149 0 24 ≤ 2443012624531 := by decide +kernel

theorem rows22250R_4587 : rowsJ2 148 149 24 50 ≤ 2111871037906 := by decide +kernel

theorem rows22250R_4588 : rowsJ2 148 149 50 53 ≤ 4509700308865 := by decide +kernel

theorem rows22250R_4589 : rowsJ2 148 149 53 55 ≤ 5280806125262 := by decide +kernel

theorem rows22250R_4590 : rowsJ2 148 149 55 56 ≤ 3454336076210 := by decide +kernel

theorem rows22250R_4591 : rowsJ2 148 149 56 57 ≤ 4051097782914 := by decide +kernel

theorem rows22250R_4592 : rowsJ2 148 149 57 58 ≤ 4686381710816 := by decide +kernel

theorem rows22250R_4593 : rowsJ2 148 149 58 59 ≤ 5358661935201 := by decide +kernel

theorem rows22250R_4594 : rowsJ2 148 149 59 60 ≤ 6066521931056 := by decide +kernel

theorem rows22250R_4595 : rowsJ2 148 149 60 61 ≤ 6808648825933 := by decide +kernel

theorem rows22250R_4596 : rowsJ2 148 149 61 62 ≤ 7583828109579 := by decide +kernel

theorem rows22250R_4597 : rowsJ2 148 149 62 63 ≤ 8390938770459 := by decide +kernel

theorem rows22250R_4598 : rowsJ2 148 149 63 64 ≤ 9228948832271 := by decide +kernel

theorem rows22250R_4599 : rowsJ2 148 149 64 65 ≤ 10064276734537 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4586
#print axioms SieveCert.rows22250R_4599
