/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3805–3817 of 4715

File 292 of 351: the parts `rows22250R_3805` … `rows22250R_3817` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 98874 in units of a depth-4 test: row 143 columns 42–48, row 143
columns 49–50, row 143 columns 51–52, row 143 columns 53–53, row 143 columns 54–54, row 143 columns 55–55, row 143
columns 56–56, row 143 columns 57–57, row 143 columns 58–58, row 143 columns 59–59, row 143 columns 60–60, row 143
columns 61–61, row 143 columns 62–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3805 : rowsJ2 143 144 42 49 ≤ 8178094393614 := by decide +kernel

theorem rows22250R_3806 : rowsJ2 143 144 49 51 ≤ 6912092901927 := by decide +kernel

theorem rows22250R_3807 : rowsJ2 143 144 51 53 ≤ 9805646328020 := by decide +kernel

theorem rows22250R_3808 : rowsJ2 143 144 53 54 ≤ 6114835346005 := by decide +kernel

theorem rows22250R_3809 : rowsJ2 143 144 54 55 ≤ 6986283120447 := by decide +kernel

theorem rows22250R_3810 : rowsJ2 143 144 55 56 ≤ 7902937598594 := by decide +kernel

theorem rows22250R_3811 : rowsJ2 143 144 56 57 ≤ 8863082663983 := by decide +kernel

theorem rows22250R_3812 : rowsJ2 143 144 57 58 ≤ 9865144700197 := by decide +kernel

theorem rows22250R_3813 : rowsJ2 143 144 58 59 ≤ 10907685324796 := by decide +kernel

theorem rows22250R_3814 : rowsJ2 143 144 59 60 ≤ 11989394783441 := by decide +kernel

theorem rows22250R_3815 : rowsJ2 143 144 60 61 ≤ 13088768800616 := by decide +kernel

theorem rows22250R_3816 : rowsJ2 143 144 61 62 ≤ 12947101992898 := by decide +kernel

theorem rows22250R_3817 : rowsJ2 143 144 62 63 ≤ 11638994616537 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3805
#print axioms SieveCert.rows22250R_3817
