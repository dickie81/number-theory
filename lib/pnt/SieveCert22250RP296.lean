/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3862–3874 of 4715

File 296 of 351: the parts `rows22250R_3862` … `rows22250R_3874` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 98484 in units of a depth-4 test: row 145 columns 56–56, row 145
columns 57–57, row 145 columns 58–58, row 145 columns 59–59, row 145 columns 60–60, row 145 columns 61–61, row 145
columns 62–62, row 145 columns 63–63, row 145 columns 64–64, row 145 columns 65–65, row 145 columns 66–66, row 145
columns 67–67, row 145 columns 68–68), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_3862 : rowsJ2 145 146 56 57 ≤ 10192751733624 := by decide +kernel

theorem rows22250R_3863 : rowsJ2 145 146 57 58 ≤ 11268738801034 := by decide +kernel

theorem rows22250R_3864 : rowsJ2 145 146 58 59 ≤ 12385038627576 := by decide +kernel

theorem rows22250R_3865 : rowsJ2 145 146 59 60 ≤ 13540433660866 := by decide +kernel

theorem rows22250R_3866 : rowsJ2 145 146 60 61 ≤ 13413925559207 := by decide +kernel

theorem rows22250R_3867 : rowsJ2 145 146 61 62 ≤ 12041112147255 := by decide +kernel

theorem rows22250R_3868 : rowsJ2 145 146 62 63 ≤ 10751976581346 := by decide +kernel

theorem rows22250R_3869 : rowsJ2 145 146 63 64 ≤ 9544311578165 := by decide +kernel

theorem rows22250R_3870 : rowsJ2 145 146 64 65 ≤ 8416063847068 := by decide +kernel

theorem rows22250R_3871 : rowsJ2 145 146 65 66 ≤ 7365327143729 := by decide +kernel

theorem rows22250R_3872 : rowsJ2 145 146 66 67 ≤ 6390335946198 := by decide +kernel

theorem rows22250R_3873 : rowsJ2 145 146 67 68 ≤ 5489459712144 := by decide +kernel

theorem rows22250R_3874 : rowsJ2 145 146 68 69 ≤ 4661197681008 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3862
#print axioms SieveCert.rows22250R_3874
