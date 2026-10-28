/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 936–945 of 5066

File 93 of 387: the parts `rows22240R_936` … `rows22240R_945` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (10 parts, work 94638 in units of a depth-4 test: row 60 columns 57–57, row 60 columns
58–58, row 60 columns 59–59, row 60 columns 60–339, row 61 columns 0–16, row 61 columns 17–20, row 61 columns 21–22,
row 61 columns 23–23, row 61 columns 24–24, row 61 columns 25–25), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_936 : rowsJ2 60 61 57 58 ≤ 12312400368020 := by decide +kernel

theorem rows22240R_937 : rowsJ2 60 61 58 59 ≤ 13249478649553 := by decide +kernel

theorem rows22240R_938 : rowsJ2 60 61 59 60 ≤ 14170027162888 := by decide +kernel

theorem rows22240R_939 : rowsJ2 60 61 60 340 ≤ 15196075680183 := by decide +kernel

theorem rows22240R_940 : rowsJ2 61 62 0 17 ≤ 2844963648603 := by decide +kernel

theorem rows22240R_941 : rowsJ2 61 62 17 21 ≤ 653064659236 := by decide +kernel

theorem rows22240R_942 : rowsJ2 61 62 21 23 ≤ 185187607165 := by decide +kernel

theorem rows22240R_943 : rowsJ2 61 62 23 24 ≤ 65666589898 := by decide +kernel

theorem rows22240R_944 : rowsJ2 61 62 24 25 ≤ 49245304304 := by decide +kernel

theorem rows22240R_945 : rowsJ2 61 62 25 26 ≤ 36869471475 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_936
#print axioms SieveCert.rows22240R_945
