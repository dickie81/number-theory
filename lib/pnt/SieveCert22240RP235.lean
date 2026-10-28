/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2771–2784 of 5066

File 235 of 387: the parts `rows22240R_2771` … `rows22240R_2784` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 97153 in units of a depth-4 test: row 100 columns 48–49, row 100
columns 50–51, row 100 columns 52–53, row 100 columns 54–56, row 100 columns 57–61, row 100 columns 62–68, row 100
columns 69–73, row 100 columns 74–77, row 100 columns 78–79, row 100 columns 80–80, row 100 columns 81–81, row 100
columns 82–82, row 100 columns 83–83, row 100 columns 84–84), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2771 : rowsJ2 100 101 48 50 ≤ 9657429645777 := by decide +kernel

theorem rows22240R_2772 : rowsJ2 100 101 50 52 ≤ 5934810828475 := by decide +kernel

theorem rows22240R_2773 : rowsJ2 100 101 52 54 ≤ 3213040100948 := by decide +kernel

theorem rows22240R_2774 : rowsJ2 100 101 54 57 ≤ 1222673260862 := by decide +kernel

theorem rows22240R_2775 : rowsJ2 100 101 57 62 ≤ 0 := by decide +kernel

theorem rows22240R_2776 : rowsJ2 100 101 62 69 ≤ 0 := by decide +kernel

theorem rows22240R_2777 : rowsJ2 100 101 69 74 ≤ 0 := by decide +kernel

theorem rows22240R_2778 : rowsJ2 100 101 74 78 ≤ 231612289774 := by decide +kernel

theorem rows22240R_2779 : rowsJ2 100 101 78 80 ≤ 963849977172 := by decide +kernel

theorem rows22240R_2780 : rowsJ2 100 101 80 81 ≤ 918344225777 := by decide +kernel

theorem rows22240R_2781 : rowsJ2 100 101 81 82 ≤ 1383337956489 := by decide +kernel

theorem rows22240R_2782 : rowsJ2 100 101 82 83 ≤ 1927239384386 := by decide +kernel

theorem rows22240R_2783 : rowsJ2 100 101 83 84 ≤ 2239491468922 := by decide +kernel

theorem rows22240R_2784 : rowsJ2 100 101 84 85 ≤ 2084056517665 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2771
#print axioms SieveCert.rows22240R_2784
