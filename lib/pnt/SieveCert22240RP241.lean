/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2866–2881 of 5066

File 241 of 387: the parts `rows22240R_2866` … `rows22240R_2881` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 95690 in units of a depth-4 test: row 102 columns 55–59, row 102
columns 60–66, row 102 columns 67–72, row 102 columns 73–76, row 102 columns 77–78, row 102 columns 79–79, row 102
columns 80–80, row 102 columns 81–81, row 102 columns 82–82, row 102 columns 83–83, row 102 columns 84–84, row 102
columns 85–85, row 102 columns 86–86, row 102 columns 87–87, row 102 columns 88–88, row 102 columns 89–89), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2866 : rowsJ2 102 103 55 60 ≤ 90656939499 := by decide +kernel

theorem rows22240R_2867 : rowsJ2 102 103 60 67 ≤ 0 := by decide +kernel

theorem rows22240R_2868 : rowsJ2 102 103 67 73 ≤ 0 := by decide +kernel

theorem rows22240R_2869 : rowsJ2 102 103 73 77 ≤ 57032754100 := by decide +kernel

theorem rows22240R_2870 : rowsJ2 102 103 77 79 ≤ 524057337490 := by decide +kernel

theorem rows22240R_2871 : rowsJ2 102 103 79 80 ≤ 592787149416 := by decide +kernel

theorem rows22240R_2872 : rowsJ2 102 103 80 81 ≤ 902639555496 := by decide +kernel

theorem rows22240R_2873 : rowsJ2 102 103 81 82 ≤ 1269112394801 := by decide +kernel

theorem rows22240R_2874 : rowsJ2 102 103 82 83 ≤ 1707820020463 := by decide +kernel

theorem rows22240R_2875 : rowsJ2 102 103 83 84 ≤ 1564931127551 := by decide +kernel

theorem rows22240R_2876 : rowsJ2 102 103 84 85 ≤ 1475026257558 := by decide +kernel

theorem rows22240R_2877 : rowsJ2 102 103 85 86 ≤ 1464277408466 := by decide +kernel

theorem rows22240R_2878 : rowsJ2 102 103 86 87 ≤ 1550068322088 := by decide +kernel

theorem rows22240R_2879 : rowsJ2 102 103 87 88 ≤ 1719144575902 := by decide +kernel

theorem rows22240R_2880 : rowsJ2 102 103 88 89 ≤ 1944830767186 := by decide +kernel

theorem rows22240R_2881 : rowsJ2 102 103 89 90 ≤ 2256489106866 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2866
#print axioms SieveCert.rows22240R_2881
