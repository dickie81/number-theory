/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3177–3192 of 5066

File 260 of 387: the parts `rows22240R_3177` … `rows22240R_3192` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 96879 in units of a depth-4 test: row 110 columns 52–60, row 110
columns 61–65, row 110 columns 66–70, row 110 columns 71–74, row 110 columns 75–77, row 110 columns 78–79, row 110
columns 80–81, row 110 columns 82–84, row 110 columns 85–86, row 110 columns 87–88, row 110 columns 89–90, row 110
columns 91–92, row 110 columns 93–93, row 110 columns 94–94, row 110 columns 95–95, row 110 columns 96–96), each a
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

theorem rows22240R_3177 : rowsJ2 110 111 52 61 ≤ 367151669021 := by decide +kernel

theorem rows22240R_3178 : rowsJ2 110 111 61 66 ≤ 2269601638199 := by decide +kernel

theorem rows22240R_3179 : rowsJ2 110 111 66 71 ≤ 234210174195 := by decide +kernel

theorem rows22240R_3180 : rowsJ2 110 111 71 75 ≤ 0 := by decide +kernel

theorem rows22240R_3181 : rowsJ2 110 111 75 78 ≤ 211065163678 := by decide +kernel

theorem rows22240R_3182 : rowsJ2 110 111 78 80 ≤ 595696610142 := by decide +kernel

theorem rows22240R_3183 : rowsJ2 110 111 80 82 ≤ 467576501515 := by decide +kernel

theorem rows22240R_3184 : rowsJ2 110 111 82 85 ≤ 1674638740075 := by decide +kernel

theorem rows22240R_3185 : rowsJ2 110 111 85 87 ≤ 2673664171046 := by decide +kernel

theorem rows22240R_3186 : rowsJ2 110 111 87 89 ≤ 4676066259741 := by decide +kernel

theorem rows22240R_3187 : rowsJ2 110 111 89 91 ≤ 7350349114703 := by decide +kernel

theorem rows22240R_3188 : rowsJ2 110 111 91 93 ≤ 10687483988474 := by decide +kernel

theorem rows22240R_3189 : rowsJ2 110 111 93 94 ≤ 6819311859783 := by decide +kernel

theorem rows22240R_3190 : rowsJ2 110 111 94 95 ≤ 7907240551238 := by decide +kernel

theorem rows22240R_3191 : rowsJ2 110 111 95 96 ≤ 9116058308214 := by decide +kernel

theorem rows22240R_3192 : rowsJ2 110 111 96 97 ≤ 10396531460409 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3177
#print axioms SieveCert.rows22240R_3192
