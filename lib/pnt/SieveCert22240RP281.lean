/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3499–3514 of 5066

File 281 of 387: the parts `rows22240R_3499` … `rows22240R_3514` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 96150 in units of a depth-4 test: row 122 columns 38–46, row 122
columns 47–57, row 122 columns 58–60, row 122 columns 61–62, row 122 columns 63–63, row 122 columns 64–64, row 122
columns 65–65, row 122 columns 66–66, row 122 columns 67–67, row 122 columns 68–68, row 122 columns 69–69, row 122
columns 70–70, row 122 columns 71–71, row 122 columns 72–72, row 122 columns 73–73, row 122 columns 74–75), each a
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

theorem rows22240R_3499 : rowsJ2 122 123 38 47 ≤ 3626523461338 := by decide +kernel

theorem rows22240R_3500 : rowsJ2 122 123 47 58 ≤ 2694753331909 := by decide +kernel

theorem rows22240R_3501 : rowsJ2 122 123 58 61 ≤ 5460379547697 := by decide +kernel

theorem rows22240R_3502 : rowsJ2 122 123 61 63 ≤ 5852055267325 := by decide +kernel

theorem rows22240R_3503 : rowsJ2 122 123 63 64 ≤ 3480806419305 := by decide +kernel

theorem rows22240R_3504 : rowsJ2 122 123 64 65 ≤ 3777539117288 := by decide +kernel

theorem rows22240R_3505 : rowsJ2 122 123 65 66 ≤ 4001504615800 := by decide +kernel

theorem rows22240R_3506 : rowsJ2 122 123 66 67 ≤ 4174647842246 := by decide +kernel

theorem rows22240R_3507 : rowsJ2 122 123 67 68 ≤ 4273103308050 := by decide +kernel

theorem rows22240R_3508 : rowsJ2 122 123 68 69 ≤ 4318873696996 := by decide +kernel

theorem rows22240R_3509 : rowsJ2 122 123 69 70 ≤ 4287525414889 := by decide +kernel

theorem rows22240R_3510 : rowsJ2 122 123 70 71 ≤ 4200899557437 := by decide +kernel

theorem rows22240R_3511 : rowsJ2 122 123 71 72 ≤ 4033862027907 := by decide +kernel

theorem rows22240R_3512 : rowsJ2 122 123 72 73 ≤ 3808149327277 := by decide +kernel

theorem rows22240R_3513 : rowsJ2 122 123 73 74 ≤ 3110793860872 := by decide +kernel

theorem rows22240R_3514 : rowsJ2 122 123 74 76 ≤ 4358242845592 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3499
#print axioms SieveCert.rows22240R_3514
