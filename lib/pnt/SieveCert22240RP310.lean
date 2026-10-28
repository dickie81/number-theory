/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3920–3930 of 5066

File 310 of 387: the parts `rows22240R_3920` … `rows22240R_3930` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 95460 in units of a depth-4 test: row 136 columns 62–62, row 136
columns 63–63, row 136 columns 64–64, row 136 columns 65–65, row 136 columns 66–66, row 136 columns 67–67, row 136
columns 68–68, row 136 columns 69–69, row 136 columns 70–70, row 136 columns 71–71, row 136 columns 72–72), each a
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

theorem rows22240R_3920 : rowsJ2 136 137 62 63 ≤ 9578173100031 := by decide +kernel

theorem rows22240R_3921 : rowsJ2 136 137 63 64 ≤ 10341079493544 := by decide +kernel

theorem rows22240R_3922 : rowsJ2 136 137 64 65 ≤ 11058610536305 := by decide +kernel

theorem rows22240R_3923 : rowsJ2 136 137 65 66 ≤ 11709503826260 := by decide +kernel

theorem rows22240R_3924 : rowsJ2 136 137 66 67 ≤ 10604332111742 := by decide +kernel

theorem rows22240R_3925 : rowsJ2 136 137 67 68 ≤ 9552328759220 := by decide +kernel

theorem rows22240R_3926 : rowsJ2 136 137 68 69 ≤ 8572734176614 := by decide +kernel

theorem rows22240R_3927 : rowsJ2 136 137 69 70 ≤ 7642341969979 := by decide +kernel

theorem rows22240R_3928 : rowsJ2 136 137 70 71 ≤ 6780864288944 := by decide +kernel

theorem rows22240R_3929 : rowsJ2 136 137 71 72 ≤ 5965017540254 := by decide +kernel

theorem rows22240R_3930 : rowsJ2 136 137 72 73 ≤ 5214971365936 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3920
#print axioms SieveCert.rows22240R_3930
