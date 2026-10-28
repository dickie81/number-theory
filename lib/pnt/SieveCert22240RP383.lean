/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4990–5004 of 5066

File 383 of 387: the parts `rows22240R_4990` … `rows22240R_5004` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 97456 in units of a depth-4 test: row 191 columns 37–339, row 192
columns 0–30, row 192 columns 31–33, row 192 columns 34–35, row 192 columns 36–339, row 193 columns 0–30, row 193
columns 31–32, row 193 columns 33–34, row 193 columns 35–339, row 194 columns 0–29, row 194 columns 30–32, row 194
columns 33–95, row 194 columns 96–339, row 195 columns 0–29, row 195 columns 30–32), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4990 : rowsJ2 191 192 37 340 ≤ 4608242698533150 := by decide +kernel

theorem rows22240R_4991 : rowsJ2 192 193 0 31 ≤ 26479879447765 := by decide +kernel

theorem rows22240R_4992 : rowsJ2 192 193 31 34 ≤ 46338709336284 := by decide +kernel

theorem rows22240R_4993 : rowsJ2 192 193 34 36 ≤ 50411175231319 := by decide +kernel

theorem rows22240R_4994 : rowsJ2 192 193 36 340 ≤ 4732433318352260 := by decide +kernel

theorem rows22240R_4995 : rowsJ2 193 194 0 31 ≤ 30626836859868 := by decide +kernel

theorem rows22240R_4996 : rowsJ2 193 194 31 33 ≤ 30031368825268 := by decide +kernel

theorem rows22240R_4997 : rowsJ2 193 194 33 35 ≤ 45315994111589 := by decide +kernel

theorem rows22240R_4998 : rowsJ2 193 194 35 340 ≤ 4855598628770745 := by decide +kernel

theorem rows22240R_4999 : rowsJ2 194 195 0 30 ≤ 23816184989225 := by decide +kernel

theorem rows22240R_5000 : rowsJ2 194 195 30 33 ≤ 44259705342997 := by decide +kernel

theorem rows22240R_5001 : rowsJ2 194 195 33 96 ≤ 1659751270596212 := by decide +kernel

theorem rows22240R_5002 : rowsJ2 194 195 96 340 ≤ 3340275772781680 := by decide +kernel

theorem rows22240R_5003 : rowsJ2 195 196 0 30 ≤ 27689581714894 := by decide +kernel

theorem rows22240R_5004 : rowsJ2 195 196 30 33 ≤ 48471167075931 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4990
#print axioms SieveCert.rows22240R_5004
