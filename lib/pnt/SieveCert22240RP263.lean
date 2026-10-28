/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3224–3237 of 5066

File 263 of 387: the parts `rows22240R_3224` … `rows22240R_3237` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 95436 in units of a depth-4 test: row 111 columns 99–339, row 112
columns 0–25, row 112 columns 26–30, row 112 columns 31–32, row 112 columns 33–34, row 112 columns 35–35, row 112
columns 36–37, row 112 columns 38–39, row 112 columns 40–41, row 112 columns 42–44, row 112 columns 45–49, row 112
columns 50–59, row 112 columns 60–64, row 112 columns 65–68), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_3224 : rowsJ2 111 112 99 340 ≤ 1279314326328238 := by decide +kernel

theorem rows22240R_3225 : rowsJ2 112 113 0 26 ≤ 0 := by decide +kernel

theorem rows22240R_3226 : rowsJ2 112 113 26 31 ≤ 8746041096328 := by decide +kernel

theorem rows22240R_3227 : rowsJ2 112 113 31 33 ≤ 12247779484991 := by decide +kernel

theorem rows22240R_3228 : rowsJ2 112 113 33 35 ≤ 19876237248434 := by decide +kernel

theorem rows22240R_3229 : rowsJ2 112 113 35 36 ≤ 13772890633529 := by decide +kernel

theorem rows22240R_3230 : rowsJ2 112 113 36 38 ≤ 24107344898881 := by decide +kernel

theorem rows22240R_3231 : rowsJ2 112 113 38 40 ≤ 17601082236728 := by decide +kernel

theorem rows22240R_3232 : rowsJ2 112 113 40 42 ≤ 11491806174562 := by decide +kernel

theorem rows22240R_3233 : rowsJ2 112 113 42 45 ≤ 9326492067355 := by decide +kernel

theorem rows22240R_3234 : rowsJ2 112 113 45 50 ≤ 3006491216278 := by decide +kernel

theorem rows22240R_3235 : rowsJ2 112 113 50 60 ≤ 376418438507 := by decide +kernel

theorem rows22240R_3236 : rowsJ2 112 113 60 65 ≤ 3560707832117 := by decide +kernel

theorem rows22240R_3237 : rowsJ2 112 113 65 69 ≤ 2438206510590 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3224
#print axioms SieveCert.rows22240R_3237
