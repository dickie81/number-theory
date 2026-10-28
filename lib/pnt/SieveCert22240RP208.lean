/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2406–2420 of 5066

File 208 of 387: the parts `rows22240R_2406` … `rows22240R_2420` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 93627 in units of a depth-4 test: row 92 columns 47–47, row 92 columns
48–48, row 92 columns 49–49, row 92 columns 50–50, row 92 columns 51–51, row 92 columns 52–52, row 92 columns 53–53,
row 92 columns 54–54, row 92 columns 55–55, row 92 columns 56–57, row 92 columns 58–59, row 92 columns 60–61, row 92
columns 62–64, row 92 columns 65–68, row 92 columns 69–73), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_2406 : rowsJ2 92 93 47 48 ≤ 13290291132562 := by decide +kernel

theorem rows22240R_2407 : rowsJ2 92 93 48 49 ≤ 11684329519778 := by decide +kernel

theorem rows22240R_2408 : rowsJ2 92 93 49 50 ≤ 10189216755745 := by decide +kernel

theorem rows22240R_2409 : rowsJ2 92 93 50 51 ≤ 6939759128440 := by decide +kernel

theorem rows22240R_2410 : rowsJ2 92 93 51 52 ≤ 4023021231710 := by decide +kernel

theorem rows22240R_2411 : rowsJ2 92 93 52 53 ≤ 1858338330354 := by decide +kernel

theorem rows22240R_2412 : rowsJ2 92 93 53 54 ≤ 0 := by decide +kernel

theorem rows22240R_2413 : rowsJ2 92 93 54 55 ≤ 0 := by decide +kernel

theorem rows22240R_2414 : rowsJ2 92 93 55 56 ≤ 0 := by decide +kernel

theorem rows22240R_2415 : rowsJ2 92 93 56 58 ≤ 0 := by decide +kernel

theorem rows22240R_2416 : rowsJ2 92 93 58 60 ≤ 0 := by decide +kernel

theorem rows22240R_2417 : rowsJ2 92 93 60 62 ≤ 0 := by decide +kernel

theorem rows22240R_2418 : rowsJ2 92 93 62 65 ≤ 0 := by decide +kernel

theorem rows22240R_2419 : rowsJ2 92 93 65 69 ≤ 0 := by decide +kernel

theorem rows22240R_2420 : rowsJ2 92 93 69 74 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2406
#print axioms SieveCert.rows22240R_2420
