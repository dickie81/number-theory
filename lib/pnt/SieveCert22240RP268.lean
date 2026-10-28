/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3298–3313 of 5066

File 268 of 387: the parts `rows22240R_3298` … `rows22240R_3313` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 97932 in units of a depth-4 test: row 114 columns 87–88, row 114
columns 89–90, row 114 columns 91–92, row 114 columns 93–93, row 114 columns 94–94, row 114 columns 95–95, row 114
columns 96–96, row 114 columns 97–339, row 115 columns 0–26, row 115 columns 27–30, row 115 columns 31–32, row 115
columns 33–34, row 115 columns 35–36, row 115 columns 37–38, row 115 columns 39–41, row 115 columns 42–46), each a
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

theorem rows22240R_3298 : rowsJ2 114 115 87 89 ≤ 6503209268664 := by decide +kernel

theorem rows22240R_3299 : rowsJ2 114 115 89 91 ≤ 9807723485487 := by decide +kernel

theorem rows22240R_3300 : rowsJ2 114 115 91 93 ≤ 13849850648517 := by decide +kernel

theorem rows22240R_3301 : rowsJ2 114 115 93 94 ≤ 8691144932529 := by decide +kernel

theorem rows22240R_3302 : rowsJ2 114 115 94 95 ≤ 9987006162258 := by decide +kernel

theorem rows22240R_3303 : rowsJ2 114 115 95 96 ≤ 11417487196938 := by decide +kernel

theorem rows22240R_3304 : rowsJ2 114 115 96 97 ≤ 12931182680043 := by decide +kernel

theorem rows22240R_3305 : rowsJ2 114 115 97 340 ≤ 1709824286847392 := by decide +kernel

theorem rows22240R_3306 : rowsJ2 115 116 0 27 ≤ 943485643500 := by decide +kernel

theorem rows22240R_3307 : rowsJ2 115 116 27 31 ≤ 11542120459867 := by decide +kernel

theorem rows22240R_3308 : rowsJ2 115 116 31 33 ≤ 15215523113785 := by decide +kernel

theorem rows22240R_3309 : rowsJ2 115 116 33 35 ≤ 22717978555632 := by decide +kernel

theorem rows22240R_3310 : rowsJ2 115 116 35 37 ≤ 20095532543472 := by decide +kernel

theorem rows22240R_3311 : rowsJ2 115 116 37 39 ≤ 15277900692696 := by decide +kernel

theorem rows22240R_3312 : rowsJ2 115 116 39 42 ≤ 12383030621340 := by decide +kernel

theorem rows22240R_3313 : rowsJ2 115 116 42 47 ≤ 5408618809363 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3298
#print axioms SieveCert.rows22240R_3313
