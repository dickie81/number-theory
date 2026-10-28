/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4307–4320 of 5066

File 339 of 387: the parts `rows22240R_4307` … `rows22240R_4320` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 97029 in units of a depth-4 test: row 150 columns 75–339, row 151
columns 0–42, row 151 columns 43–46, row 151 columns 47–48, row 151 columns 49–49, row 151 columns 50–50, row 151
columns 51–51, row 151 columns 52–52, row 151 columns 53–53, row 151 columns 54–54, row 151 columns 55–55, row 151
columns 56–56, row 151 columns 57–57, row 151 columns 58–58), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_4307 : rowsJ2 150 151 75 340 ≤ 1909283416620346 := by decide +kernel

theorem rows22240R_4308 : rowsJ2 151 152 0 43 ≤ 3324298377728 := by decide +kernel

theorem rows22240R_4309 : rowsJ2 151 152 43 47 ≤ 11539045848141 := by decide +kernel

theorem rows22240R_4310 : rowsJ2 151 152 47 49 ≤ 10257297915095 := by decide +kernel

theorem rows22240R_4311 : rowsJ2 151 152 49 50 ≤ 6459302857064 := by decide +kernel

theorem rows22240R_4312 : rowsJ2 151 152 50 51 ≤ 7418949677507 := by decide +kernel

theorem rows22240R_4313 : rowsJ2 151 152 51 52 ≤ 8430264788638 := by decide +kernel

theorem rows22240R_4314 : rowsJ2 151 152 52 53 ≤ 9491245329667 := by decide +kernel

theorem rows22240R_4315 : rowsJ2 151 152 53 54 ≤ 10600039553129 := by decide +kernel

theorem rows22240R_4316 : rowsJ2 151 152 54 55 ≤ 11754952513886 := by decide +kernel

theorem rows22240R_4317 : rowsJ2 151 152 55 56 ≤ 12954430848907 := by decide +kernel

theorem rows22240R_4318 : rowsJ2 151 152 56 57 ≤ 14197039364869 := by decide +kernel

theorem rows22240R_4319 : rowsJ2 151 152 57 58 ≤ 15481457215975 := by decide +kernel

theorem rows22240R_4320 : rowsJ2 151 152 58 59 ≤ 15333673458815 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4307
#print axioms SieveCert.rows22240R_4320
