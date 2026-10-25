/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4148–4163 of 4715

File 316 of 351: the parts `rows22250R_4148` … `rows22250R_4163` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 94630 tests: row 157 columns 58–58, row 157 columns 59–59, row 157 columns
60–60, row 157 columns 61–62, row 157 columns 63–64, row 157 columns 65–68, row 157 columns 69–339, row 158 columns
0–40, row 158 columns 41–43, row 158 columns 44–45, row 158 columns 46–46, row 158 columns 47–47, row 158 columns
48–48, row 158 columns 49–49, row 158 columns 50–50, row 158 columns 51–51), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4148 : rowsJ2 157 158 58 59 ≤ 10323850399766 := by decide +kernel

theorem rows22250R_4149 : rowsJ2 157 158 59 60 ≤ 9031364894923 := by decide +kernel

theorem rows22250R_4150 : rowsJ2 157 158 60 61 ≤ 7833042411022 := by decide +kernel

theorem rows22250R_4151 : rowsJ2 157 158 61 63 ≤ 12436758962274 := by decide +kernel

theorem rows22250R_4152 : rowsJ2 157 158 63 65 ≤ 8720911171052 := by decide +kernel

theorem rows22250R_4153 : rowsJ2 157 158 65 69 ≤ 9010010470493 := by decide +kernel

theorem rows22250R_4154 : rowsJ2 157 158 69 340 ≤ 2638544157964453 := by decide +kernel

theorem rows22250R_4155 : rowsJ2 158 159 0 41 ≤ 8707634590597 := by decide +kernel

theorem rows22250R_4156 : rowsJ2 158 159 41 44 ≤ 13550870667910 := by decide +kernel

theorem rows22250R_4157 : rowsJ2 158 159 44 46 ≤ 13775311448409 := by decide +kernel

theorem rows22250R_4158 : rowsJ2 158 159 46 47 ≤ 8500840651175 := by decide +kernel

theorem rows22250R_4159 : rowsJ2 158 159 47 48 ≤ 9654669231265 := by decide +kernel

theorem rows22250R_4160 : rowsJ2 158 159 48 49 ≤ 10864318539837 := by decide +kernel

theorem rows22250R_4161 : rowsJ2 158 159 49 50 ≤ 12127683743852 := by decide +kernel

theorem rows22250R_4162 : rowsJ2 158 159 50 51 ≤ 13442864431653 := by decide +kernel

theorem rows22250R_4163 : rowsJ2 158 159 51 52 ≤ 14808154218161 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4148
#print axioms SieveCert.rows22250R_4163
