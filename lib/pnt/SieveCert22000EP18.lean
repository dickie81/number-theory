/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 170–179 of 1136

File 18 of 114: the parts `rows22000E_170` … `rows22000E_179` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 257 s of the kernel: row 74 columns 72–271, row 75 columns 0–36,
row 75 columns 37–47, row 75 columns 48–54, row 75 columns 55–60, row 75 columns 61–67, row 75 columns 68–73, row 75
columns 74–271, row 76 columns 0–36, row 76 columns 37–48), each a sum of the costs (`rowsJD`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22000E.lean`.
-/
import SieveGrid22000E

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveDeep

open SieveCert

section

attribute [local instance] grid22000E ibPar22000E

theorem rows22000E_170 : rowsJD 74 75 72 272 ≤ 52125099387544 := by decide +kernel

theorem rows22000E_171 : rowsJD 75 76 0 37 ≤ 234820028308888 := by decide +kernel

theorem rows22000E_172 : rowsJD 75 76 37 48 ≤ 162705491506304 := by decide +kernel

theorem rows22000E_173 : rowsJD 75 76 48 55 ≤ 85609525614186 := by decide +kernel

theorem rows22000E_174 : rowsJD 75 76 55 61 ≤ 75434211954909 := by decide +kernel

theorem rows22000E_175 : rowsJD 75 76 61 68 ≤ 82999181528451 := by decide +kernel

theorem rows22000E_176 : rowsJD 75 76 68 74 ≤ 85621670516637 := by decide +kernel

theorem rows22000E_177 : rowsJD 75 76 74 272 ≤ 36344387669712 := by decide +kernel

theorem rows22000E_178 : rowsJD 76 77 0 37 ≤ 231704546451265 := by decide +kernel

theorem rows22000E_179 : rowsJD 76 77 37 49 ≤ 168446458316581 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_170
#print axioms SieveDeep.rows22000E_179
