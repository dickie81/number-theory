/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 690–699 of 1136

File 70 of 114: the parts `rows22000E_690` … `rows22000E_699` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 241 s of the kernel: row 137 columns 99–107, row 137 columns
108–125, row 137 columns 126–271, row 138 columns 0–47, row 138 columns 48–61, row 138 columns 62–72, row 138
columns 73–98, row 138 columns 99–107, row 138 columns 108–124, row 138 columns 125–271), each a sum of the costs
(`rowsJD`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_690 : rowsJD 137 138 99 108 ≤ 349391360343432 := by decide +kernel

theorem rows22000E_691 : rowsJD 137 138 108 126 ≤ 1379229600181500 := by decide +kernel

theorem rows22000E_692 : rowsJD 137 138 126 272 ≤ 725108155776240 := by decide +kernel

theorem rows22000E_693 : rowsJD 138 139 0 48 ≤ 83777054405005 := by decide +kernel

theorem rows22000E_694 : rowsJD 138 139 48 62 ≤ 37884615391636 := by decide +kernel

theorem rows22000E_695 : rowsJD 138 139 62 73 ≤ 119510297734210 := by decide +kernel

theorem rows22000E_696 : rowsJD 138 139 73 99 ≤ 209902809472585 := by decide +kernel

theorem rows22000E_697 : rowsJD 138 139 99 108 ≤ 331318501597940 := by decide +kernel

theorem rows22000E_698 : rowsJD 138 139 108 125 ≤ 1253763601677754 := by decide +kernel

theorem rows22000E_699 : rowsJD 138 139 125 272 ≤ 725401145434897 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_690
#print axioms SieveDeep.rows22000E_699
