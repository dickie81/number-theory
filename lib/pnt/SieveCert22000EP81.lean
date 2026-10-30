/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 800–809 of 1136

File 81 of 114: the parts `rows22000E_800` … `rows22000E_809` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 261 s of the kernel: row 152 columns 103–107, row 152 columns
108–113, row 152 columns 114–271, row 153 columns 0–45, row 153 columns 46–57, row 153 columns 58–87, row 153
columns 88–95, row 153 columns 96–101, row 153 columns 102–106, row 153 columns 107–111), each a sum of the costs
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

theorem rows22000E_800 : rowsJD 152 153 103 108 ≤ 392065872178843 := by decide +kernel

theorem rows22000E_801 : rowsJD 152 153 108 114 ≤ 413995268092618 := by decide +kernel

theorem rows22000E_802 : rowsJD 152 153 114 272 ≤ 1992461225689451 := by decide +kernel

theorem rows22000E_803 : rowsJD 153 154 0 46 ≤ 35974790018074 := by decide +kernel

theorem rows22000E_804 : rowsJD 153 154 46 58 ≤ 18504093751475 := by decide +kernel

theorem rows22000E_805 : rowsJD 153 154 58 88 ≤ 312041171761741 := by decide +kernel

theorem rows22000E_806 : rowsJD 153 154 88 96 ≤ 427351224904143 := by decide +kernel

theorem rows22000E_807 : rowsJD 153 154 96 102 ≤ 472098654838604 := by decide +kernel

theorem rows22000E_808 : rowsJD 153 154 102 107 ≤ 407585747243070 := by decide +kernel

theorem rows22000E_809 : rowsJD 153 154 107 112 ≤ 352433878419596 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_800
#print axioms SieveDeep.rows22000E_809
