/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 840–849 of 1136

File 85 of 114: the parts `rows22000E_840` … `rows22000E_849` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 258 s of the kernel: row 157 columns 102–106, row 157 columns
107–111, row 157 columns 112–271, row 158 columns 0–44, row 158 columns 45–75, row 158 columns 76–87, row 158
columns 88–95, row 158 columns 96–101, row 158 columns 102–105, row 158 columns 106–109), each a sum of the costs
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

theorem rows22000E_840 : rowsJD 157 158 102 107 ≤ 499344423977228 := by decide +kernel

theorem rows22000E_841 : rowsJD 157 158 107 112 ≤ 431545061281711 := by decide +kernel

theorem rows22000E_842 : rowsJD 157 158 112 272 ≤ 2655496805416001 := by decide +kernel

theorem rows22000E_843 : rowsJD 158 159 0 45 ≤ 26970520087791 := by decide +kernel

theorem rows22000E_844 : rowsJD 158 159 45 76 ≤ 53359297231368 := by decide +kernel

theorem rows22000E_845 : rowsJD 158 159 76 88 ≤ 472807492728880 := by decide +kernel

theorem rows22000E_846 : rowsJD 158 159 88 96 ≤ 367842580266425 := by decide +kernel

theorem rows22000E_847 : rowsJD 158 159 96 102 ≤ 462525490715604 := by decide +kernel

theorem rows22000E_848 : rowsJD 158 159 102 106 ≤ 429579280167395 := by decide +kernel

theorem rows22000E_849 : rowsJD 158 159 106 110 ≤ 410864238408639 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_840
#print axioms SieveDeep.rows22000E_849
