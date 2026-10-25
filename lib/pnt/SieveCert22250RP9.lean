/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 131–147 of 5796

File 9 of 465: the parts `rows22250R_131` … `rows22250R_147` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 98439 tests: row 31 columns 14–16, row 31 columns 17–18, row 31 columns
19–19, row 31 columns 20–20, row 31 columns 21–21, row 31 columns 22–22, row 31 columns 23–23, row 31 columns 24–24,
row 31 columns 25–25, row 31 columns 26–26, row 31 columns 27–27, row 31 columns 28–28, row 31 columns 29–29, row 31
columns 30–30, row 31 columns 31–359, row 32 columns 0–13, row 32 columns 14–16), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_131 : rowsJ2 31 32 14 17 ≤ 964216750600 := by decide +kernel

theorem rows22250R_132 : rowsJ2 31 32 17 19 ≤ 1477317449049 := by decide +kernel

theorem rows22250R_133 : rowsJ2 31 32 19 20 ≤ 967992988621 := by decide +kernel

theorem rows22250R_134 : rowsJ2 31 32 20 21 ≤ 1090541103281 := by decide +kernel

theorem rows22250R_135 : rowsJ2 31 32 21 22 ≤ 1176380607309 := by decide +kernel

theorem rows22250R_136 : rowsJ2 31 32 22 23 ≤ 1216637113400 := by decide +kernel

theorem rows22250R_137 : rowsJ2 31 32 23 24 ≤ 1241590543896 := by decide +kernel

theorem rows22250R_138 : rowsJ2 31 32 24 25 ≤ 1248485542711 := by decide +kernel

theorem rows22250R_139 : rowsJ2 31 32 25 26 ≤ 1237979796141 := by decide +kernel

theorem rows22250R_140 : rowsJ2 31 32 26 27 ≤ 1197586300894 := by decide +kernel

theorem rows22250R_141 : rowsJ2 31 32 27 28 ≤ 1146925365188 := by decide +kernel

theorem rows22250R_142 : rowsJ2 31 32 28 29 ≤ 1086671938917 := by decide +kernel

theorem rows22250R_143 : rowsJ2 31 32 29 30 ≤ 1022670618892 := by decide +kernel

theorem rows22250R_144 : rowsJ2 31 32 30 31 ≤ 951189949729 := by decide +kernel

theorem rows22250R_145 : rowsJ2 31 32 31 360 ≤ 887226423302 := by decide +kernel

theorem rows22250R_146 : rowsJ2 32 33 0 14 ≤ 475452420138 := by decide +kernel

theorem rows22250R_147 : rowsJ2 32 33 14 17 ≤ 1048767792348 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_131
#print axioms SieveCert.rows22250R_147
