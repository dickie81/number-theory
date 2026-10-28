/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 183–195 of 4715

File 13 of 351: the parts `rows22250R_183` … `rows22250R_195` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 93728 in units of a depth-4 test: row 34 columns 34–339, row 35 columns
0–13, row 35 columns 14–16, row 35 columns 17–18, row 35 columns 19–20, row 35 columns 21–22, row 35 columns 23–24,
row 35 columns 25–25, row 35 columns 26–26, row 35 columns 27–27, row 35 columns 28–28, row 35 columns 29–29, row 35
columns 30–30), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R
-- exclusive-heavy: a part of this file can use over 7 GiB; scripts/lean-slots.sh runs it alone among the parts

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_183 : rowsJ2 34 35 34 340 ≤ 872829374871 := by decide +kernel

theorem rows22250R_184 : rowsJ2 35 36 0 14 ≤ 804693858069 := by decide +kernel

theorem rows22250R_185 : rowsJ2 35 36 14 17 ≤ 2224663783459 := by decide +kernel

theorem rows22250R_186 : rowsJ2 35 36 17 19 ≤ 2182691011309 := by decide +kernel

theorem rows22250R_187 : rowsJ2 35 36 19 21 ≤ 2391795759396 := by decide +kernel

theorem rows22250R_188 : rowsJ2 35 36 21 23 ≤ 2343850232172 := by decide +kernel

theorem rows22250R_189 : rowsJ2 35 36 23 25 ≤ 2113413216891 := by decide +kernel

theorem rows22250R_190 : rowsJ2 35 36 25 26 ≤ 941461844374 := by decide +kernel

theorem rows22250R_191 : rowsJ2 35 36 26 27 ≤ 863012042325 := by decide +kernel

theorem rows22250R_192 : rowsJ2 35 36 27 28 ≤ 787850621080 := by decide +kernel

theorem rows22250R_193 : rowsJ2 35 36 28 29 ≤ 733899808276 := by decide +kernel

theorem rows22250R_194 : rowsJ2 35 36 29 30 ≤ 690705827845 := by decide +kernel

theorem rows22250R_195 : rowsJ2 35 36 30 31 ≤ 676571348004 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_183
#print axioms SieveCert.rows22250R_195
