/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2086–2098 of 4715

File 174 of 351: the parts `rows22250R_2086` … `rows22250R_2098` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 99250 in units of a depth-4 test: row 87 columns 62–63, row 87 columns
64–66, row 87 columns 67–70, row 87 columns 71–74, row 87 columns 75–77, row 87 columns 78–79, row 87 columns 80–80,
row 87 columns 81–81, row 87 columns 82–82, row 87 columns 83–83, row 87 columns 84–84, row 87 columns 85–85, row 87
columns 86–86), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2086 : rowsJ2 87 88 62 64 ≤ 0 := by decide +kernel

theorem rows22250R_2087 : rowsJ2 87 88 64 67 ≤ 0 := by decide +kernel

theorem rows22250R_2088 : rowsJ2 87 88 67 71 ≤ 0 := by decide +kernel

theorem rows22250R_2089 : rowsJ2 87 88 71 75 ≤ 0 := by decide +kernel

theorem rows22250R_2090 : rowsJ2 87 88 75 78 ≤ 389260602400 := by decide +kernel

theorem rows22250R_2091 : rowsJ2 87 88 78 80 ≤ 1328336674298 := by decide +kernel

theorem rows22250R_2092 : rowsJ2 87 88 80 81 ≤ 1205907493711 := by decide +kernel

theorem rows22250R_2093 : rowsJ2 87 88 81 82 ≤ 1669758240634 := by decide +kernel

theorem rows22250R_2094 : rowsJ2 87 88 82 83 ≤ 2267217349701 := by decide +kernel

theorem rows22250R_2095 : rowsJ2 87 88 83 84 ≤ 3021128117311 := by decide +kernel

theorem rows22250R_2096 : rowsJ2 87 88 84 85 ≤ 3924442748249 := by decide +kernel

theorem rows22250R_2097 : rowsJ2 87 88 85 86 ≤ 5005720403412 := by decide +kernel

theorem rows22250R_2098 : rowsJ2 87 88 86 87 ≤ 6259513939932 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2086
#print axioms SieveCert.rows22250R_2098
