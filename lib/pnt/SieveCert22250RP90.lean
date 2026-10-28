/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 970–986 of 4715

File 90 of 351: the parts `rows22250R_970` … `rows22250R_986` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, work 93817 in units of a depth-4 test: row 62 columns 32–32, row 62 columns
33–33, row 62 columns 34–34, row 62 columns 35–35, row 62 columns 36–36, row 62 columns 37–37, row 62 columns 38–38,
row 62 columns 39–39, row 62 columns 40–40, row 62 columns 41–41, row 62 columns 42–42, row 62 columns 43–43, row 62
columns 44–44, row 62 columns 45–45, row 62 columns 46–46, row 62 columns 47–47, row 62 columns 48–48), each a sum
of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_970 : rowsJ2 62 63 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_971 : rowsJ2 62 63 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_972 : rowsJ2 62 63 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_973 : rowsJ2 62 63 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_974 : rowsJ2 62 63 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_975 : rowsJ2 62 63 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_976 : rowsJ2 62 63 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_977 : rowsJ2 62 63 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_978 : rowsJ2 62 63 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_979 : rowsJ2 62 63 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_980 : rowsJ2 62 63 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_981 : rowsJ2 62 63 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_982 : rowsJ2 62 63 44 45 ≤ 67672680620 := by decide +kernel

theorem rows22250R_983 : rowsJ2 62 63 45 46 ≤ 265615430271 := by decide +kernel

theorem rows22250R_984 : rowsJ2 62 63 46 47 ≤ 792423442439 := by decide +kernel

theorem rows22250R_985 : rowsJ2 62 63 47 48 ≤ 1573630038943 := by decide +kernel

theorem rows22250R_986 : rowsJ2 62 63 48 49 ≤ 2325273982159 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_970
#print axioms SieveCert.rows22250R_986
