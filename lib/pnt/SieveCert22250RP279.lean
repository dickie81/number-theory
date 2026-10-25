/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3114–3126 of 5796

File 279 of 465: the parts `rows22250R_3114` … `rows22250R_3126` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 96946 tests: row 105 columns 85–85, row 105 columns 86–86, row 105 columns
87–87, row 105 columns 88–88, row 105 columns 89–89, row 105 columns 90–90, row 105 columns 91–91, row 105 columns
92–92, row 105 columns 93–93, row 105 columns 94–94, row 105 columns 95–95, row 105 columns 96–96, row 105 columns
97–97), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3114 : rowsJ2 105 106 85 86 ≤ 1094843228089 := by decide +kernel

theorem rows22250R_3115 : rowsJ2 105 106 86 87 ≤ 1466725661935 := by decide +kernel

theorem rows22250R_3116 : rowsJ2 105 106 87 88 ≤ 1884225680852 := by decide +kernel

theorem rows22250R_3117 : rowsJ2 105 106 88 89 ≤ 2046736338172 := by decide +kernel

theorem rows22250R_3118 : rowsJ2 105 106 89 90 ≤ 1904432656502 := by decide +kernel

theorem rows22250R_3119 : rowsJ2 105 106 90 91 ≤ 1772604415157 := by decide +kernel

theorem rows22250R_3120 : rowsJ2 105 106 91 92 ≤ 1701441216806 := by decide +kernel

theorem rows22250R_3121 : rowsJ2 105 106 92 93 ≤ 1705538387049 := by decide +kernel

theorem rows22250R_3122 : rowsJ2 105 106 93 94 ≤ 1774300173884 := by decide +kernel

theorem rows22250R_3123 : rowsJ2 105 106 94 95 ≤ 1921590545095 := by decide +kernel

theorem rows22250R_3124 : rowsJ2 105 106 95 96 ≤ 2100500267123 := by decide +kernel

theorem rows22250R_3125 : rowsJ2 105 106 96 97 ≤ 2360218432595 := by decide +kernel

theorem rows22250R_3126 : rowsJ2 105 106 97 98 ≤ 2654197058377 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3114
#print axioms SieveCert.rows22250R_3126
