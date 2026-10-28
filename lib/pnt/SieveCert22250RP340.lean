/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4529–4546 of 4715

File 340 of 351: the parts `rows22250R_4529` … `rows22250R_4546` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (18 parts, work 95462 in units of a depth-4 test: row 179 columns 39–39, row 179
columns 40–40, row 179 columns 41–41, row 179 columns 42–42, row 179 columns 43–43, row 179 columns 44–44, row 179
columns 45–45, row 179 columns 46–46, row 179 columns 47–99, row 179 columns 100–339, row 180 columns 0–33, row 180
columns 34–35, row 180 columns 36–37, row 180 columns 38–38, row 180 columns 39–39, row 180 columns 40–40, row 180
columns 41–41, row 180 columns 42–42), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4529 : rowsJ2 179 180 39 40 ≤ 19602351656097 := by decide +kernel

theorem rows22250R_4530 : rowsJ2 179 180 40 41 ≤ 21629632370980 := by decide +kernel

theorem rows22250R_4531 : rowsJ2 179 180 41 42 ≤ 23729728813505 := by decide +kernel

theorem rows22250R_4532 : rowsJ2 179 180 42 43 ≤ 25900865802955 := by decide +kernel

theorem rows22250R_4533 : rowsJ2 179 180 43 44 ≤ 25613181161065 := by decide +kernel

theorem rows22250R_4534 : rowsJ2 179 180 44 45 ≤ 22947706316659 := by decide +kernel

theorem rows22250R_4535 : rowsJ2 179 180 45 46 ≤ 20454519477789 := by decide +kernel

theorem rows22250R_4536 : rowsJ2 179 180 46 47 ≤ 18127415659636 := by decide +kernel

theorem rows22250R_4537 : rowsJ2 179 180 47 100 ≤ 594534667441069 := by decide +kernel

theorem rows22250R_4538 : rowsJ2 179 180 100 340 ≤ 2474301155506031 := by decide +kernel

theorem rows22250R_4539 : rowsJ2 180 181 0 34 ≤ 19900850919612 := by decide +kernel

theorem rows22250R_4540 : rowsJ2 180 181 34 36 ≤ 21756392784514 := by decide +kernel

theorem rows22250R_4541 : rowsJ2 180 181 36 38 ≤ 32250011322262 := by decide +kernel

theorem rows22250R_4542 : rowsJ2 180 181 38 39 ≤ 19019490151772 := by decide +kernel

theorem rows22250R_4543 : rowsJ2 180 181 39 40 ≤ 21053634241488 := by decide +kernel

theorem rows22250R_4544 : rowsJ2 180 181 40 41 ≤ 23163150213166 := by decide +kernel

theorem rows22250R_4545 : rowsJ2 180 181 41 42 ≤ 25346077511185 := by decide +kernel

theorem rows22250R_4546 : rowsJ2 180 181 42 43 ≤ 27600800782125 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4529
#print axioms SieveCert.rows22250R_4546
