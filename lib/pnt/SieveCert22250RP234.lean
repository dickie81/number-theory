/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2547–2559 of 5796

File 234 of 465: the parts `rows22250R_2547` … `rows22250R_2559` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 97363 tests: row 93 columns 93–359, row 94 columns 0–16, row 94 columns
17–19, row 94 columns 20–22, row 94 columns 23–26, row 94 columns 27–32, row 94 columns 33–36, row 94 columns 37–38,
row 94 columns 39–40, row 94 columns 41–41, row 94 columns 42–42, row 94 columns 43–43, row 94 columns 44–44), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2547 : rowsJ2 93 94 93 360 ≤ 7753033237650 := by decide +kernel

theorem rows22250R_2548 : rowsJ2 94 95 0 17 ≤ 0 := by decide +kernel

theorem rows22250R_2549 : rowsJ2 94 95 17 20 ≤ 0 := by decide +kernel

theorem rows22250R_2550 : rowsJ2 94 95 20 23 ≤ 0 := by decide +kernel

theorem rows22250R_2551 : rowsJ2 94 95 23 27 ≤ 0 := by decide +kernel

theorem rows22250R_2552 : rowsJ2 94 95 27 33 ≤ 0 := by decide +kernel

theorem rows22250R_2553 : rowsJ2 94 95 33 37 ≤ 3157676449859 := by decide +kernel

theorem rows22250R_2554 : rowsJ2 94 95 37 39 ≤ 6346522835857 := by decide +kernel

theorem rows22250R_2555 : rowsJ2 94 95 39 41 ≤ 10758925214856 := by decide +kernel

theorem rows22250R_2556 : rowsJ2 94 95 41 42 ≤ 6932039223364 := by decide +kernel

theorem rows22250R_2557 : rowsJ2 94 95 42 43 ≤ 8099857595759 := by decide +kernel

theorem rows22250R_2558 : rowsJ2 94 95 43 44 ≤ 9279562526979 := by decide +kernel

theorem rows22250R_2559 : rowsJ2 94 95 44 45 ≤ 10468947806549 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2547
#print axioms SieveCert.rows22250R_2559
