/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2058–2072 of 5796

File 197 of 465: the parts `rows22250R_2058` … `rows22250R_2072` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 94419 tests: row 83 columns 75–76, row 83 columns 77–78, row 83 columns
79–80, row 83 columns 81–82, row 83 columns 83–359, row 84 columns 0–17, row 84 columns 18–19, row 84 columns 20–21,
row 84 columns 22–22, row 84 columns 23–24, row 84 columns 25–26, row 84 columns 27–28, row 84 columns 29–30, row 84
columns 31–33, row 84 columns 34–36), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_2058 : rowsJ2 83 84 75 77 ≤ 0 := by decide +kernel

theorem rows22250R_2059 : rowsJ2 83 84 77 79 ≤ 0 := by decide +kernel

theorem rows22250R_2060 : rowsJ2 83 84 79 81 ≤ 57936706929 := by decide +kernel

theorem rows22250R_2061 : rowsJ2 83 84 81 83 ≤ 532652850664 := by decide +kernel

theorem rows22250R_2062 : rowsJ2 83 84 83 360 ≤ 1126435775681 := by decide +kernel

theorem rows22250R_2063 : rowsJ2 84 85 0 18 ≤ 89155062755 := by decide +kernel

theorem rows22250R_2064 : rowsJ2 84 85 18 20 ≤ 6495608139 := by decide +kernel

theorem rows22250R_2065 : rowsJ2 84 85 20 22 ≤ 10001681988 := by decide +kernel

theorem rows22250R_2066 : rowsJ2 84 85 22 23 ≤ 2844221991 := by decide +kernel

theorem rows22250R_2067 : rowsJ2 84 85 23 25 ≤ 2123241713 := by decide +kernel

theorem rows22250R_2068 : rowsJ2 84 85 25 27 ≤ 0 := by decide +kernel

theorem rows22250R_2069 : rowsJ2 84 85 27 29 ≤ 0 := by decide +kernel

theorem rows22250R_2070 : rowsJ2 84 85 29 31 ≤ 0 := by decide +kernel

theorem rows22250R_2071 : rowsJ2 84 85 31 34 ≤ 0 := by decide +kernel

theorem rows22250R_2072 : rowsJ2 84 85 34 37 ≤ 149742909641 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2058
#print axioms SieveCert.rows22250R_2072
