/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2986–3000 of 5796

File 270 of 465: the parts `rows22250R_2986` … `rows22250R_3000` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 95848 tests: row 103 columns 0–16, row 103 columns 17–24, row 103 columns
25–32, row 103 columns 33–35, row 103 columns 36–37, row 103 columns 38–38, row 103 columns 39–39, row 103 columns
40–40, row 103 columns 41–41, row 103 columns 42–42, row 103 columns 43–43, row 103 columns 44–44, row 103 columns
45–45, row 103 columns 46–46, row 103 columns 47–47), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2986 : rowsJ2 103 104 0 17 ≤ 0 := by decide +kernel

theorem rows22250R_2987 : rowsJ2 103 104 17 25 ≤ 0 := by decide +kernel

theorem rows22250R_2988 : rowsJ2 103 104 25 33 ≤ 914099436309 := by decide +kernel

theorem rows22250R_2989 : rowsJ2 103 104 33 36 ≤ 6455392997512 := by decide +kernel

theorem rows22250R_2990 : rowsJ2 103 104 36 38 ≤ 9861680355810 := by decide +kernel

theorem rows22250R_2991 : rowsJ2 103 104 38 39 ≤ 6922312337943 := by decide +kernel

theorem rows22250R_2992 : rowsJ2 103 104 39 40 ≤ 8531430810487 := by decide +kernel

theorem rows22250R_2993 : rowsJ2 103 104 40 41 ≤ 9808233607911 := by decide +kernel

theorem rows22250R_2994 : rowsJ2 103 104 41 42 ≤ 11181045060062 := by decide +kernel

theorem rows22250R_2995 : rowsJ2 103 104 42 43 ≤ 12557434679948 := by decide +kernel

theorem rows22250R_2996 : rowsJ2 103 104 43 44 ≤ 13839806756708 := by decide +kernel

theorem rows22250R_2997 : rowsJ2 103 104 44 45 ≤ 13594942805716 := by decide +kernel

theorem rows22250R_2998 : rowsJ2 103 104 45 46 ≤ 12063225369734 := by decide +kernel

theorem rows22250R_2999 : rowsJ2 103 104 46 47 ≤ 10548514410675 := by decide +kernel

theorem rows22250R_3000 : rowsJ2 103 104 47 48 ≤ 9098951308051 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2986
#print axioms SieveCert.rows22250R_3000
