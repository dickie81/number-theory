/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3004–3018 of 4715

File 237 of 351: the parts `rows22250R_3004` … `rows22250R_3018` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 94578 in units of a depth-4 test: row 111 columns 91–92, row 111
columns 93–94, row 111 columns 95–95, row 111 columns 96–96, row 111 columns 97–97, row 111 columns 98–339, row 112
columns 0–26, row 112 columns 27–30, row 112 columns 31–32, row 112 columns 33–34, row 112 columns 35–36, row 112
columns 37–38, row 112 columns 39–41, row 112 columns 42–46, row 112 columns 47–58), each a sum of refined costs
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

theorem rows22250R_3004 : rowsJ2 111 112 91 93 ≤ 10531464559860 := by decide +kernel

theorem rows22250R_3005 : rowsJ2 111 112 93 95 ≤ 14675723597972 := by decide +kernel

theorem rows22250R_3006 : rowsJ2 111 112 95 96 ≤ 9129451937243 := by decide +kernel

theorem rows22250R_3007 : rowsJ2 111 112 96 97 ≤ 10479362468874 := by decide +kernel

theorem rows22250R_3008 : rowsJ2 111 112 97 98 ≤ 11908944514876 := by decide +kernel

theorem rows22250R_3009 : rowsJ2 111 112 98 340 ≤ 1383003969706183 := by decide +kernel

theorem rows22250R_3010 : rowsJ2 112 113 0 27 ≤ 944055281285 := by decide +kernel

theorem rows22250R_3011 : rowsJ2 112 113 27 31 ≤ 11553228861341 := by decide +kernel

theorem rows22250R_3012 : rowsJ2 112 113 31 33 ≤ 15232944549292 := by decide +kernel

theorem rows22250R_3013 : rowsJ2 112 113 33 35 ≤ 22745467754741 := by decide +kernel

theorem rows22250R_3014 : rowsJ2 112 113 35 37 ≤ 20118119596936 := by decide +kernel

theorem rows22250R_3015 : rowsJ2 112 113 37 39 ≤ 15293684147816 := by decide +kernel

theorem rows22250R_3016 : rowsJ2 112 113 39 42 ≤ 12395802814194 := by decide +kernel

theorem rows22250R_3017 : rowsJ2 112 113 42 47 ≤ 5413637043365 := by decide +kernel

theorem rows22250R_3018 : rowsJ2 112 113 47 59 ≤ 217158911251 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3004
#print axioms SieveCert.rows22250R_3018
