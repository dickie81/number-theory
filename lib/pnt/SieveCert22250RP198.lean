/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2073–2085 of 5796

File 198 of 465: the parts `rows22250R_2073` … `rows22250R_2085` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 97074 tests: row 84 columns 37–39, row 84 columns 40–41, row 84 columns
42–42, row 84 columns 43–43, row 84 columns 44–44, row 84 columns 45–45, row 84 columns 46–46, row 84 columns 47–47,
row 84 columns 48–48, row 84 columns 49–49, row 84 columns 50–50, row 84 columns 51–51, row 84 columns 52–52), each
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

theorem rows22250R_2073 : rowsJ2 84 85 37 40 ≤ 2443311431594 := by decide +kernel

theorem rows22250R_2074 : rowsJ2 84 85 40 42 ≤ 854733664190 := by decide +kernel

theorem rows22250R_2075 : rowsJ2 84 85 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_2076 : rowsJ2 84 85 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_2077 : rowsJ2 84 85 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_2078 : rowsJ2 84 85 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_2079 : rowsJ2 84 85 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_2080 : rowsJ2 84 85 47 48 ≤ 92300290090 := by decide +kernel

theorem rows22250R_2081 : rowsJ2 84 85 48 49 ≤ 413675035153 := by decide +kernel

theorem rows22250R_2082 : rowsJ2 84 85 49 50 ≤ 728233351011 := by decide +kernel

theorem rows22250R_2083 : rowsJ2 84 85 50 51 ≤ 907674135463 := by decide +kernel

theorem rows22250R_2084 : rowsJ2 84 85 51 52 ≤ 1001233450721 := by decide +kernel

theorem rows22250R_2085 : rowsJ2 84 85 52 53 ≤ 1145730472830 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2073
#print axioms SieveCert.rows22250R_2085
