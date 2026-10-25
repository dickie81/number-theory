/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2165–2178 of 5796

File 205 of 465: the parts `rows22250R_2165` … `rows22250R_2178` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 92564 tests: row 86 columns 26–27, row 86 columns 28–30, row 86 columns
31–34, row 86 columns 35–37, row 86 columns 38–39, row 86 columns 40–41, row 86 columns 42–42, row 86 columns 43–43,
row 86 columns 44–44, row 86 columns 45–45, row 86 columns 46–46, row 86 columns 47–47, row 86 columns 48–48, row 86
columns 49–49), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22250R_2165 : rowsJ2 86 87 26 28 ≤ 0 := by decide +kernel

theorem rows22250R_2166 : rowsJ2 86 87 28 31 ≤ 0 := by decide +kernel

theorem rows22250R_2167 : rowsJ2 86 87 31 35 ≤ 0 := by decide +kernel

theorem rows22250R_2168 : rowsJ2 86 87 35 38 ≤ 1659553210158 := by decide +kernel

theorem rows22250R_2169 : rowsJ2 86 87 38 40 ≤ 4311764731871 := by decide +kernel

theorem rows22250R_2170 : rowsJ2 86 87 40 42 ≤ 4871062531722 := by decide +kernel

theorem rows22250R_2171 : rowsJ2 86 87 42 43 ≤ 1516561023630 := by decide +kernel

theorem rows22250R_2172 : rowsJ2 86 87 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_2173 : rowsJ2 86 87 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_2174 : rowsJ2 86 87 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_2175 : rowsJ2 86 87 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_2176 : rowsJ2 86 87 47 48 ≤ 90940921249 := by decide +kernel

theorem rows22250R_2177 : rowsJ2 86 87 48 49 ≤ 407582562936 := by decide +kernel

theorem rows22250R_2178 : rowsJ2 86 87 49 50 ≤ 589248387631 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2165
#print axioms SieveCert.rows22250R_2178
