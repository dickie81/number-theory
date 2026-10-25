/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2099–2111 of 4715

File 175 of 351: the parts `rows22250R_2099` … `rows22250R_2111` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 96734 tests: row 87 columns 87–339, row 88 columns 0–16, row 88 columns
17–19, row 88 columns 20–23, row 88 columns 24–29, row 88 columns 30–34, row 88 columns 35–37, row 88 columns 38–39,
row 88 columns 40–40, row 88 columns 41–41, row 88 columns 42–42, row 88 columns 43–43, row 88 columns 44–44), each
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

theorem rows22250R_2099 : rowsJ2 87 88 87 340 ≤ 7718226717822 := by decide +kernel

theorem rows22250R_2100 : rowsJ2 88 89 0 17 ≤ 0 := by decide +kernel

theorem rows22250R_2101 : rowsJ2 88 89 17 20 ≤ 0 := by decide +kernel

theorem rows22250R_2102 : rowsJ2 88 89 20 24 ≤ 0 := by decide +kernel

theorem rows22250R_2103 : rowsJ2 88 89 24 30 ≤ 0 := by decide +kernel

theorem rows22250R_2104 : rowsJ2 88 89 30 35 ≤ 3708848335722 := by decide +kernel

theorem rows22250R_2105 : rowsJ2 88 89 35 38 ≤ 13240261229347 := by decide +kernel

theorem rows22250R_2106 : rowsJ2 88 89 38 40 ≤ 15497060175256 := by decide +kernel

theorem rows22250R_2107 : rowsJ2 88 89 40 41 ≤ 9639469143953 := by decide +kernel

theorem rows22250R_2108 : rowsJ2 88 89 41 42 ≤ 10925676040191 := by decide +kernel

theorem rows22250R_2109 : rowsJ2 88 89 42 43 ≤ 12323730761914 := by decide +kernel

theorem rows22250R_2110 : rowsJ2 88 89 43 44 ≤ 13828278948461 := by decide +kernel

theorem rows22250R_2111 : rowsJ2 88 89 44 45 ≤ 15210301306050 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2099
#print axioms SieveCert.rows22250R_2111
