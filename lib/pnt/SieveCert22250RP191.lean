/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2304–2314 of 4715

File 191 of 351: the parts `rows22250R_2304` … `rows22250R_2314` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 97828 tests: row 92 columns 88–88, row 92 columns 89–89, row 92 columns
90–90, row 92 columns 91–91, row 92 columns 92–339, row 93 columns 0–15, row 93 columns 16–20, row 93 columns 21–29,
row 93 columns 30–34, row 93 columns 35–36, row 93 columns 37–38), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2304 : rowsJ2 92 93 88 89 ≤ 4384419135777 := by decide +kernel

theorem rows22250R_2305 : rowsJ2 92 93 89 90 ≤ 4160643002997 := by decide +kernel

theorem rows22250R_2306 : rowsJ2 92 93 90 91 ≤ 4005241579651 := by decide +kernel

theorem rows22250R_2307 : rowsJ2 92 93 91 92 ≤ 3937593117325 := by decide +kernel

theorem rows22250R_2308 : rowsJ2 92 93 92 340 ≤ 3941655249713 := by decide +kernel

theorem rows22250R_2309 : rowsJ2 93 94 0 16 ≤ 0 := by decide +kernel

theorem rows22250R_2310 : rowsJ2 93 94 16 21 ≤ 0 := by decide +kernel

theorem rows22250R_2311 : rowsJ2 93 94 21 30 ≤ 0 := by decide +kernel

theorem rows22250R_2312 : rowsJ2 93 94 30 35 ≤ 7900262994323 := by decide +kernel

theorem rows22250R_2313 : rowsJ2 93 94 35 37 ≤ 11087346556049 := by decide +kernel

theorem rows22250R_2314 : rowsJ2 93 94 37 39 ≤ 17277761997614 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2304
#print axioms SieveCert.rows22250R_2314
