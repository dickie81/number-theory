/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 516–528 of 4715

File 51 of 351: the parts `rows22250R_516` … `rows22250R_528` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 99722 tests: row 49 columns 42–42, row 49 columns 43–43, row 49 columns
44–44, row 49 columns 45–45, row 49 columns 46–46, row 49 columns 47–47, row 49 columns 48–48, row 49 columns
49–339, row 50 columns 0–14, row 50 columns 15–19, row 50 columns 20–22, row 50 columns 23–24, row 50 columns
25–25), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_516 : rowsJ2 49 50 42 43 ≤ 1390958979 := by decide +kernel

theorem rows22250R_517 : rowsJ2 49 50 43 44 ≤ 692846753 := by decide +kernel

theorem rows22250R_518 : rowsJ2 49 50 44 45 ≤ 76833621833 := by decide +kernel

theorem rows22250R_519 : rowsJ2 49 50 45 46 ≤ 301572146036 := by decide +kernel

theorem rows22250R_520 : rowsJ2 49 50 46 47 ≤ 899694862845 := by decide +kernel

theorem rows22250R_521 : rowsJ2 49 50 47 48 ≤ 1786654440326 := by decide +kernel

theorem rows22250R_522 : rowsJ2 49 50 48 49 ≤ 2640049428638 := by decide +kernel

theorem rows22250R_523 : rowsJ2 49 50 49 340 ≤ 3611050724844 := by decide +kernel

theorem rows22250R_524 : rowsJ2 50 51 0 15 ≤ 2746985524246 := by decide +kernel

theorem rows22250R_525 : rowsJ2 50 51 15 20 ≤ 2378222527767 := by decide +kernel

theorem rows22250R_526 : rowsJ2 50 51 20 23 ≤ 885319418404 := by decide +kernel

theorem rows22250R_527 : rowsJ2 50 51 23 25 ≤ 406185360991 := by decide +kernel

theorem rows22250R_528 : rowsJ2 50 51 25 26 ≤ 160589056488 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_516
#print axioms SieveCert.rows22250R_528
