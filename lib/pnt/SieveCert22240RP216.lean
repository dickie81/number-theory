/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2509–2520 of 5066

File 216 of 387: the parts `rows22240R_2509` … `rows22240R_2520` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 94559 in units of a depth-4 test: row 94 columns 68–72, row 94 columns
73–76, row 94 columns 77–78, row 94 columns 79–79, row 94 columns 80–80, row 94 columns 81–81, row 94 columns 82–82,
row 94 columns 83–83, row 94 columns 84–84, row 94 columns 85–85, row 94 columns 86–86, row 94 columns 87–87), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2509 : rowsJ2 94 95 68 73 ≤ 0 := by decide +kernel

theorem rows22240R_2510 : rowsJ2 94 95 73 77 ≤ 61393272355 := by decide +kernel

theorem rows22240R_2511 : rowsJ2 94 95 77 79 ≤ 564185682553 := by decide +kernel

theorem rows22240R_2512 : rowsJ2 94 95 79 80 ≤ 637510915380 := by decide +kernel

theorem rows22240R_2513 : rowsJ2 94 95 80 81 ≤ 968866622616 := by decide +kernel

theorem rows22240R_2514 : rowsJ2 94 95 81 82 ≤ 1435784363433 := by decide +kernel

theorem rows22240R_2515 : rowsJ2 94 95 82 83 ≤ 2063759634411 := by decide +kernel

theorem rows22240R_2516 : rowsJ2 94 95 83 84 ≤ 2847643044462 := by decide +kernel

theorem rows22240R_2517 : rowsJ2 94 95 84 85 ≤ 3816325611460 := by decide +kernel

theorem rows22240R_2518 : rowsJ2 94 95 85 86 ≤ 4869165742826 := by decide +kernel

theorem rows22240R_2519 : rowsJ2 94 95 86 87 ≤ 5730380176908 := by decide +kernel

theorem rows22240R_2520 : rowsJ2 94 95 87 88 ≤ 4979023553541 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2509
#print axioms SieveCert.rows22240R_2520
