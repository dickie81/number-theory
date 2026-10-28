/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2456–2471 of 5066

File 212 of 387: the parts `rows22240R_2456` … `rows22240R_2471` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 95745 in units of a depth-4 test: row 93 columns 52–52, row 93 columns
53–53, row 93 columns 54–54, row 93 columns 55–56, row 93 columns 57–58, row 93 columns 59–60, row 93 columns 61–63,
row 93 columns 64–67, row 93 columns 68–72, row 93 columns 73–76, row 93 columns 77–78, row 93 columns 79–79, row 93
columns 80–80, row 93 columns 81–81, row 93 columns 82–82, row 93 columns 83–83), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2456 : rowsJ2 93 94 52 53 ≤ 2986241781855 := by decide +kernel

theorem rows22240R_2457 : rowsJ2 93 94 53 54 ≤ 1186821872513 := by decide +kernel

theorem rows22240R_2458 : rowsJ2 93 94 54 55 ≤ 0 := by decide +kernel

theorem rows22240R_2459 : rowsJ2 93 94 55 57 ≤ 0 := by decide +kernel

theorem rows22240R_2460 : rowsJ2 93 94 57 59 ≤ 0 := by decide +kernel

theorem rows22240R_2461 : rowsJ2 93 94 59 61 ≤ 0 := by decide +kernel

theorem rows22240R_2462 : rowsJ2 93 94 61 64 ≤ 0 := by decide +kernel

theorem rows22240R_2463 : rowsJ2 93 94 64 68 ≤ 0 := by decide +kernel

theorem rows22240R_2464 : rowsJ2 93 94 68 73 ≤ 0 := by decide +kernel

theorem rows22240R_2465 : rowsJ2 93 94 73 77 ≤ 61957568922 := by decide +kernel

theorem rows22240R_2466 : rowsJ2 93 94 77 79 ≤ 569374517423 := by decide +kernel

theorem rows22240R_2467 : rowsJ2 93 94 79 80 ≤ 643379752480 := by decide +kernel

theorem rows22240R_2468 : rowsJ2 93 94 80 81 ≤ 977692692223 := by decide +kernel

theorem rows22240R_2469 : rowsJ2 93 94 81 82 ≤ 1445709708642 := by decide +kernel

theorem rows22240R_2470 : rowsJ2 93 94 82 83 ≤ 2072522045294 := by decide +kernel

theorem rows22240R_2471 : rowsJ2 93 94 83 84 ≤ 2852232272878 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2456
#print axioms SieveCert.rows22240R_2471
