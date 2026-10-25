/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3849–3864 of 5796

File 326 of 465: the parts `rows22250R_3849` … `rows22250R_3864` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 98577 tests: row 124 columns 94–95, row 124 columns 96–97, row 124 columns
98–98, row 124 columns 99–99, row 124 columns 100–100, row 124 columns 101–359, row 125 columns 0–26, row 125
columns 27–29, row 125 columns 30–31, row 125 columns 32–33, row 125 columns 34–35, row 125 columns 36–38, row 125
columns 39–42, row 125 columns 43–51, row 125 columns 52–62, row 125 columns 63–64), each a sum of refined costs
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

theorem rows22250R_3849 : rowsJ2 124 125 94 96 ≤ 9261903586542 := by decide +kernel

theorem rows22250R_3850 : rowsJ2 124 125 96 98 ≤ 13044570662217 := by decide +kernel

theorem rows22250R_3851 : rowsJ2 124 125 98 99 ≤ 8150504606831 := by decide +kernel

theorem rows22250R_3852 : rowsJ2 124 125 99 100 ≤ 9372200237510 := by decide +kernel

theorem rows22250R_3853 : rowsJ2 124 125 100 101 ≤ 10665719519843 := by decide +kernel

theorem rows22250R_3854 : rowsJ2 124 125 101 360 ≤ 1291418026413334 := by decide +kernel

theorem rows22250R_3855 : rowsJ2 125 126 0 27 ≤ 782227163917 := by decide +kernel

theorem rows22250R_3856 : rowsJ2 125 126 27 30 ≤ 5444456679000 := by decide +kernel

theorem rows22250R_3857 : rowsJ2 125 126 30 32 ≤ 9650001265893 := by decide +kernel

theorem rows22250R_3858 : rowsJ2 125 126 32 34 ≤ 14852155304410 := by decide +kernel

theorem rows22250R_3859 : rowsJ2 125 126 34 36 ≤ 12932989910555 := by decide +kernel

theorem rows22250R_3860 : rowsJ2 125 126 36 39 ≤ 13701586803285 := by decide +kernel

theorem rows22250R_3861 : rowsJ2 125 126 39 43 ≤ 7777222481668 := by decide +kernel

theorem rows22250R_3862 : rowsJ2 125 126 43 52 ≤ 940675728408 := by decide +kernel

theorem rows22250R_3863 : rowsJ2 125 126 52 63 ≤ 2522020407005 := by decide +kernel

theorem rows22250R_3864 : rowsJ2 125 126 63 65 ≤ 2730590435494 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3849
#print axioms SieveCert.rows22250R_3864
