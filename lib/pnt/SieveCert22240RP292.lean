/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3666–3680 of 5066

File 292 of 387: the parts `rows22240R_3666` … `rows22240R_3680` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 95185 in units of a depth-4 test: row 127 columns 83–85, row 127
columns 86–88, row 127 columns 89–90, row 127 columns 91–339, row 128 columns 0–24, row 128 columns 25–28, row 128
columns 29–33, row 128 columns 34–50, row 128 columns 51–55, row 128 columns 56–57, row 128 columns 58–59, row 128
columns 60–60, row 128 columns 61–61, row 128 columns 62–62, row 128 columns 63–63), each a sum of refined costs
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

theorem rows22240R_3666 : rowsJ2 127 128 83 86 ≤ 9552874588695 := by decide +kernel

theorem rows22240R_3667 : rowsJ2 127 128 86 89 ≤ 19888422796078 := by decide +kernel

theorem rows22240R_3668 : rowsJ2 127 128 89 91 ≤ 20760577447885 := by decide +kernel

theorem rows22240R_3669 : rowsJ2 127 128 91 340 ≤ 893735321783888 := by decide +kernel

theorem rows22240R_3670 : rowsJ2 128 129 0 25 ≤ 3083205717082 := by decide +kernel

theorem rows22240R_3671 : rowsJ2 128 129 25 29 ≤ 17945933515377 := by decide +kernel

theorem rows22240R_3672 : rowsJ2 128 129 29 34 ≤ 15262044927336 := by decide +kernel

theorem rows22240R_3673 : rowsJ2 128 129 34 51 ≤ 3903542950922 := by decide +kernel

theorem rows22240R_3674 : rowsJ2 128 129 51 56 ≤ 4295615338125 := by decide +kernel

theorem rows22240R_3675 : rowsJ2 128 129 56 58 ≤ 4414210484982 := by decide +kernel

theorem rows22240R_3676 : rowsJ2 128 129 58 60 ≤ 6531261752733 := by decide +kernel

theorem rows22240R_3677 : rowsJ2 128 129 60 61 ≤ 4166694562947 := by decide +kernel

theorem rows22240R_3678 : rowsJ2 128 129 61 62 ≤ 4799442606698 := by decide +kernel

theorem rows22240R_3679 : rowsJ2 128 129 62 63 ≤ 5385087091747 := by decide +kernel

theorem rows22240R_3680 : rowsJ2 128 129 63 64 ≤ 5901550294103 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3666
#print axioms SieveCert.rows22240R_3680
