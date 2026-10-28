/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3695–3709 of 5066

File 294 of 387: the parts `rows22240R_3695` … `rows22240R_3709` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 97009 in units of a depth-4 test: row 128 columns 79–80, row 128
columns 81–83, row 128 columns 84–86, row 128 columns 87–89, row 128 columns 90–339, row 129 columns 0–24, row 129
columns 25–28, row 129 columns 29–34, row 129 columns 35–52, row 129 columns 53–56, row 129 columns 57–58, row 129
columns 59–59, row 129 columns 60–60, row 129 columns 61–61, row 129 columns 62–62), each a sum of refined costs
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

theorem rows22240R_3695 : rowsJ2 128 129 79 81 ≤ 2688544027895 := by decide +kernel

theorem rows22240R_3696 : rowsJ2 128 129 81 84 ≤ 6172192028737 := by decide +kernel

theorem rows22240R_3697 : rowsJ2 128 129 84 87 ≤ 13453654497510 := by decide +kernel

theorem rows22240R_3698 : rowsJ2 128 129 87 90 ≤ 25490202741039 := by decide +kernel

theorem rows22240R_3699 : rowsJ2 128 129 90 340 ≤ 888890290758955 := by decide +kernel

theorem rows22240R_3700 : rowsJ2 129 130 0 25 ≤ 3611873440748 := by decide +kernel

theorem rows22240R_3701 : rowsJ2 129 130 25 29 ≤ 17072457640621 := by decide +kernel

theorem rows22240R_3702 : rowsJ2 129 130 29 35 ≤ 13579489384987 := by decide +kernel

theorem rows22240R_3703 : rowsJ2 129 130 35 53 ≤ 2567497478084 := by decide +kernel

theorem rows22240R_3704 : rowsJ2 129 130 53 57 ≤ 6294118423478 := by decide +kernel

theorem rows22240R_3705 : rowsJ2 129 130 57 59 ≤ 6039875137414 := by decide +kernel

theorem rows22240R_3706 : rowsJ2 129 130 59 60 ≤ 3902212551400 := by decide +kernel

theorem rows22240R_3707 : rowsJ2 129 130 60 61 ≤ 4545819645643 := by decide +kernel

theorem rows22240R_3708 : rowsJ2 129 130 61 62 ≤ 5207465365674 := by decide +kernel

theorem rows22240R_3709 : rowsJ2 129 130 62 63 ≤ 5822236423923 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3695
#print axioms SieveCert.rows22240R_3709
