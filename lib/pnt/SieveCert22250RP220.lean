/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2737–2752 of 4715

File 220 of 351: the parts `rows22250R_2737` … `rows22250R_2752` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 96384 tests: row 103 columns 34–35, row 103 columns 36–36, row 103 columns
37–37, row 103 columns 38–38, row 103 columns 39–39, row 103 columns 40–40, row 103 columns 41–41, row 103 columns
42–43, row 103 columns 44–45, row 103 columns 46–47, row 103 columns 48–50, row 103 columns 51–55, row 103 columns
56–65, row 103 columns 66–71, row 103 columns 72–75, row 103 columns 76–77), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2737 : rowsJ2 103 104 34 36 ≤ 17676554845096 := by decide +kernel

theorem rows22250R_2738 : rowsJ2 103 104 36 37 ≤ 11750616116965 := by decide +kernel

theorem rows22250R_2739 : rowsJ2 103 104 37 38 ≤ 14161059124060 := by decide +kernel

theorem rows22250R_2740 : rowsJ2 103 104 38 39 ≤ 16003015830607 := by decide +kernel

theorem rows22250R_2741 : rowsJ2 103 104 39 40 ≤ 13831855222678 := by decide +kernel

theorem rows22250R_2742 : rowsJ2 103 104 40 41 ≤ 11867330615694 := by decide +kernel

theorem rows22250R_2743 : rowsJ2 103 104 41 42 ≤ 10104058732763 := by decide +kernel

theorem rows22250R_2744 : rowsJ2 103 104 42 44 ≤ 15699509372734 := by decide +kernel

theorem rows22250R_2745 : rowsJ2 103 104 44 46 ≤ 10540434852064 := by decide +kernel

theorem rows22250R_2746 : rowsJ2 103 104 46 48 ≤ 6066822665655 := by decide +kernel

theorem rows22250R_2747 : rowsJ2 103 104 48 51 ≤ 3264535083273 := by decide +kernel

theorem rows22250R_2748 : rowsJ2 103 104 51 56 ≤ 378240748151 := by decide +kernel

theorem rows22250R_2749 : rowsJ2 103 104 56 66 ≤ 0 := by decide +kernel

theorem rows22250R_2750 : rowsJ2 103 104 66 72 ≤ 0 := by decide +kernel

theorem rows22250R_2751 : rowsJ2 103 104 72 76 ≤ 15228802362 := by decide +kernel

theorem rows22250R_2752 : rowsJ2 103 104 76 78 ≤ 332519565582 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2737
#print axioms SieveCert.rows22250R_2752
