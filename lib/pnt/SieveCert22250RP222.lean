/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2770–2785 of 4715

File 222 of 351: the parts `rows22250R_2770` … `rows22250R_2785` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 98729 in units of a depth-4 test: row 103 columns 101–101, row 103
columns 102–339, row 104 columns 0–22, row 104 columns 23–30, row 104 columns 31–33, row 104 columns 34–35, row 104
columns 36–36, row 104 columns 37–37, row 104 columns 38–38, row 104 columns 39–39, row 104 columns 40–40, row 104
columns 41–42, row 104 columns 43–44, row 104 columns 45–46, row 104 columns 47–49, row 104 columns 50–54), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22250R_2770 : rowsJ2 103 104 101 102 ≤ 12396800309582 := by decide +kernel

theorem rows22250R_2771 : rowsJ2 103 104 102 340 ≤ 163944509086853 := by decide +kernel

theorem rows22250R_2772 : rowsJ2 104 105 0 23 ≤ 0 := by decide +kernel

theorem rows22250R_2773 : rowsJ2 104 105 23 31 ≤ 4085271092881 := by decide +kernel

theorem rows22250R_2774 : rowsJ2 104 105 31 34 ≤ 14552109948448 := by decide +kernel

theorem rows22250R_2775 : rowsJ2 104 105 34 36 ≤ 18585427427971 := by decide +kernel

theorem rows22250R_2776 : rowsJ2 104 105 36 37 ≤ 12356668601015 := by decide +kernel

theorem rows22250R_2777 : rowsJ2 104 105 37 38 ≤ 14988671948607 := by decide +kernel

theorem rows22250R_2778 : rowsJ2 104 105 38 39 ≤ 14812401295935 := by decide +kernel

theorem rows22250R_2779 : rowsJ2 104 105 39 40 ≤ 12708937293651 := by decide +kernel

theorem rows22250R_2780 : rowsJ2 104 105 40 41 ≤ 10813413006891 := by decide +kernel

theorem rows22250R_2781 : rowsJ2 104 105 41 43 ≤ 16746196258574 := by decide +kernel

theorem rows22250R_2782 : rowsJ2 104 105 43 45 ≤ 11433757909805 := by decide +kernel

theorem rows22250R_2783 : rowsJ2 104 105 45 47 ≤ 6920908520213 := by decide +kernel

theorem rows22250R_2784 : rowsJ2 104 105 47 50 ≤ 3876801840674 := by decide +kernel

theorem rows22250R_2785 : rowsJ2 104 105 50 55 ≤ 379598726336 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2770
#print axioms SieveCert.rows22250R_2785
