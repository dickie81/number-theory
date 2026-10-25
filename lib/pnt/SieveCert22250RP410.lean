/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4978–4993 of 5796

File 410 of 465: the parts `rows22250R_4978` … `rows22250R_4993` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 96879 tests: row 161 columns 67–67, row 161 columns 68–68, row 161 columns
69–69, row 161 columns 70–71, row 161 columns 72–74, row 161 columns 75–359, row 162 columns 0–43, row 162 columns
44–46, row 162 columns 47–48, row 162 columns 49–49, row 162 columns 50–50, row 162 columns 51–51, row 162 columns
52–52, row 162 columns 53–53, row 162 columns 54–54, row 162 columns 55–55), each a sum of refined costs (`rows2` or
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

theorem rows22250R_4978 : rowsJ2 161 162 67 68 ≤ 6110083798262 := by decide +kernel

theorem rows22250R_4979 : rowsJ2 161 162 68 69 ≤ 5276387256551 := by decide +kernel

theorem rows22250R_4980 : rowsJ2 161 162 69 70 ≤ 4507532480912 := by decide +kernel

theorem rows22250R_4981 : rowsJ2 161 162 70 72 ≤ 6961962382596 := by decide +kernel

theorem rows22250R_4982 : rowsJ2 161 162 72 75 ≤ 6233934772770 := by decide +kernel

theorem rows22250R_4983 : rowsJ2 161 162 75 360 ≤ 2128285850095304 := by decide +kernel

theorem rows22250R_4984 : rowsJ2 162 163 0 44 ≤ 3570694827303 := by decide +kernel

theorem rows22250R_4985 : rowsJ2 162 163 44 47 ≤ 7275085448664 := by decide +kernel

theorem rows22250R_4986 : rowsJ2 162 163 47 49 ≤ 7972177274325 := by decide +kernel

theorem rows22250R_4987 : rowsJ2 162 163 49 50 ≤ 5077349969328 := by decide +kernel

theorem rows22250R_4988 : rowsJ2 162 163 50 51 ≤ 5868332675358 := by decide +kernel

theorem rows22250R_4989 : rowsJ2 162 163 51 52 ≤ 6704449701829 := by decide +kernel

theorem rows22250R_4990 : rowsJ2 162 163 52 53 ≤ 7583909309774 := by decide +kernel

theorem rows22250R_4991 : rowsJ2 162 163 53 54 ≤ 8505064715867 := by decide +kernel

theorem rows22250R_4992 : rowsJ2 162 163 54 55 ≤ 9466406403432 := by decide +kernel

theorem rows22250R_4993 : rowsJ2 162 163 55 56 ≤ 10466555116465 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4978
#print axioms SieveCert.rows22250R_4993
