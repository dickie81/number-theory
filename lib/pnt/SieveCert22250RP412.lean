/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5005–5020 of 5796

File 412 of 465: the parts `rows22250R_5005` … `rows22250R_5020` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 96096 tests: row 162 columns 67–67, row 162 columns 68–68, row 162 columns
69–70, row 162 columns 71–72, row 162 columns 73–76, row 162 columns 77–359, row 163 columns 0–43, row 163 columns
44–46, row 163 columns 47–48, row 163 columns 49–49, row 163 columns 50–50, row 163 columns 51–51, row 163 columns
52–52, row 163 columns 53–53, row 163 columns 54–54, row 163 columns 55–55), each a sum of refined costs (`rows2` or
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

theorem rows22250R_5005 : rowsJ2 162 163 67 68 ≤ 5786022052540 := by decide +kernel

theorem rows22250R_5006 : rowsJ2 162 163 68 69 ≤ 4971633905776 := by decide +kernel

theorem rows22250R_5007 : rowsJ2 162 163 69 71 ≤ 7760215009678 := by decide +kernel

theorem rows22250R_5008 : rowsJ2 162 163 71 73 ≤ 5271842151737 := by decide +kernel

theorem rows22250R_5009 : rowsJ2 162 163 73 77 ≤ 5040155239082 := by decide +kernel

theorem rows22250R_5010 : rowsJ2 162 163 77 360 ≤ 2226002136008135 := by decide +kernel

theorem rows22250R_5011 : rowsJ2 163 164 0 44 ≤ 4449592123049 := by decide +kernel

theorem rows22250R_5012 : rowsJ2 163 164 44 47 ≤ 8249778102583 := by decide +kernel

theorem rows22250R_5013 : rowsJ2 163 164 47 49 ≤ 8810441837257 := by decide +kernel

theorem rows22250R_5014 : rowsJ2 163 164 49 50 ≤ 5551882911809 := by decide +kernel

theorem rows22250R_5015 : rowsJ2 163 164 50 51 ≤ 6379398786597 := by decide +kernel

theorem rows22250R_5016 : rowsJ2 163 164 51 52 ≤ 7251803940297 := by decide +kernel

theorem rows22250R_5017 : rowsJ2 163 164 52 53 ≤ 8167350356544 := by decide +kernel

theorem rows22250R_5018 : rowsJ2 163 164 53 54 ≤ 9124434635683 := by decide +kernel

theorem rows22250R_5019 : rowsJ2 163 164 54 55 ≤ 10121590448744 := by decide +kernel

theorem rows22250R_5020 : rowsJ2 163 164 55 56 ≤ 11157481675524 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5005
#print axioms SieveCert.rows22250R_5020
