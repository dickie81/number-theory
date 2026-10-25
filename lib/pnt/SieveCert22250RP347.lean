/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4174–4187 of 5796

File 347 of 465: the parts `rows22250R_4174` … `rows22250R_4187` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 98824 tests: row 135 columns 29–32, row 135 columns 33–41, row 135 columns
42–57, row 135 columns 58–59, row 135 columns 60–61, row 135 columns 62–62, row 135 columns 63–63, row 135 columns
64–64, row 135 columns 65–65, row 135 columns 66–66, row 135 columns 67–67, row 135 columns 68–68, row 135 columns
69–69, row 135 columns 70–70), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4174 : rowsJ2 135 136 29 33 ≤ 9768555305788 := by decide +kernel

theorem rows22250R_4175 : rowsJ2 135 136 33 42 ≤ 3564860715377 := by decide +kernel

theorem rows22250R_4176 : rowsJ2 135 136 42 58 ≤ 2883667045099 := by decide +kernel

theorem rows22250R_4177 : rowsJ2 135 136 58 60 ≤ 3158577286822 := by decide +kernel

theorem rows22250R_4178 : rowsJ2 135 136 60 62 ≤ 4795769601057 := by decide +kernel

theorem rows22250R_4179 : rowsJ2 135 136 62 63 ≤ 3101259065741 := by decide +kernel

theorem rows22250R_4180 : rowsJ2 135 136 63 64 ≤ 3615009196301 := by decide +kernel

theorem rows22250R_4181 : rowsJ2 135 136 64 65 ≤ 4125826996653 := by decide +kernel

theorem rows22250R_4182 : rowsJ2 135 136 65 66 ≤ 4580668067317 := by decide +kernel

theorem rows22250R_4183 : rowsJ2 135 136 66 67 ≤ 4996888480680 := by decide +kernel

theorem rows22250R_4184 : rowsJ2 135 136 67 68 ≤ 5356357414836 := by decide +kernel

theorem rows22250R_4185 : rowsJ2 135 136 68 69 ≤ 5676418482343 := by decide +kernel

theorem rows22250R_4186 : rowsJ2 135 136 69 70 ≤ 5938583292798 := by decide +kernel

theorem rows22250R_4187 : rowsJ2 135 136 70 71 ≤ 6160177387312 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4174
#print axioms SieveCert.rows22250R_4187
