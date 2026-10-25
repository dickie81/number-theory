/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3913–3928 of 5796

File 330 of 465: the parts `rows22250R_3913` … `rows22250R_3928` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 99364 tests: row 126 columns 97–98, row 126 columns 99–99, row 126 columns
100–359, row 127 columns 0–26, row 127 columns 27–29, row 127 columns 30–31, row 127 columns 32–33, row 127 columns
34–36, row 127 columns 37–40, row 127 columns 41–49, row 127 columns 50–61, row 127 columns 62–63, row 127 columns
64–65, row 127 columns 66–66, row 127 columns 67–67, row 127 columns 68–68), each a sum of refined costs (`rows2` or
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

theorem rows22250R_3913 : rowsJ2 126 127 97 99 ≤ 16849706249112 := by decide +kernel

theorem rows22250R_3914 : rowsJ2 126 127 99 100 ≤ 10354291147387 := by decide +kernel

theorem rows22250R_3915 : rowsJ2 126 127 100 360 ≤ 1188839854830649 := by decide +kernel

theorem rows22250R_3916 : rowsJ2 127 128 0 27 ≤ 976620059779 := by decide +kernel

theorem rows22250R_3917 : rowsJ2 127 128 27 30 ≤ 7176168213684 := by decide +kernel

theorem rows22250R_3918 : rowsJ2 127 128 30 32 ≤ 11342695704519 := by decide +kernel

theorem rows22250R_3919 : rowsJ2 127 128 32 34 ≤ 13097558368520 := by decide +kernel

theorem rows22250R_3920 : rowsJ2 127 128 34 37 ≤ 13866519788336 := by decide +kernel

theorem rows22250R_3921 : rowsJ2 127 128 37 41 ≤ 8974975213058 := by decide +kernel

theorem rows22250R_3922 : rowsJ2 127 128 41 50 ≤ 1048749068075 := by decide +kernel

theorem rows22250R_3923 : rowsJ2 127 128 50 62 ≤ 2588030637943 := by decide +kernel

theorem rows22250R_3924 : rowsJ2 127 128 62 64 ≤ 2838950446035 := by decide +kernel

theorem rows22250R_3925 : rowsJ2 127 128 64 66 ≤ 4114325262921 := by decide +kernel

theorem rows22250R_3926 : rowsJ2 127 128 66 67 ≤ 2429580305762 := by decide +kernel

theorem rows22250R_3927 : rowsJ2 127 128 67 68 ≤ 2605630754096 := by decide +kernel

theorem rows22250R_3928 : rowsJ2 127 128 68 69 ≤ 2740745121036 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3913
#print axioms SieveCert.rows22250R_3928
