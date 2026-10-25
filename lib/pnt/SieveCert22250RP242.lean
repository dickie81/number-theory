/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3079–3092 of 4715

File 242 of 351: the parts `rows22250R_3079` … `rows22250R_3092` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 93477 tests: row 114 columns 97–339, row 115 columns 0–26, row 115 columns
27–29, row 115 columns 30–31, row 115 columns 32–33, row 115 columns 34–35, row 115 columns 36–38, row 115 columns
39–43, row 115 columns 44–57, row 115 columns 58–61, row 115 columns 62–64, row 115 columns 65–67, row 115 columns
68–71, row 115 columns 72–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_3079 : rowsJ2 114 115 97 340 ≤ 1582159019931668 := by decide +kernel

theorem rows22250R_3080 : rowsJ2 115 116 0 27 ≤ 1290085865706 := by decide +kernel

theorem rows22250R_3081 : rowsJ2 115 116 27 30 ≤ 9930694578477 := by decide +kernel

theorem rows22250R_3082 : rowsJ2 115 116 30 32 ≤ 14788623909170 := by decide +kernel

theorem rows22250R_3083 : rowsJ2 115 116 32 34 ≤ 20490727481235 := by decide +kernel

theorem rows22250R_3084 : rowsJ2 115 116 34 36 ≤ 16188040430617 := by decide +kernel

theorem rows22250R_3085 : rowsJ2 115 116 36 39 ≤ 16410879653654 := by decide +kernel

theorem rows22250R_3086 : rowsJ2 115 116 39 44 ≤ 7271334389715 := by decide +kernel

theorem rows22250R_3087 : rowsJ2 115 116 44 58 ≤ 507623880376 := by decide +kernel

theorem rows22250R_3088 : rowsJ2 115 116 58 62 ≤ 3195987034986 := by decide +kernel

theorem rows22250R_3089 : rowsJ2 115 116 62 65 ≤ 4003280814485 := by decide +kernel

theorem rows22250R_3090 : rowsJ2 115 116 65 68 ≤ 3510098534768 := by decide +kernel

theorem rows22250R_3091 : rowsJ2 115 116 68 72 ≤ 1150432267198 := by decide +kernel

theorem rows22250R_3092 : rowsJ2 115 116 72 75 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3079
#print axioms SieveCert.rows22250R_3092
