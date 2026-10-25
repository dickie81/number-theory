/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1941–1951 of 5796

File 188 of 465: the parts `rows22250R_1941` … `rows22250R_1951` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 95531 tests: row 81 columns 58–58, row 81 columns 59–59, row 81 columns
60–60, row 81 columns 61–61, row 81 columns 62–62, row 81 columns 63–63, row 81 columns 64–64, row 81 columns 65–65,
row 81 columns 66–66, row 81 columns 67–67, row 81 columns 68–68), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1941 : rowsJ2 81 82 58 59 ≤ 1450761209679 := by decide +kernel

theorem rows22250R_1942 : rowsJ2 81 82 59 60 ≤ 1313875471536 := by decide +kernel

theorem rows22250R_1943 : rowsJ2 81 82 60 61 ≤ 1178301902700 := by decide +kernel

theorem rows22250R_1944 : rowsJ2 81 82 61 62 ≤ 1039517600608 := by decide +kernel

theorem rows22250R_1945 : rowsJ2 81 82 62 63 ≤ 901945457518 := by decide +kernel

theorem rows22250R_1946 : rowsJ2 81 82 63 64 ≤ 760948338825 := by decide +kernel

theorem rows22250R_1947 : rowsJ2 81 82 64 65 ≤ 621062553416 := by decide +kernel

theorem rows22250R_1948 : rowsJ2 81 82 65 66 ≤ 477529710796 := by decide +kernel

theorem rows22250R_1949 : rowsJ2 81 82 66 67 ≤ 335005764223 := by decide +kernel

theorem rows22250R_1950 : rowsJ2 81 82 67 68 ≤ 239329241842 := by decide +kernel

theorem rows22250R_1951 : rowsJ2 81 82 68 69 ≤ 144274962407 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1941
#print axioms SieveCert.rows22250R_1951
