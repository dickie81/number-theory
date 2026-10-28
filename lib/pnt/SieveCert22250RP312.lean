/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4091–4104 of 4715

File 312 of 351: the parts `rows22250R_4091` … `rows22250R_4104` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 95005 in units of a depth-4 test: row 155 columns 0–41, row 155 columns
42–44, row 155 columns 45–46, row 155 columns 47–47, row 155 columns 48–48, row 155 columns 49–49, row 155 columns
50–50, row 155 columns 51–51, row 155 columns 52–52, row 155 columns 53–53, row 155 columns 54–54, row 155 columns
55–55, row 155 columns 56–56, row 155 columns 57–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4091 : rowsJ2 155 156 0 42 ≤ 7033814289629 := by decide +kernel

theorem rows22250R_4092 : rowsJ2 155 156 42 45 ≤ 11637386492367 := by decide +kernel

theorem rows22250R_4093 : rowsJ2 155 156 45 47 ≤ 12087848512382 := by decide +kernel

theorem rows22250R_4094 : rowsJ2 155 156 47 48 ≤ 7528562389904 := by decide +kernel

theorem rows22250R_4095 : rowsJ2 155 156 48 49 ≤ 8594559303265 := by decide +kernel

theorem rows22250R_4096 : rowsJ2 155 156 49 50 ≤ 9714800926577 := by decide +kernel

theorem rows22250R_4097 : rowsJ2 155 156 50 51 ≤ 10887188401301 := by decide +kernel

theorem rows22250R_4098 : rowsJ2 155 156 51 52 ≤ 12109816533329 := by decide +kernel

theorem rows22250R_4099 : rowsJ2 155 156 52 53 ≤ 13380963712109 := by decide +kernel

theorem rows22250R_4100 : rowsJ2 155 156 53 54 ≤ 14699082846882 := by decide +kernel

theorem rows22250R_4101 : rowsJ2 155 156 54 55 ≤ 16062793257233 := by decide +kernel

theorem rows22250R_4102 : rowsJ2 155 156 55 56 ≤ 15905364507366 := by decide +kernel

theorem rows22250R_4103 : rowsJ2 155 156 56 57 ≤ 14271087798064 := by decide +kernel

theorem rows22250R_4104 : rowsJ2 155 156 57 58 ≤ 12737846936591 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4091
#print axioms SieveCert.rows22250R_4104
