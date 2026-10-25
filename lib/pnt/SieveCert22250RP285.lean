/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3713–3725 of 4715

File 285 of 351: the parts `rows22250R_3713` … `rows22250R_3725` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 99474 tests: row 139 columns 61–61, row 139 columns 62–62, row 139 columns
63–63, row 139 columns 64–64, row 139 columns 65–65, row 139 columns 66–66, row 139 columns 67–67, row 139 columns
68–68, row 139 columns 69–69, row 139 columns 70–70, row 139 columns 71–71, row 139 columns 72–73, row 139 columns
74–75), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3713 : rowsJ2 139 140 61 62 ≤ 11131203986222 := by decide +kernel

theorem rows22250R_3714 : rowsJ2 139 140 62 63 ≤ 11979399953297 := by decide +kernel

theorem rows22250R_3715 : rowsJ2 139 140 63 64 ≤ 11784604603948 := by decide +kernel

theorem rows22250R_3716 : rowsJ2 139 140 64 65 ≤ 10618626405943 := by decide +kernel

theorem rows22250R_3717 : rowsJ2 139 140 65 66 ≤ 9529507484111 := by decide +kernel

theorem rows22250R_3718 : rowsJ2 139 140 66 67 ≤ 8493830258010 := by decide +kernel

theorem rows22250R_3719 : rowsJ2 139 140 67 68 ≤ 7531066852233 := by decide +kernel

theorem rows22250R_3720 : rowsJ2 139 140 68 69 ≤ 6617784587481 := by decide +kernel

theorem rows22250R_3721 : rowsJ2 139 140 69 70 ≤ 5773909953438 := by decide +kernel

theorem rows22250R_3722 : rowsJ2 139 140 70 71 ≤ 4975956800097 := by decide +kernel

theorem rows22250R_3723 : rowsJ2 139 140 71 72 ≤ 4244300401975 := by decide +kernel

theorem rows22250R_3724 : rowsJ2 139 140 72 74 ≤ 6485339427079 := by decide +kernel

theorem rows22250R_3725 : rowsJ2 139 140 74 76 ≤ 4233101100164 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3713
#print axioms SieveCert.rows22250R_3725
