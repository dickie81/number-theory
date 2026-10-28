/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3834–3845 of 4715

File 294 of 351: the parts `rows22250R_3834` … `rows22250R_3845` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, work 95688 in units of a depth-4 test: row 144 columns 53–53, row 144
columns 54–54, row 144 columns 55–55, row 144 columns 56–56, row 144 columns 57–57, row 144 columns 58–58, row 144
columns 59–59, row 144 columns 60–60, row 144 columns 61–61, row 144 columns 62–62, row 144 columns 63–63, row 144
columns 64–64), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3834 : rowsJ2 144 145 53 54 ≤ 6643524855734 := by decide +kernel

theorem rows22250R_3835 : rowsJ2 144 145 54 55 ≤ 7552272316916 := by decide +kernel

theorem rows22250R_3836 : rowsJ2 144 145 55 56 ≤ 8505990922786 := by decide +kernel

theorem rows22250R_3837 : rowsJ2 144 145 56 57 ≤ 9503010428213 := by decide +kernel

theorem rows22250R_3838 : rowsJ2 144 145 57 58 ≤ 10541802801509 := by decide +kernel

theorem rows22250R_3839 : rowsJ2 144 145 58 59 ≤ 11620975110541 := by decide +kernel

theorem rows22250R_3840 : rowsJ2 144 145 59 60 ≤ 12739263070413 := by decide +kernel

theorem rows22250R_3841 : rowsJ2 144 145 60 61 ≤ 13875314405176 := by decide +kernel

theorem rows22250R_3842 : rowsJ2 144 145 61 62 ≤ 12503420990225 := by decide +kernel

theorem rows22250R_3843 : rowsJ2 144 145 62 63 ≤ 11194643042755 := by decide +kernel

theorem rows22250R_3844 : rowsJ2 144 145 63 64 ≤ 9966963367197 := by decide +kernel

theorem rows22250R_3845 : rowsJ2 144 145 64 65 ≤ 8818307070923 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3834
#print axioms SieveCert.rows22250R_3845
