/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 722–732 of 5796

File 78 of 465: the parts `rows22250R_722` … `rows22250R_732` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 99671 tests: row 55 columns 41–41, row 55 columns 42–42, row 55 columns
43–43, row 55 columns 44–44, row 55 columns 45–45, row 55 columns 46–46, row 55 columns 47–47, row 55 columns 48–48,
row 55 columns 49–49, row 55 columns 50–50, row 55 columns 51–51), each a sum of refined costs (`rows2` or `rowsJ2`)
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

theorem rows22250R_722 : rowsJ2 55 56 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_723 : rowsJ2 55 56 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_724 : rowsJ2 55 56 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_725 : rowsJ2 55 56 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_726 : rowsJ2 55 56 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_727 : rowsJ2 55 56 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_728 : rowsJ2 55 56 47 48 ≤ 117841707180 := by decide +kernel

theorem rows22250R_729 : rowsJ2 55 56 48 49 ≤ 528147553087 := by decide +kernel

theorem rows22250R_730 : rowsJ2 55 56 49 50 ≤ 983479739285 := by decide +kernel

theorem rows22250R_731 : rowsJ2 55 56 50 51 ≤ 1479182600552 := by decide +kernel

theorem rows22250R_732 : rowsJ2 55 56 51 52 ≤ 2129278483457 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_722
#print axioms SieveCert.rows22250R_732
