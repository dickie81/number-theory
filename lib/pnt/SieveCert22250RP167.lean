/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1677–1684 of 5796

File 167 of 465: the parts `rows22250R_1677` … `rows22250R_1684` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 97174 tests: row 76 columns 57–57, row 76 columns 58–58, row 76 columns
59–59, row 76 columns 60–60, row 76 columns 61–61, row 76 columns 62–62, row 76 columns 63–63, row 76 columns
64–64), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_1677 : rowsJ2 76 77 57 58 ≤ 4346166835319 := by decide +kernel

theorem rows22250R_1678 : rowsJ2 76 77 58 59 ≤ 4121484307744 := by decide +kernel

theorem rows22250R_1679 : rowsJ2 76 77 59 60 ≤ 3849812943025 := by decide +kernel

theorem rows22250R_1680 : rowsJ2 76 77 60 61 ≤ 3622956812273 := by decide +kernel

theorem rows22250R_1681 : rowsJ2 76 77 61 62 ≤ 3348220854548 := by decide +kernel

theorem rows22250R_1682 : rowsJ2 76 77 62 63 ≤ 3118657538987 := by decide +kernel

theorem rows22250R_1683 : rowsJ2 76 77 63 64 ≤ 2840278721172 := by decide +kernel

theorem rows22250R_1684 : rowsJ2 76 77 64 65 ≤ 2607464857078 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1677
#print axioms SieveCert.rows22250R_1684
