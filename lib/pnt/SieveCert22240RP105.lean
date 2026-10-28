/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1066–1076 of 5066

File 105 of 387: the parts `rows22240R_1066` … `rows22240R_1076` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 93786 in units of a depth-4 test: row 63 columns 61–61, row 63 columns
62–62, row 63 columns 63–339, row 64 columns 0–16, row 64 columns 17–20, row 64 columns 21–22, row 64 columns 23–23,
row 64 columns 24–24, row 64 columns 25–25, row 64 columns 26–26, row 64 columns 27–27), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1066 : rowsJ2 63 64 61 62 ≤ 11865576431575 := by decide +kernel

theorem rows22240R_1067 : rowsJ2 63 64 62 63 ≤ 11360443987890 := by decide +kernel

theorem rows22240R_1068 : rowsJ2 63 64 63 340 ≤ 10843763116239 := by decide +kernel

theorem rows22240R_1069 : rowsJ2 64 65 0 17 ≤ 2390515076710 := by decide +kernel

theorem rows22240R_1070 : rowsJ2 64 65 17 21 ≤ 381401837027 := by decide +kernel

theorem rows22240R_1071 : rowsJ2 64 65 21 23 ≤ 87472590208 := by decide +kernel

theorem rows22240R_1072 : rowsJ2 64 65 23 24 ≤ 24966131796 := by decide +kernel

theorem rows22240R_1073 : rowsJ2 64 65 24 25 ≤ 16606978238 := by decide +kernel

theorem rows22240R_1074 : rowsJ2 64 65 25 26 ≤ 8317183065 := by decide +kernel

theorem rows22240R_1075 : rowsJ2 64 65 26 27 ≤ 4144847653 := by decide +kernel

theorem rows22240R_1076 : rowsJ2 64 65 27 28 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1066
#print axioms SieveCert.rows22240R_1076
