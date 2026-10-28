/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 5038–5052 of 5066

File 386 of 387: the parts `rows22240R_5038` … `rows22240R_5052` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 97520 in units of a depth-4 test: rows 232–233, rows 234–235, rows
236–237, rows 238–239, rows 240–241, rows 242–243, rows 244–245, rows 246–247, rows 248–249, rows 250–251, rows
252–253, rows 254–255, rows 256–257, rows 258–259, rows 260–261), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_5038 : rows2 232 234 ≤ 18319703917729379 := by decide +kernel

theorem rows22240R_5039 : rows2 234 236 ≤ 18821931282974415 := by decide +kernel

theorem rows22240R_5040 : rows2 236 238 ≤ 19134376449980482 := by decide +kernel

theorem rows22240R_5041 : rows2 238 240 ≤ 19240120978867144 := by decide +kernel

theorem rows22240R_5042 : rows2 240 242 ≤ 19345144087572105 := by decide +kernel

theorem rows22240R_5043 : rows2 242 244 ≤ 19449271251055066 := by decide +kernel

theorem rows22240R_5044 : rows2 244 246 ≤ 19552930022345825 := by decide +kernel

theorem rows22240R_5045 : rows2 246 248 ≤ 19658752281940006 := by decide +kernel

theorem rows22240R_5046 : rows2 248 250 ≤ 19767160166634020 := by decide +kernel

theorem rows22240R_5047 : rows2 250 252 ≤ 19877701932470429 := by decide +kernel

theorem rows22240R_5048 : rows2 252 254 ≤ 19990317983798561 := by decide +kernel

theorem rows22240R_5049 : rows2 254 256 ≤ 20104879770614349 := by decide +kernel

theorem rows22240R_5050 : rows2 256 258 ≤ 20220859269054461 := by decide +kernel

theorem rows22240R_5051 : rows2 258 260 ≤ 20338101773912846 := by decide +kernel

theorem rows22240R_5052 : rows2 260 262 ≤ 20456383565030335 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_5038
#print axioms SieveCert.rows22240R_5052
