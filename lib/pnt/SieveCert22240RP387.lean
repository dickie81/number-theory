/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 5053–5065 of 5066

File 387 of 387: the parts `rows22240R_5053` … `rows22240R_5065` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 80639 in units of a depth-4 test: rows 262–263, rows 264–265, rows
266–267, rows 268–269, rows 270–271, rows 272–319, rows 320–323, rows 324–326, rows 327–329, rows 330–332, rows
333–335, rows 336–337, rows 338–339), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_5053 : rows2 262 264 ≤ 20575053282052657 := by decide +kernel

theorem rows22240R_5054 : rows2 264 266 ≤ 20693834038903277 := by decide +kernel

theorem rows22240R_5055 : rows2 266 268 ≤ 20812346454560228 := by decide +kernel

theorem rows22240R_5056 : rows2 268 270 ≤ 20929772300519185 := by decide +kernel

theorem rows22240R_5057 : rows2 270 272 ≤ 21045637726232298 := by decide +kernel

theorem rows22240R_5058 : rows2 272 320 ≤ 31845994466942905 := by decide +kernel

theorem rows22240R_5059 : rows2 320 324 ≤ 42199182564926709 := by decide +kernel

theorem rows22240R_5060 : rows2 324 327 ≤ 33354904202215044 := by decide +kernel

theorem rows22240R_5061 : rows2 327 330 ≤ 34992660223594000 := by decide +kernel

theorem rows22240R_5062 : rows2 330 333 ≤ 36706427778246277 := by decide +kernel

theorem rows22240R_5063 : rows2 333 336 ≤ 38634099026240917 := by decide +kernel

theorem rows22240R_5064 : rows2 336 338 ≤ 26885048590188345 := by decide +kernel

theorem rows22240R_5065 : rows2 338 340 ≤ 27862890399097830 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_5053
#print axioms SieveCert.rows22240R_5065
