/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 569–578 of 5066

File 58 of 387: the parts `rows22240R_569` … `rows22240R_578` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (10 parts, work 98977 in units of a depth-4 test: row 50 columns 41–41, row 50 columns
42–42, row 50 columns 43–43, row 50 columns 44–44, row 50 columns 45–45, row 50 columns 46–46, row 50 columns 47–47,
row 50 columns 48–48, row 50 columns 49–49, row 50 columns 50–339), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_569 : rowsJ2 50 51 41 42 ≤ 1891234680 := by decide +kernel

theorem rows22240R_570 : rowsJ2 50 51 42 43 ≤ 1896753771 := by decide +kernel

theorem rows22240R_571 : rowsJ2 50 51 43 44 ≤ 1268706993 := by decide +kernel

theorem rows22240R_572 : rowsJ2 50 51 44 45 ≤ 78475820038 := by decide +kernel

theorem rows22240R_573 : rowsJ2 50 51 45 46 ≤ 226413807239 := by decide +kernel

theorem rows22240R_574 : rowsJ2 50 51 46 47 ≤ 440934106238 := by decide +kernel

theorem rows22240R_575 : rowsJ2 50 51 47 48 ≤ 940061160093 := by decide +kernel

theorem rows22240R_576 : rowsJ2 50 51 48 49 ≤ 1795986615561 := by decide +kernel

theorem rows22240R_577 : rowsJ2 50 51 49 50 ≤ 2769647068640 := by decide +kernel

theorem rows22240R_578 : rowsJ2 50 51 50 340 ≤ 3779162537429 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_569
#print axioms SieveCert.rows22240R_578
