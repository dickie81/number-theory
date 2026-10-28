/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2306–2319 of 5066

File 200 of 387: the parts `rows22240R_2306` … `rows22240R_2319` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 94713 in units of a depth-4 test: row 90 columns 33–35, row 90 columns
36–37, row 90 columns 38–39, row 90 columns 40–40, row 90 columns 41–41, row 90 columns 42–42, row 90 columns 43–43,
row 90 columns 44–44, row 90 columns 45–45, row 90 columns 46–46, row 90 columns 47–47, row 90 columns 48–48, row 90
columns 49–49, row 90 columns 50–50), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22240R_2306 : rowsJ2 90 91 33 36 ≤ 5538628323146 := by decide +kernel

theorem rows22240R_2307 : rowsJ2 90 91 36 38 ≤ 9292185039424 := by decide +kernel

theorem rows22240R_2308 : rowsJ2 90 91 38 40 ≤ 14505369678258 := by decide +kernel

theorem rows22240R_2309 : rowsJ2 90 91 40 41 ≤ 9153911227220 := by decide +kernel

theorem rows22240R_2310 : rowsJ2 90 91 41 42 ≤ 10446473813548 := by decide +kernel

theorem rows22240R_2311 : rowsJ2 90 91 42 43 ≤ 11753988371090 := by decide +kernel

theorem rows22240R_2312 : rowsJ2 90 91 43 44 ≤ 13168258945353 := by decide +kernel

theorem rows22240R_2313 : rowsJ2 90 91 44 45 ≤ 14573845851846 := by decide +kernel

theorem rows22240R_2314 : rowsJ2 90 91 45 46 ≤ 15802640499376 := by decide +kernel

theorem rows22240R_2315 : rowsJ2 90 91 46 47 ≤ 16909459517857 := by decide +kernel

theorem rows22240R_2316 : rowsJ2 90 91 47 48 ≤ 15065407812368 := by decide +kernel

theorem rows22240R_2317 : rowsJ2 90 91 48 49 ≤ 10392656451836 := by decide +kernel

theorem rows22240R_2318 : rowsJ2 90 91 49 50 ≤ 6143777287205 := by decide +kernel

theorem rows22240R_2319 : rowsJ2 90 91 50 51 ≤ 2906991871141 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2306
#print axioms SieveCert.rows22240R_2319
