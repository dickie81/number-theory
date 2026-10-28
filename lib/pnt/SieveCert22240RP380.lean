/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4941–4957 of 5066

File 380 of 387: the parts `rows22240R_4941` … `rows22240R_4957` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 95679 in units of a depth-4 test: row 185 columns 35–36, row 185
columns 37–37, row 185 columns 38–38, row 185 columns 39–39, row 185 columns 40–40, row 185 columns 41–41, row 185
columns 42–42, row 185 columns 43–339, row 186 columns 0–32, row 186 columns 33–34, row 186 columns 35–36, row 186
columns 37–37, row 186 columns 38–38, row 186 columns 39–39, row 186 columns 40–40, row 186 columns 41–41, row 186
columns 42–339), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4941 : rowsJ2 185 186 35 37 ≤ 35464367407596 := by decide +kernel

theorem rows22240R_4942 : rowsJ2 185 186 37 38 ≤ 23373735175877 := by decide +kernel

theorem rows22240R_4943 : rowsJ2 185 186 38 39 ≤ 25708585499696 := by decide +kernel

theorem rows22240R_4944 : rowsJ2 185 186 39 40 ≤ 28124480408806 := by decide +kernel

theorem rows22240R_4945 : rowsJ2 185 186 40 41 ≤ 30619807085805 := by decide +kernel

theorem rows22240R_4946 : rowsJ2 185 186 41 42 ≤ 30270419458447 := by decide +kernel

theorem rows22240R_4947 : rowsJ2 185 186 42 43 ≤ 27172597829447 := by decide +kernel

theorem rows22240R_4948 : rowsJ2 185 186 43 340 ≤ 3813975764501421 := by decide +kernel

theorem rows22240R_4949 : rowsJ2 186 187 0 33 ≤ 24286784507295 := by decide +kernel

theorem rows22240R_4950 : rowsJ2 186 187 33 35 ≤ 25116284352248 := by decide +kernel

theorem rows22240R_4951 : rowsJ2 186 187 35 37 ≤ 38391015175597 := by decide +kernel

theorem rows22240R_4952 : rowsJ2 186 187 37 38 ≤ 25137986912298 := by decide +kernel

theorem rows22240R_4953 : rowsJ2 186 187 38 39 ≤ 27568485620850 := by decide +kernel

theorem rows22240R_4954 : rowsJ2 186 187 39 40 ≤ 30081030788450 := by decide +kernel

theorem rows22240R_4955 : rowsJ2 186 187 40 41 ≤ 32674218826717 := by decide +kernel

theorem rows22240R_4956 : rowsJ2 186 187 41 42 ≤ 29394550694970 := by decide +kernel

theorem rows22240R_4957 : rowsJ2 186 187 42 340 ≤ 3949394751147649 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4941
#print axioms SieveCert.rows22240R_4957
