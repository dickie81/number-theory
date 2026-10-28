/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2934–2949 of 5066

File 245 of 387: the parts `rows22240R_2934` … `rows22240R_2949` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 94978 in units of a depth-4 test: row 103 columns 96–96, row 103
columns 97–97, row 103 columns 98–98, row 103 columns 99–99, row 103 columns 100–100, row 103 columns 101–101, row
103 columns 102–102, row 103 columns 103–339, row 104 columns 0–17, row 104 columns 18–29, row 104 columns 30–33,
row 104 columns 34–35, row 104 columns 36–36, row 104 columns 37–37, row 104 columns 38–38, row 104 columns 39–39),
each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2934 : rowsJ2 103 104 96 97 ≤ 6877925753307 := by decide +kernel

theorem rows22240R_2935 : rowsJ2 103 104 97 98 ≤ 7863347235608 := by decide +kernel

theorem rows22240R_2936 : rowsJ2 103 104 98 99 ≤ 8974806563643 := by decide +kernel

theorem rows22240R_2937 : rowsJ2 103 104 99 100 ≤ 10148741596174 := by decide +kernel

theorem rows22240R_2938 : rowsJ2 103 104 100 101 ≤ 11455676324096 := by decide +kernel

theorem rows22240R_2939 : rowsJ2 103 104 101 102 ≤ 12830913664435 := by decide +kernel

theorem rows22240R_2940 : rowsJ2 103 104 102 103 ≤ 14346990162140 := by decide +kernel

theorem rows22240R_2941 : rowsJ2 103 104 103 340 ≤ 15938052592583 := by decide +kernel

theorem rows22240R_2942 : rowsJ2 104 105 0 18 ≤ 0 := by decide +kernel

theorem rows22240R_2943 : rowsJ2 104 105 18 30 ≤ 528736070989 := by decide +kernel

theorem rows22240R_2944 : rowsJ2 104 105 30 34 ≤ 12410131479517 := by decide +kernel

theorem rows22240R_2945 : rowsJ2 104 105 34 36 ≤ 15469858249745 := by decide +kernel

theorem rows22240R_2946 : rowsJ2 104 105 36 37 ≤ 10734083390533 := by decide +kernel

theorem rows22240R_2947 : rowsJ2 104 105 37 38 ≤ 12822203030746 := by decide +kernel

theorem rows22240R_2948 : rowsJ2 104 105 38 39 ≤ 14465079422406 := by decide +kernel

theorem rows22240R_2949 : rowsJ2 104 105 39 40 ≤ 16161421316718 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2934
#print axioms SieveCert.rows22240R_2949
