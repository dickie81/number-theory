/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2899–2914 of 5066

File 243 of 387: the parts `rows22240R_2899` … `rows22240R_2914` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 94370 in units of a depth-4 test: row 103 columns 36–36, row 103
columns 37–37, row 103 columns 38–38, row 103 columns 39–39, row 103 columns 40–40, row 103 columns 41–41, row 103
columns 42–42, row 103 columns 43–43, row 103 columns 44–44, row 103 columns 45–46, row 103 columns 47–48, row 103
columns 49–50, row 103 columns 51–53, row 103 columns 54–58, row 103 columns 59–66, row 103 columns 67–72), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22240R_2899 : rowsJ2 103 104 36 37 ≤ 10242693967722 := by decide +kernel

theorem rows22240R_2900 : rowsJ2 103 104 37 38 ≤ 12232505047262 := by decide +kernel

theorem rows22240R_2901 : rowsJ2 103 104 38 39 ≤ 13781914426772 := by decide +kernel

theorem rows22240R_2902 : rowsJ2 103 104 39 40 ≤ 15447967630317 := by decide +kernel

theorem rows22240R_2903 : rowsJ2 103 104 40 41 ≤ 15207823295900 := by decide +kernel

theorem rows22240R_2904 : rowsJ2 103 104 41 42 ≤ 13310138025888 := by decide +kernel

theorem rows22240R_2905 : rowsJ2 103 104 42 43 ≤ 11542482366242 := by decide +kernel

theorem rows22240R_2906 : rowsJ2 103 104 43 44 ≤ 9961973180810 := by decide +kernel

theorem rows22240R_2907 : rowsJ2 103 104 44 45 ≤ 8463187212460 := by decide +kernel

theorem rows22240R_2908 : rowsJ2 103 104 45 47 ≤ 12757191908373 := by decide +kernel

theorem rows22240R_2909 : rowsJ2 103 104 47 49 ≤ 7848163758386 := by decide +kernel

theorem rows22240R_2910 : rowsJ2 103 104 49 51 ≤ 4299349000651 := by decide +kernel

theorem rows22240R_2911 : rowsJ2 103 104 51 54 ≤ 2543109724151 := by decide +kernel

theorem rows22240R_2912 : rowsJ2 103 104 54 59 ≤ 184484911626 := by decide +kernel

theorem rows22240R_2913 : rowsJ2 103 104 59 67 ≤ 0 := by decide +kernel

theorem rows22240R_2914 : rowsJ2 103 104 67 73 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2899
#print axioms SieveCert.rows22240R_2914
