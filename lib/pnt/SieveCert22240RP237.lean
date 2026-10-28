/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2801–2816 of 5066

File 237 of 387: the parts `rows22240R_2801` … `rows22240R_2816` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 93733 in units of a depth-4 test: row 101 columns 0–16, row 101 columns
17–26, row 101 columns 27–32, row 101 columns 33–34, row 101 columns 35–36, row 101 columns 37–37, row 101 columns
38–38, row 101 columns 39–39, row 101 columns 40–40, row 101 columns 41–41, row 101 columns 42–42, row 101 columns
43–43, row 101 columns 44–44, row 101 columns 45–45, row 101 columns 46–46, row 101 columns 47–48), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2801 : rowsJ2 101 102 0 17 ≤ 0 := by decide +kernel

theorem rows22240R_2802 : rowsJ2 101 102 17 27 ≤ 0 := by decide +kernel

theorem rows22240R_2803 : rowsJ2 101 102 27 33 ≤ 4888972950181 := by decide +kernel

theorem rows22240R_2804 : rowsJ2 101 102 33 35 ≤ 9152373519407 := by decide +kernel

theorem rows22240R_2805 : rowsJ2 101 102 35 37 ≤ 15963769116558 := by decide +kernel

theorem rows22240R_2806 : rowsJ2 101 102 37 38 ≤ 11166700404991 := by decide +kernel

theorem rows22240R_2807 : rowsJ2 101 102 38 39 ≤ 12641145993232 := by decide +kernel

theorem rows22240R_2808 : rowsJ2 101 102 39 40 ≤ 14126028851199 := by decide +kernel

theorem rows22240R_2809 : rowsJ2 101 102 40 41 ≤ 15663469063551 := by decide +kernel

theorem rows22240R_2810 : rowsJ2 101 102 41 42 ≤ 15423493087340 := by decide +kernel

theorem rows22240R_2811 : rowsJ2 101 102 42 43 ≤ 13586664675348 := by decide +kernel

theorem rows22240R_2812 : rowsJ2 101 102 43 44 ≤ 11936027833485 := by decide +kernel

theorem rows22240R_2813 : rowsJ2 101 102 44 45 ≤ 10304297431794 := by decide +kernel

theorem rows22240R_2814 : rowsJ2 101 102 45 46 ≤ 8752557702846 := by decide +kernel

theorem rows22240R_2815 : rowsJ2 101 102 46 47 ≤ 7280776602653 := by decide +kernel

theorem rows22240R_2816 : rowsJ2 101 102 47 49 ≤ 10567420018489 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2801
#print axioms SieveCert.rows22240R_2816
