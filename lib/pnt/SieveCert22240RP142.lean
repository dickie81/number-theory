/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1507–1524 of 5066

File 142 of 387: the parts `rows22240R_1507` … `rows22240R_1524` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (18 parts, work 97800 in units of a depth-4 test: row 73 columns 24–24, row 73 columns
25–25, row 73 columns 26–26, row 73 columns 27–27, row 73 columns 28–28, row 73 columns 29–29, row 73 columns 30–30,
row 73 columns 31–31, row 73 columns 32–32, row 73 columns 33–34, row 73 columns 35–36, row 73 columns 37–38, row 73
columns 39–40, row 73 columns 41–41, row 73 columns 42–42, row 73 columns 43–43, row 73 columns 44–44, row 73
columns 45–45), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22240R_1507 : rowsJ2 73 74 24 25 ≤ 5613516894 := by decide +kernel

theorem rows22240R_1508 : rowsJ2 73 74 25 26 ≤ 3767889909 := by decide +kernel

theorem rows22240R_1509 : rowsJ2 73 74 26 27 ≤ 3773282986 := by decide +kernel

theorem rows22240R_1510 : rowsJ2 73 74 27 28 ≤ 1920842495 := by decide +kernel

theorem rows22240R_1511 : rowsJ2 73 74 28 29 ≤ 1924656634 := by decide +kernel

theorem rows22240R_1512 : rowsJ2 73 74 29 30 ≤ 964646904 := by decide +kernel

theorem rows22240R_1513 : rowsJ2 73 74 30 31 ≤ 967259597 := by decide +kernel

theorem rows22240R_1514 : rowsJ2 73 74 31 32 ≤ 0 := by decide +kernel

theorem rows22240R_1515 : rowsJ2 73 74 32 33 ≤ 0 := by decide +kernel

theorem rows22240R_1516 : rowsJ2 73 74 33 35 ≤ 0 := by decide +kernel

theorem rows22240R_1517 : rowsJ2 73 74 35 37 ≤ 0 := by decide +kernel

theorem rows22240R_1518 : rowsJ2 73 74 37 39 ≤ 0 := by decide +kernel

theorem rows22240R_1519 : rowsJ2 73 74 39 41 ≤ 0 := by decide +kernel

theorem rows22240R_1520 : rowsJ2 73 74 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_1521 : rowsJ2 73 74 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_1522 : rowsJ2 73 74 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_1523 : rowsJ2 73 74 44 45 ≤ 62360932054 := by decide +kernel

theorem rows22240R_1524 : rowsJ2 73 74 45 46 ≤ 182370936003 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1507
#print axioms SieveCert.rows22240R_1524
