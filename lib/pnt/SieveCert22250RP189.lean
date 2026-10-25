/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1952–1969 of 5796

File 189 of 465: the parts `rows22250R_1952` … `rows22250R_1969` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (18 parts, 97167 tests: row 81 columns 69–69, row 81 columns 70–70, row 81 columns
71–71, row 81 columns 72–72, row 81 columns 73–73, row 81 columns 74–74, row 81 columns 75–76, row 81 columns 77–78,
row 81 columns 79–80, row 81 columns 81–359, row 82 columns 0–17, row 82 columns 18–19, row 82 columns 20–21, row 82
columns 22–22, row 82 columns 23–23, row 82 columns 24–24, row 82 columns 25–25, row 82 columns 26–26), each a sum
of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1952 : rowsJ2 81 82 69 70 ≤ 96441760404 := by decide +kernel

theorem rows22250R_1953 : rowsJ2 81 82 70 71 ≤ 48898368091 := by decide +kernel

theorem rows22250R_1954 : rowsJ2 81 82 71 72 ≤ 0 := by decide +kernel

theorem rows22250R_1955 : rowsJ2 81 82 72 73 ≤ 0 := by decide +kernel

theorem rows22250R_1956 : rowsJ2 81 82 73 74 ≤ 0 := by decide +kernel

theorem rows22250R_1957 : rowsJ2 81 82 74 75 ≤ 0 := by decide +kernel

theorem rows22250R_1958 : rowsJ2 81 82 75 77 ≤ 0 := by decide +kernel

theorem rows22250R_1959 : rowsJ2 81 82 77 79 ≤ 0 := by decide +kernel

theorem rows22250R_1960 : rowsJ2 81 82 79 81 ≤ 58822597809 := by decide +kernel

theorem rows22250R_1961 : rowsJ2 81 82 81 360 ≤ 175744267485 := by decide +kernel

theorem rows22250R_1962 : rowsJ2 82 83 0 18 ≤ 156963089881 := by decide +kernel

theorem rows22250R_1963 : rowsJ2 82 83 18 20 ≤ 2860549392 := by decide +kernel

theorem rows22250R_1964 : rowsJ2 82 83 20 22 ≤ 13434682397 := by decide +kernel

theorem rows22250R_1965 : rowsJ2 82 83 22 23 ≤ 5637371022 := by decide +kernel

theorem rows22250R_1966 : rowsJ2 82 83 23 24 ≤ 4234918260 := by decide +kernel

theorem rows22250R_1967 : rowsJ2 82 83 24 25 ≤ 2809131900 := by decide +kernel

theorem rows22250R_1968 : rowsJ2 82 83 25 26 ≤ 1401406332 := by decide +kernel

theorem rows22250R_1969 : rowsJ2 82 83 26 27 ≤ 696673629 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1952
#print axioms SieveCert.rows22250R_1969
