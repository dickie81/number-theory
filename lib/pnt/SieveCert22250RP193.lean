/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2004–2020 of 5796

File 193 of 465: the parts `rows22250R_2004` … `rows22250R_2020` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 97796 tests: row 82 columns 70–70, row 82 columns 71–71, row 82 columns
72–72, row 82 columns 73–73, row 82 columns 74–75, row 82 columns 76–77, row 82 columns 78–79, row 82 columns 80–81,
row 82 columns 82–359, row 83 columns 0–17, row 83 columns 18–19, row 83 columns 20–21, row 83 columns 22–22, row 83
columns 23–23, row 83 columns 24–24, row 83 columns 25–26, row 83 columns 27–28), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2004 : rowsJ2 82 83 70 71 ≤ 0 := by decide +kernel

theorem rows22250R_2005 : rowsJ2 82 83 71 72 ≤ 0 := by decide +kernel

theorem rows22250R_2006 : rowsJ2 82 83 72 73 ≤ 0 := by decide +kernel

theorem rows22250R_2007 : rowsJ2 82 83 73 74 ≤ 0 := by decide +kernel

theorem rows22250R_2008 : rowsJ2 82 83 74 76 ≤ 0 := by decide +kernel

theorem rows22250R_2009 : rowsJ2 82 83 76 78 ≤ 0 := by decide +kernel

theorem rows22250R_2010 : rowsJ2 82 83 78 80 ≤ 0 := by decide +kernel

theorem rows22250R_2011 : rowsJ2 82 83 80 82 ≤ 232787130074 := by decide +kernel

theorem rows22250R_2012 : rowsJ2 82 83 82 360 ≤ 362283422883 := by decide +kernel

theorem rows22250R_2013 : rowsJ2 83 84 0 18 ≤ 119443011945 := by decide +kernel

theorem rows22250R_2014 : rowsJ2 83 84 18 20 ≤ 5023886726 := by decide +kernel

theorem rows22250R_2015 : rowsJ2 83 84 20 22 ≤ 12083734511 := by decide +kernel

theorem rows22250R_2016 : rowsJ2 83 84 22 23 ≤ 4261567541 := by decide +kernel

theorem rows22250R_2017 : rowsJ2 83 84 23 24 ≤ 2826275669 := by decide +kernel

theorem rows22250R_2018 : rowsJ2 83 84 24 25 ≤ 1409700048 := by decide +kernel

theorem rows22250R_2019 : rowsJ2 83 84 25 27 ≤ 700671382 := by decide +kernel

theorem rows22250R_2020 : rowsJ2 83 84 27 29 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2004
#print axioms SieveCert.rows22250R_2020
