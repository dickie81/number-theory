/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 16–30 of 5796

File 2 of 465: the parts `rows22250R_16` … `rows22250R_30` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 95991 tests: row 19 columns 0–13, row 19 columns 14–16, row 19 columns
17–18, row 19 columns 19–359, row 20 columns 0–13, row 20 columns 14–16, row 20 columns 17–18, row 20 columns 19–19,
row 20 columns 20–359, row 21 columns 0–13, row 21 columns 14–16, row 21 columns 17–18, row 21 columns 19–19, row 21
columns 20–20, row 21 columns 21–359), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_16 : rowsJ2 19 20 0 14 ≤ 2402562026349 := by decide +kernel

theorem rows22250R_17 : rowsJ2 19 20 14 17 ≤ 548583051010 := by decide +kernel

theorem rows22250R_18 : rowsJ2 19 20 17 19 ≤ 780088473966 := by decide +kernel

theorem rows22250R_19 : rowsJ2 19 20 19 360 ≤ 670940401425 := by decide +kernel

theorem rows22250R_20 : rowsJ2 20 21 0 14 ≤ 2178523618002 := by decide +kernel

theorem rows22250R_21 : rowsJ2 20 21 14 17 ≤ 503088688391 := by decide +kernel

theorem rows22250R_22 : rowsJ2 20 21 17 19 ≤ 820322036081 := by decide +kernel

theorem rows22250R_23 : rowsJ2 20 21 19 20 ≤ 699226740218 := by decide +kernel

theorem rows22250R_24 : rowsJ2 20 21 20 360 ≤ 909339379653 := by decide +kernel

theorem rows22250R_25 : rowsJ2 21 22 0 14 ≤ 1967677631214 := by decide +kernel

theorem rows22250R_26 : rowsJ2 21 22 14 17 ≤ 479513136630 := by decide +kernel

theorem rows22250R_27 : rowsJ2 21 22 17 19 ≤ 864977009106 := by decide +kernel

theorem rows22250R_28 : rowsJ2 21 22 19 20 ≤ 719366068162 := by decide +kernel

theorem rows22250R_29 : rowsJ2 21 22 20 21 ≤ 939424211033 := by decide +kernel

theorem rows22250R_30 : rowsJ2 21 22 21 360 ≤ 1164714884906 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_16
#print axioms SieveCert.rows22250R_30
