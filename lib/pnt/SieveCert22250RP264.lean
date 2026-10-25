/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3413–3427 of 4715

File 264 of 351: the parts `rows22250R_3413` … `rows22250R_3427` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 95152 tests: row 128 columns 68–68, row 128 columns 69–69, row 128 columns
70–70, row 128 columns 71–71, row 128 columns 72–72, row 128 columns 73–73, row 128 columns 74–74, row 128 columns
75–76, row 128 columns 77–78, row 128 columns 79–82, row 128 columns 83–86, row 128 columns 87–89, row 128 columns
90–339, row 129 columns 0–24, row 129 columns 25–29), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3413 : rowsJ2 128 129 68 69 ≤ 7288264103278 := by decide +kernel

theorem rows22250R_3414 : rowsJ2 128 129 69 70 ≤ 6452918409920 := by decide +kernel

theorem rows22250R_3415 : rowsJ2 128 129 70 71 ≤ 5662499497505 := by decide +kernel

theorem rows22250R_3416 : rowsJ2 128 129 71 72 ≤ 4938750275069 := by decide +kernel

theorem rows22250R_3417 : rowsJ2 128 129 72 73 ≤ 4256694914346 := by decide +kernel

theorem rows22250R_3418 : rowsJ2 128 129 73 74 ≤ 3638538839562 := by decide +kernel

theorem rows22250R_3419 : rowsJ2 128 129 74 75 ≤ 3059164499971 := by decide +kernel

theorem rows22250R_3420 : rowsJ2 128 129 75 77 ≤ 4600718630808 := by decide +kernel

theorem rows22250R_3421 : rowsJ2 128 129 77 79 ≤ 2885351733344 := by decide +kernel

theorem rows22250R_3422 : rowsJ2 128 129 79 83 ≤ 2774995819476 := by decide +kernel

theorem rows22250R_3423 : rowsJ2 128 129 83 87 ≤ 12368652398922 := by decide +kernel

theorem rows22250R_3424 : rowsJ2 128 129 87 90 ≤ 22756570786121 := by decide +kernel

theorem rows22250R_3425 : rowsJ2 128 129 90 340 ≤ 805803203102982 := by decide +kernel

theorem rows22250R_3426 : rowsJ2 129 130 0 25 ≤ 5312562512354 := by decide +kernel

theorem rows22250R_3427 : rowsJ2 129 130 25 30 ≤ 15703085658839 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3413
#print axioms SieveCert.rows22250R_3427
