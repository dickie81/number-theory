/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4379–4394 of 4715

File 331 of 351: the parts `rows22250R_4379` … `rows22250R_4394` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 92969 tests: row 169 columns 49–49, row 169 columns 50–50, row 169 columns
51–51, row 169 columns 52–52, row 169 columns 53–53, row 169 columns 54–55, row 169 columns 56–104, row 169 columns
105–339, row 170 columns 0–36, row 170 columns 37–39, row 170 columns 40–41, row 170 columns 42–42, row 170 columns
43–43, row 170 columns 44–44, row 170 columns 45–45, row 170 columns 46–46), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4379 : rowsJ2 169 170 49 50 ≤ 18594604942041 := by decide +kernel

theorem rows22250R_4380 : rowsJ2 169 170 50 51 ≤ 16584933067725 := by decide +kernel

theorem rows22250R_4381 : rowsJ2 169 170 51 52 ≤ 14706670175307 := by decide +kernel

theorem rows22250R_4382 : rowsJ2 169 170 52 53 ≤ 12955725629622 := by decide +kernel

theorem rows22250R_4383 : rowsJ2 169 170 53 54 ≤ 11328328373099 := by decide +kernel

theorem rows22250R_4384 : rowsJ2 169 170 54 56 ≤ 18251598898446 := by decide +kernel

theorem rows22250R_4385 : rowsJ2 169 170 56 105 ≤ 100550491884330 := by decide +kernel

theorem rows22250R_4386 : rowsJ2 169 170 105 340 ≤ 2615032754887280 := by decide +kernel

theorem rows22250R_4387 : rowsJ2 170 171 0 37 ≤ 15114741804303 := by decide +kernel

theorem rows22250R_4388 : rowsJ2 170 171 37 40 ≤ 24344883067810 := by decide +kernel

theorem rows22250R_4389 : rowsJ2 170 171 40 42 ≤ 22998826500424 := by decide +kernel

theorem rows22250R_4390 : rowsJ2 170 171 42 43 ≤ 13745554913161 := by decide +kernel

theorem rows22250R_4391 : rowsJ2 170 171 43 44 ≤ 15332117808196 := by decide +kernel

theorem rows22250R_4392 : rowsJ2 170 171 44 45 ≤ 16982580718591 := by decide +kernel

theorem rows22250R_4393 : rowsJ2 170 171 45 46 ≤ 18694914326955 := by decide +kernel

theorem rows22250R_4394 : rowsJ2 170 171 46 47 ≤ 20467350478252 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4379
#print axioms SieveCert.rows22250R_4394
