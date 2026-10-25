/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4461–4476 of 4715

File 336 of 351: the parts `rows22250R_4461` … `rows22250R_4476` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 98214 tests: row 174 columns 45–45, row 174 columns 46–46, row 174 columns
47–47, row 174 columns 48–48, row 174 columns 49–49, row 174 columns 50–51, row 174 columns 52–339, row 175 columns
0–35, row 175 columns 36–37, row 175 columns 38–39, row 175 columns 40–40, row 175 columns 41–41, row 175 columns
42–42, row 175 columns 43–43, row 175 columns 44–44, row 175 columns 45–45), each a sum of refined costs (`rows2` or
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

theorem rows22250R_4461 : rowsJ2 174 175 45 46 ≤ 24228399113260 := by decide +kernel

theorem rows22250R_4462 : rowsJ2 174 175 46 47 ≤ 21764857274491 := by decide +kernel

theorem rows22250R_4463 : rowsJ2 174 175 47 48 ≤ 19456610768451 := by decide +kernel

theorem rows22250R_4464 : rowsJ2 174 175 48 49 ≤ 17298224043541 := by decide +kernel

theorem rows22250R_4465 : rowsJ2 174 175 49 50 ≤ 15284682457425 := by decide +kernel

theorem rows22250R_4466 : rowsJ2 174 175 50 52 ≤ 25085398731431 := by decide +kernel

theorem rows22250R_4467 : rowsJ2 174 175 52 340 ≤ 2826452595037867 := by decide +kernel

theorem rows22250R_4468 : rowsJ2 175 176 0 36 ≤ 21324826850506 := by decide +kernel

theorem rows22250R_4469 : rowsJ2 175 176 36 38 ≤ 20963247268263 := by decide +kernel

theorem rows22250R_4470 : rowsJ2 175 176 38 40 ≤ 27240126815394 := by decide +kernel

theorem rows22250R_4471 : rowsJ2 175 176 40 41 ≤ 16165042013888 := by decide +kernel

theorem rows22250R_4472 : rowsJ2 175 176 41 42 ≤ 17957899911948 := by decide +kernel

theorem rows22250R_4473 : rowsJ2 175 176 42 43 ≤ 19819914412104 := by decide +kernel

theorem rows22250R_4474 : rowsJ2 175 176 43 44 ≤ 21749065384209 := by decide +kernel

theorem rows22250R_4475 : rowsJ2 175 176 44 45 ≤ 23743631320395 := by decide +kernel

theorem rows22250R_4476 : rowsJ2 175 176 45 46 ≤ 23485638518509 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4461
#print axioms SieveCert.rows22250R_4476
