/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2440–2455 of 5066

File 211 of 387: the parts `rows22240R_2440` … `rows22240R_2455` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 99024 in units of a depth-4 test: row 93 columns 32–35, row 93 columns
36–37, row 93 columns 38–38, row 93 columns 39–39, row 93 columns 40–40, row 93 columns 41–41, row 93 columns 42–42,
row 93 columns 43–43, row 93 columns 44–44, row 93 columns 45–45, row 93 columns 46–46, row 93 columns 47–47, row 93
columns 48–48, row 93 columns 49–49, row 93 columns 50–50, row 93 columns 51–51), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2440 : rowsJ2 93 94 32 36 ≤ 8668130142928 := by decide +kernel

theorem rows22240R_2441 : rowsJ2 93 94 36 38 ≤ 11852296251192 := by decide +kernel

theorem rows22240R_2442 : rowsJ2 93 94 38 39 ≤ 7898778303557 := by decide +kernel

theorem rows22240R_2443 : rowsJ2 93 94 39 40 ≤ 9108617903120 := by decide +kernel

theorem rows22240R_2444 : rowsJ2 93 94 40 41 ≤ 10438735363090 := by decide +kernel

theorem rows22240R_2445 : rowsJ2 93 94 41 42 ≤ 11883091988591 := by decide +kernel

theorem rows22240R_2446 : rowsJ2 93 94 42 43 ≤ 13436156695295 := by decide +kernel

theorem rows22240R_2447 : rowsJ2 93 94 43 44 ≤ 14979898017703 := by decide +kernel

theorem rows22240R_2448 : rowsJ2 93 94 44 45 ≤ 16240554853241 := by decide +kernel

theorem rows22240R_2449 : rowsJ2 93 94 45 46 ≤ 15887849042540 := by decide +kernel

theorem rows22240R_2450 : rowsJ2 93 94 46 47 ≤ 14091780603829 := by decide +kernel

theorem rows22240R_2451 : rowsJ2 93 94 47 48 ≤ 12373972459337 := by decide +kernel

theorem rows22240R_2452 : rowsJ2 93 94 48 49 ≤ 10771750124822 := by decide +kernel

theorem rows22240R_2453 : rowsJ2 93 94 49 50 ≤ 9339089336956 := by decide +kernel

theorem rows22240R_2454 : rowsJ2 93 94 50 51 ≤ 8012408763765 := by decide +kernel

theorem rows22240R_2455 : rowsJ2 93 94 51 52 ≤ 5153854155505 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2440
#print axioms SieveCert.rows22240R_2455
