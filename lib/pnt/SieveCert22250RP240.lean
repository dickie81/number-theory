/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3048–3063 of 4715

File 240 of 351: the parts `rows22250R_3048` … `rows22250R_3063` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 99708 in units of a depth-4 test: row 113 columns 80–82, row 113
columns 83–85, row 113 columns 86–88, row 113 columns 89–90, row 113 columns 91–92, row 113 columns 93–94, row 113
columns 95–95, row 113 columns 96–96, row 113 columns 97–339, row 114 columns 0–26, row 114 columns 27–29, row 114
columns 30–31, row 114 columns 32–33, row 114 columns 34–35, row 114 columns 36–38, row 114 columns 39–42), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3048 : rowsJ2 113 114 80 83 ≤ 195278450554 := by decide +kernel

theorem rows22250R_3049 : rowsJ2 113 114 83 86 ≤ 2431870473362 := by decide +kernel

theorem rows22250R_3050 : rowsJ2 113 114 86 89 ≤ 6941510410126 := by decide +kernel

theorem rows22250R_3051 : rowsJ2 113 114 89 91 ≤ 8258005669216 := by decide +kernel

theorem rows22250R_3052 : rowsJ2 113 114 91 93 ≤ 12017999052728 := by decide +kernel

theorem rows22250R_3053 : rowsJ2 113 114 93 95 ≤ 16561154589004 := by decide +kernel

theorem rows22250R_3054 : rowsJ2 113 114 95 96 ≤ 10236633912947 := by decide +kernel

theorem rows22250R_3055 : rowsJ2 113 114 96 97 ≤ 11705549760670 := by decide +kernel

theorem rows22250R_3056 : rowsJ2 113 114 97 340 ≤ 1636510177787873 := by decide +kernel

theorem rows22250R_3057 : rowsJ2 114 115 0 27 ≤ 1177812217615 := by decide +kernel

theorem rows22250R_3058 : rowsJ2 114 115 27 30 ≤ 8640227394970 := by decide +kernel

theorem rows22250R_3059 : rowsJ2 114 115 30 32 ≤ 13641241047122 := by decide +kernel

theorem rows22250R_3060 : rowsJ2 114 115 32 34 ≤ 20815350139861 := by decide +kernel

theorem rows22250R_3061 : rowsJ2 114 115 34 36 ≤ 18193856683371 := by decide +kernel

theorem rows22250R_3062 : rowsJ2 114 115 36 39 ≤ 19128710748318 := by decide +kernel

theorem rows22250R_3063 : rowsJ2 114 115 39 43 ≤ 9257878673904 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3048
#print axioms SieveCert.rows22250R_3063
