/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3098–3112 of 5066

File 255 of 387: the parts `rows22240R_3098` … `rows22240R_3112` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 97643 in units of a depth-4 test: row 107 columns 101–339, row 108
columns 0–22, row 108 columns 23–30, row 108 columns 31–33, row 108 columns 34–35, row 108 columns 36–36, row 108
columns 37–37, row 108 columns 38–38, row 108 columns 39–39, row 108 columns 40–41, row 108 columns 42–43, row 108
columns 44–45, row 108 columns 46–48, row 108 columns 49–53, row 108 columns 54–62), each a sum of refined costs
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

theorem rows22240R_3098 : rowsJ2 107 108 101 340 ≤ 706511718610936 := by decide +kernel

theorem rows22240R_3099 : rowsJ2 108 109 0 23 ≤ 0 := by decide +kernel

theorem rows22240R_3100 : rowsJ2 108 109 23 31 ≤ 4958155737586 := by decide +kernel

theorem rows22240R_3101 : rowsJ2 108 109 31 34 ≤ 15792151973863 := by decide +kernel

theorem rows22240R_3102 : rowsJ2 108 109 34 36 ≤ 19445186905970 := by decide +kernel

theorem rows22240R_3103 : rowsJ2 108 109 36 37 ≤ 13048298740765 := by decide +kernel

theorem rows22240R_3104 : rowsJ2 108 109 37 38 ≤ 15776574410596 := by decide +kernel

theorem rows22240R_3105 : rowsJ2 108 109 38 39 ≤ 13654717819197 := by decide +kernel

theorem rows22240R_3106 : rowsJ2 108 109 39 40 ≤ 11625041592605 := by decide +kernel

theorem rows22240R_3107 : rowsJ2 108 109 40 42 ≤ 17991700816858 := by decide +kernel

theorem rows22240R_3108 : rowsJ2 108 109 42 44 ≤ 12316374332140 := by decide +kernel

theorem rows22240R_3109 : rowsJ2 108 109 44 46 ≤ 7774662064118 := by decide +kernel

theorem rows22240R_3110 : rowsJ2 108 109 46 49 ≤ 4801046438616 := by decide +kernel

theorem rows22240R_3111 : rowsJ2 108 109 49 54 ≤ 478045347530 := by decide +kernel

theorem rows22240R_3112 : rowsJ2 108 109 54 63 ≤ 589126734676 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3098
#print axioms SieveCert.rows22240R_3112
