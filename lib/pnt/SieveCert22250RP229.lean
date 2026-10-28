/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2882–2896 of 4715

File 229 of 351: the parts `rows22250R_2882` … `rows22250R_2896` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 95734 in units of a depth-4 test: row 107 columns 42–43, row 107
columns 44–46, row 107 columns 47–51, row 107 columns 52–62, row 107 columns 63–69, row 107 columns 70–73, row 107
columns 74–76, row 107 columns 77–78, row 107 columns 79–80, row 107 columns 81–82, row 107 columns 83–84, row 107
columns 85–86, row 107 columns 87–88, row 107 columns 89–90, row 107 columns 91–92), each a sum of refined costs
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

theorem rows22250R_2882 : rowsJ2 107 108 42 44 ≤ 9603991126207 := by decide +kernel

theorem rows22250R_2883 : rowsJ2 107 108 44 47 ≤ 7285364544596 := by decide +kernel

theorem rows22250R_2884 : rowsJ2 107 108 47 52 ≤ 1397664691406 := by decide +kernel

theorem rows22250R_2885 : rowsJ2 107 108 52 63 ≤ 180750679986 := by decide +kernel

theorem rows22250R_2886 : rowsJ2 107 108 63 70 ≤ 0 := by decide +kernel

theorem rows22250R_2887 : rowsJ2 107 108 70 74 ≤ 0 := by decide +kernel

theorem rows22250R_2888 : rowsJ2 107 108 74 77 ≤ 103371961151 := by decide +kernel

theorem rows22250R_2889 : rowsJ2 107 108 77 79 ≤ 670158520047 := by decide +kernel

theorem rows22250R_2890 : rowsJ2 107 108 79 81 ≤ 965232748887 := by decide +kernel

theorem rows22250R_2891 : rowsJ2 107 108 81 83 ≤ 715733536012 := by decide +kernel

theorem rows22250R_2892 : rowsJ2 107 108 83 85 ≤ 874104631378 := by decide +kernel

theorem rows22250R_2893 : rowsJ2 107 108 85 87 ≤ 1639640089994 := by decide +kernel

theorem rows22250R_2894 : rowsJ2 107 108 87 89 ≤ 3037442511304 := by decide +kernel

theorem rows22250R_2895 : rowsJ2 107 108 89 91 ≤ 5095459803663 := by decide +kernel

theorem rows22250R_2896 : rowsJ2 107 108 91 93 ≤ 7846223056183 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2882
#print axioms SieveCert.rows22250R_2896
