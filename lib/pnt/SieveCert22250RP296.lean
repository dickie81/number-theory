/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3385–3400 of 5796

File 296 of 465: the parts `rows22250R_3385` … `rows22250R_3400` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 97772 tests: row 111 columns 21–31, row 111 columns 32–34, row 111 columns
35–36, row 111 columns 37–37, row 111 columns 38–38, row 111 columns 39–39, row 111 columns 40–40, row 111 columns
41–41, row 111 columns 42–42, row 111 columns 43–43, row 111 columns 44–44, row 111 columns 45–46, row 111 columns
47–48, row 111 columns 49–50, row 111 columns 51–53, row 111 columns 54–58), each a sum of refined costs (`rows2` or
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

theorem rows22250R_3385 : rowsJ2 111 112 21 32 ≤ 1968846078018 := by decide +kernel

theorem rows22250R_3386 : rowsJ2 111 112 32 35 ≤ 9711609076398 := by decide +kernel

theorem rows22250R_3387 : rowsJ2 111 112 35 37 ≤ 13297997571641 := by decide +kernel

theorem rows22250R_3388 : rowsJ2 111 112 37 38 ≤ 9307069929825 := by decide +kernel

theorem rows22250R_3389 : rowsJ2 111 112 38 39 ≤ 11091337082886 := by decide +kernel

theorem rows22250R_3390 : rowsJ2 111 112 39 40 ≤ 13061828367101 := by decide +kernel

theorem rows22250R_3391 : rowsJ2 111 112 40 41 ≤ 12916371672599 := by decide +kernel

theorem rows22250R_3392 : rowsJ2 111 112 41 42 ≤ 11259326297838 := by decide +kernel

theorem rows22250R_3393 : rowsJ2 111 112 42 43 ≤ 9763873810044 := by decide +kernel

theorem rows22250R_3394 : rowsJ2 111 112 43 44 ≤ 8426253477466 := by decide +kernel

theorem rows22250R_3395 : rowsJ2 111 112 44 45 ≤ 7157971380905 := by decide +kernel

theorem rows22250R_3396 : rowsJ2 111 112 45 47 ≤ 10788822322863 := by decide +kernel

theorem rows22250R_3397 : rowsJ2 111 112 47 49 ≤ 6636966663873 := by decide +kernel

theorem rows22250R_3398 : rowsJ2 111 112 49 51 ≤ 3634811583874 := by decide +kernel

theorem rows22250R_3399 : rowsJ2 111 112 51 54 ≤ 2148394360577 := by decide +kernel

theorem rows22250R_3400 : rowsJ2 111 112 54 59 ≤ 155714004966 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3385
#print axioms SieveCert.rows22250R_3400
