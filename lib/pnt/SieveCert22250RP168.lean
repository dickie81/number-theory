/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2002–2015 of 4715

File 168 of 351: the parts `rows22250R_2002` … `rows22250R_2015` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 90623 tests: row 85 columns 59–59, row 85 columns 60–61, row 85 columns
62–63, row 85 columns 64–65, row 85 columns 66–68, row 85 columns 69–72, row 85 columns 73–76, row 85 columns 77–78,
row 85 columns 79–79, row 85 columns 80–80, row 85 columns 81–81, row 85 columns 82–82, row 85 columns 83–83, row 85
columns 84–84), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2002 : rowsJ2 85 86 59 60 ≤ 0 := by decide +kernel

theorem rows22250R_2003 : rowsJ2 85 86 60 62 ≤ 0 := by decide +kernel

theorem rows22250R_2004 : rowsJ2 85 86 62 64 ≤ 0 := by decide +kernel

theorem rows22250R_2005 : rowsJ2 85 86 64 66 ≤ 0 := by decide +kernel

theorem rows22250R_2006 : rowsJ2 85 86 66 69 ≤ 0 := by decide +kernel

theorem rows22250R_2007 : rowsJ2 85 86 69 73 ≤ 0 := by decide +kernel

theorem rows22250R_2008 : rowsJ2 85 86 73 77 ≤ 120596426606 := by decide +kernel

theorem rows22250R_2009 : rowsJ2 85 86 77 79 ≤ 787515146863 := by decide +kernel

theorem rows22250R_2010 : rowsJ2 85 86 79 80 ≤ 835503568168 := by decide +kernel

theorem rows22250R_2011 : rowsJ2 85 86 80 81 ≤ 1224174370778 := by decide +kernel

theorem rows22250R_2012 : rowsJ2 85 86 81 82 ≤ 1696437277832 := by decide +kernel

theorem rows22250R_2013 : rowsJ2 85 86 82 83 ≤ 2297961185917 := by decide +kernel

theorem rows22250R_2014 : rowsJ2 85 86 83 84 ≤ 3053969836081 := by decide +kernel

theorem rows22250R_2015 : rowsJ2 85 86 84 85 ≤ 3954890353301 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2002
#print axioms SieveCert.rows22250R_2015
