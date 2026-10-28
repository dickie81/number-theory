/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2002–2014 of 5066

File 178 of 387: the parts `rows22240R_2002` … `rows22240R_2014` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 99929 in units of a depth-4 test: row 83 columns 49–49, row 83 columns
50–50, row 83 columns 51–51, row 83 columns 52–52, row 83 columns 53–53, row 83 columns 54–54, row 83 columns 55–55,
row 83 columns 56–56, row 83 columns 57–57, row 83 columns 58–58, row 83 columns 59–59, row 83 columns 60–60, row 83
columns 61–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2002 : rowsJ2 83 84 49 50 ≤ 506176488411 := by decide +kernel

theorem rows22240R_2003 : rowsJ2 83 84 50 51 ≤ 451838838761 := by decide +kernel

theorem rows22240R_2004 : rowsJ2 83 84 51 52 ≤ 396289671177 := by decide +kernel

theorem rows22240R_2005 : rowsJ2 83 84 52 53 ≤ 341344940849 := by decide +kernel

theorem rows22240R_2006 : rowsJ2 83 84 53 54 ≤ 285095031112 := by decide +kernel

theorem rows22240R_2007 : rowsJ2 83 84 54 55 ≤ 229401193497 := by decide +kernel

theorem rows22240R_2008 : rowsJ2 83 84 55 56 ≤ 172305870553 := by decide +kernel

theorem rows22240R_2009 : rowsJ2 83 84 56 57 ≤ 115718272807 := by decide +kernel

theorem rows22240R_2010 : rowsJ2 83 84 57 58 ≤ 57629654673 := by decide +kernel

theorem rows22240R_2011 : rowsJ2 83 84 58 59 ≤ 0 := by decide +kernel

theorem rows22240R_2012 : rowsJ2 83 84 59 60 ≤ 0 := by decide +kernel

theorem rows22240R_2013 : rowsJ2 83 84 60 61 ≤ 0 := by decide +kernel

theorem rows22240R_2014 : rowsJ2 83 84 61 62 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2002
#print axioms SieveCert.rows22240R_2014
