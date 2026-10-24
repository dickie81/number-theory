/-
# The refined certificate of the sieve route's loss at `L = 893/400` with `n = 300`: `total2 < K`

On `SieveGrid22325R.grid22325R` (`U1 = ⌈(40980/100000)DEN⌉`, `U2 = ⌊(47731/100000)DEN⌋`, `n = 300`),
`SieveCert.total2` is less than `K` (it is below `0.98877K`, rounded up; the certificate of `SieveCertDefs.lean` on
the same grid totals `1.09954K`): `total2` is `rows2 0 n` (`SieveCert2.total2_eq_rows2_full`), and its bound is
assembled one step at a time from the 561 parts' bounds (`rows22325R_0` … `rows22325R_560`, each by `decide +kernel`
in one of the 142 part files): a heavy row's bound from its column pieces' (`rowsJ2_le_of_split`,
`rows2_le_of_rowsJ2`), then the 170 ranges of rows from the last to the first (`rows2_le_of_split`), every bound a
literal and every step a theorem of its own (`c22325R_…`, `hr22325R_…`, `t22325R_…`); the bounds, `⌈1.001 × part⌉`
computed exactly in integers, sum to `1141112704303444843`, less than `K` by `decide +kernel` (`total2_lt_22325R`).

The file imports `SieveCert2.lean` and `SieveCert22325RP1.lean` … `SieveCert22325RP142.lean`.
-/
import SieveCert2
import SieveCert22325RP1
import SieveCert22325RP2
import SieveCert22325RP3
import SieveCert22325RP4
import SieveCert22325RP5
import SieveCert22325RP6
import SieveCert22325RP7
import SieveCert22325RP8
import SieveCert22325RP9
import SieveCert22325RP10
import SieveCert22325RP11
import SieveCert22325RP12
import SieveCert22325RP13
import SieveCert22325RP14
import SieveCert22325RP15
import SieveCert22325RP16
import SieveCert22325RP17
import SieveCert22325RP18
import SieveCert22325RP19
import SieveCert22325RP20
import SieveCert22325RP21
import SieveCert22325RP22
import SieveCert22325RP23
import SieveCert22325RP24
import SieveCert22325RP25
import SieveCert22325RP26
import SieveCert22325RP27
import SieveCert22325RP28
import SieveCert22325RP29
import SieveCert22325RP30
import SieveCert22325RP31
import SieveCert22325RP32
import SieveCert22325RP33
import SieveCert22325RP34
import SieveCert22325RP35
import SieveCert22325RP36
import SieveCert22325RP37
import SieveCert22325RP38
import SieveCert22325RP39
import SieveCert22325RP40
import SieveCert22325RP41
import SieveCert22325RP42
import SieveCert22325RP43
import SieveCert22325RP44
import SieveCert22325RP45
import SieveCert22325RP46
import SieveCert22325RP47
import SieveCert22325RP48
import SieveCert22325RP49
import SieveCert22325RP50
import SieveCert22325RP51
import SieveCert22325RP52
import SieveCert22325RP53
import SieveCert22325RP54
import SieveCert22325RP55
import SieveCert22325RP56
import SieveCert22325RP57
import SieveCert22325RP58
import SieveCert22325RP59
import SieveCert22325RP60
import SieveCert22325RP61
import SieveCert22325RP62
import SieveCert22325RP63
import SieveCert22325RP64
import SieveCert22325RP65
import SieveCert22325RP66
import SieveCert22325RP67
import SieveCert22325RP68
import SieveCert22325RP69
import SieveCert22325RP70
import SieveCert22325RP71
import SieveCert22325RP72
import SieveCert22325RP73
import SieveCert22325RP74
import SieveCert22325RP75
import SieveCert22325RP76
import SieveCert22325RP77
import SieveCert22325RP78
import SieveCert22325RP79
import SieveCert22325RP80
import SieveCert22325RP81
import SieveCert22325RP82
import SieveCert22325RP83
import SieveCert22325RP84
import SieveCert22325RP85
import SieveCert22325RP86
import SieveCert22325RP87
import SieveCert22325RP88
import SieveCert22325RP89
import SieveCert22325RP90
import SieveCert22325RP91
import SieveCert22325RP92
import SieveCert22325RP93
import SieveCert22325RP94
import SieveCert22325RP95
import SieveCert22325RP96
import SieveCert22325RP97
import SieveCert22325RP98
import SieveCert22325RP99
import SieveCert22325RP100
import SieveCert22325RP101
import SieveCert22325RP102
import SieveCert22325RP103
import SieveCert22325RP104
import SieveCert22325RP105
import SieveCert22325RP106
import SieveCert22325RP107
import SieveCert22325RP108
import SieveCert22325RP109
import SieveCert22325RP110
import SieveCert22325RP111
import SieveCert22325RP112
import SieveCert22325RP113
import SieveCert22325RP114
import SieveCert22325RP115
import SieveCert22325RP116
import SieveCert22325RP117
import SieveCert22325RP118
import SieveCert22325RP119
import SieveCert22325RP120
import SieveCert22325RP121
import SieveCert22325RP122
import SieveCert22325RP123
import SieveCert22325RP124
import SieveCert22325RP125
import SieveCert22325RP126
import SieveCert22325RP127
import SieveCert22325RP128
import SieveCert22325RP129
import SieveCert22325RP130
import SieveCert22325RP131
import SieveCert22325RP132
import SieveCert22325RP133
import SieveCert22325RP134
import SieveCert22325RP135
import SieveCert22325RP136
import SieveCert22325RP137
import SieveCert22325RP138
import SieveCert22325RP139
import SieveCert22325RP140
import SieveCert22325RP141
import SieveCert22325RP142

namespace SieveCert

section

attribute [local instance] grid22325R

/-! The chain of bounds: `c22325R_{i}_{m}` for the heavy row `i` from its `m`-th column piece on, `hr22325R_{i}` for
the heavy row `i`, `t22325R_{m}` for the rows from the `m`-th range on; each a theorem of its own, its name distinct
from the other certificates' chains in the same namespace. -/

theorem c22325R_35_0 : rowsJ2 35 36 0 300 ≤ 2880188252782499 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22325R_12 rows22325R_13 (by norm_num)

theorem hr22325R_35 : rows2 35 36 ≤ 2880188252782499 := rows2_le_of_rowsJ2 35 36 c22325R_35_0

theorem c22325R_36_0 : rowsJ2 36 37 0 300 ≤ 2869029312321431 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22325R_14 rows22325R_15 (by norm_num)

theorem hr22325R_36 : rows2 36 37 ≤ 2869029312321431 := rows2_le_of_rowsJ2 36 37 c22325R_36_0

theorem c22325R_37_0 : rowsJ2 37 38 0 300 ≤ 2843750107076598 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22325R_16 rows22325R_17 (by norm_num)

theorem hr22325R_37 : rows2 37 38 ≤ 2843750107076598 := rows2_le_of_rowsJ2 37 38 c22325R_37_0

theorem c22325R_38_0 : rowsJ2 38 39 0 300 ≤ 2807677515866848 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22325R_18 rows22325R_19 (by norm_num)

theorem hr22325R_38 : rows2 38 39 ≤ 2807677515866848 := rows2_le_of_rowsJ2 38 39 c22325R_38_0

theorem c22325R_39_0 : rowsJ2 39 40 0 300 ≤ 2763313047450471 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22325R_20 rows22325R_21 (by norm_num)

theorem hr22325R_39 : rows2 39 40 ≤ 2763313047450471 := rows2_le_of_rowsJ2 39 40 c22325R_39_0

theorem c22325R_40_0 : rowsJ2 40 41 0 300 ≤ 2713730075841687 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22325R_22 rows22325R_23 (by norm_num)

theorem hr22325R_40 : rows2 40 41 ≤ 2713730075841687 := rows2_le_of_rowsJ2 40 41 c22325R_40_0

theorem c22325R_41_0 : rowsJ2 41 42 0 300 ≤ 2661894178253561 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22325R_24 rows22325R_25 (by norm_num)

theorem hr22325R_41 : rows2 41 42 ≤ 2661894178253561 := rows2_le_of_rowsJ2 41 42 c22325R_41_0

theorem c22325R_42_0 : rowsJ2 42 43 0 300 ≤ 2610862703994818 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22325R_26 rows22325R_27 (by norm_num)

theorem hr22325R_42 : rows2 42 43 ≤ 2610862703994818 := rows2_le_of_rowsJ2 42 43 c22325R_42_0

theorem c22325R_43_0 : rowsJ2 43 44 0 300 ≤ 2563483881326354 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22325R_28 rows22325R_29 (by norm_num)

theorem hr22325R_43 : rows2 43 44 ≤ 2563483881326354 := rows2_le_of_rowsJ2 43 44 c22325R_43_0

theorem c22325R_44_1 : rowsJ2 44 45 35 300 ≤ 463777413892634 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22325R_31 rows22325R_32 (by norm_num)

theorem c22325R_44_0 : rowsJ2 44 45 0 300 ≤ 2523376093183049 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22325R_30 c22325R_44_1 (by norm_num)

theorem hr22325R_44 : rows2 44 45 ≤ 2523376093183049 := rows2_le_of_rowsJ2 44 45 c22325R_44_0

theorem c22325R_45_1 : rowsJ2 45 46 35 300 ≤ 513042600085089 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22325R_34 rows22325R_35 (by norm_num)

theorem c22325R_45_0 : rowsJ2 45 46 0 300 ≤ 2492962404061364 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22325R_33 c22325R_45_1 (by norm_num)

theorem hr22325R_45 : rows2 45 46 ≤ 2492962404061364 := rows2_le_of_rowsJ2 45 46 c22325R_45_0

theorem c22325R_46_1 : rowsJ2 46 47 35 300 ≤ 574102925023717 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22325R_37 rows22325R_38 (by norm_num)

theorem c22325R_46_0 : rowsJ2 46 47 0 300 ≤ 2475213189064815 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22325R_36 c22325R_46_1 (by norm_num)

theorem hr22325R_46 : rows2 46 47 ≤ 2475213189064815 := rows2_le_of_rowsJ2 46 47 c22325R_46_0

theorem c22325R_47_1 : rowsJ2 47 48 35 300 ≤ 649897522257209 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22325R_40 rows22325R_41 (by norm_num)

theorem c22325R_47_0 : rowsJ2 47 48 0 300 ≤ 2472949691957917 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22325R_39 c22325R_47_1 (by norm_num)

theorem hr22325R_47 : rows2 47 48 ≤ 2472949691957917 := rows2_le_of_rowsJ2 47 48 c22325R_47_0

theorem c22325R_48_1 : rowsJ2 48 49 35 300 ≤ 736125592772900 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22325R_43 rows22325R_44 (by norm_num)

theorem c22325R_48_0 : rowsJ2 48 49 0 300 ≤ 2482264989518009 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22325R_42 c22325R_48_1 (by norm_num)

theorem hr22325R_48 : rows2 48 49 ≤ 2482264989518009 := rows2_le_of_rowsJ2 48 49 c22325R_48_0

theorem c22325R_49_1 : rowsJ2 49 50 35 300 ≤ 819542647124549 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22325R_46 rows22325R_47 (by norm_num)

theorem c22325R_49_0 : rowsJ2 49 50 0 300 ≤ 2489499697235241 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22325R_45 c22325R_49_1 (by norm_num)

theorem hr22325R_49 : rows2 49 50 ≤ 2489499697235241 := rows2_le_of_rowsJ2 49 50 c22325R_49_0

theorem c22325R_50_1 : rowsJ2 50 51 35 300 ≤ 896413190353942 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22325R_49 rows22325R_50 (by norm_num)

theorem c22325R_50_0 : rowsJ2 50 51 0 300 ≤ 2491762993379829 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22325R_48 c22325R_50_1 (by norm_num)

theorem hr22325R_50 : rows2 50 51 ≤ 2491762993379829 := rows2_le_of_rowsJ2 50 51 c22325R_50_0

theorem c22325R_51_2 : rowsJ2 51 52 44 300 ≤ 610881277418601 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22325R_53 rows22325R_54 (by norm_num)

theorem c22325R_51_1 : rowsJ2 51 52 35 300 ≤ 971372512455805 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22325R_52 c22325R_51_2 (by norm_num)

theorem c22325R_51_0 : rowsJ2 51 52 0 300 ≤ 2493140994669026 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22325R_51 c22325R_51_1 (by norm_num)

theorem hr22325R_51 : rows2 51 52 ≤ 2493140994669026 := rows2_le_of_rowsJ2 51 52 c22325R_51_0

theorem c22325R_52_2 : rowsJ2 52 53 44 300 ≤ 674216609976818 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22325R_57 rows22325R_58 (by norm_num)

theorem c22325R_52_1 : rowsJ2 52 53 35 300 ≤ 1039158742266690 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22325R_56 c22325R_52_2 (by norm_num)

theorem c22325R_52_0 : rowsJ2 52 53 0 300 ≤ 2488930359610352 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22325R_55 c22325R_52_1 (by norm_num)

theorem hr22325R_52 : rows2 52 53 ≤ 2488930359610352 := rows2_le_of_rowsJ2 52 53 c22325R_52_0

theorem c22325R_53_2 : rowsJ2 53 54 44 300 ≤ 731740299258194 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22325R_61 rows22325R_62 (by norm_num)

theorem c22325R_53_1 : rowsJ2 53 54 35 300 ≤ 1104301038962150 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22325R_60 c22325R_53_2 (by norm_num)

theorem c22325R_53_0 : rowsJ2 53 54 0 300 ≤ 2483557012512271 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22325R_59 c22325R_53_1 (by norm_num)

theorem hr22325R_53 : rows2 53 54 ≤ 2483557012512271 := rows2_le_of_rowsJ2 53 54 c22325R_53_0

theorem c22325R_54_2 : rowsJ2 54 55 44 300 ≤ 778652792049260 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22325R_65 rows22325R_66 (by norm_num)

theorem c22325R_54_1 : rowsJ2 54 55 35 300 ≤ 1161552897186927 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22325R_64 c22325R_54_2 (by norm_num)

theorem c22325R_54_0 : rowsJ2 54 55 0 300 ≤ 2472218169809074 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22325R_63 c22325R_54_1 (by norm_num)

theorem hr22325R_54 : rows2 54 55 ≤ 2472218169809074 := rows2_le_of_rowsJ2 54 55 c22325R_54_0

theorem c22325R_55_2 : rowsJ2 55 56 44 300 ≤ 819106564712069 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22325R_69 rows22325R_70 (by norm_num)

theorem c22325R_55_1 : rowsJ2 55 56 35 300 ≤ 1215409742912006 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22325R_68 c22325R_55_2 (by norm_num)

theorem c22325R_55_0 : rowsJ2 55 56 0 300 ≤ 2458990377635874 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22325R_67 c22325R_55_1 (by norm_num)

theorem hr22325R_55 : rows2 55 56 ≤ 2458990377635874 := rows2_le_of_rowsJ2 55 56 c22325R_55_0

theorem c22325R_56_2 : rowsJ2 56 57 44 300 ≤ 848245680109566 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22325R_73 rows22325R_74 (by norm_num)

theorem c22325R_56_1 : rowsJ2 56 57 35 300 ≤ 1260476553570032 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22325R_72 c22325R_56_2 (by norm_num)

theorem c22325R_56_0 : rowsJ2 56 57 0 300 ≤ 2439406407203793 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22325R_71 c22325R_56_1 (by norm_num)

theorem hr22325R_56 : rows2 56 57 ≤ 2439406407203793 := rows2_le_of_rowsJ2 56 57 c22325R_56_0

theorem c22325R_57_2 : rowsJ2 57 58 44 300 ≤ 870763715803452 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22325R_77 rows22325R_78 (by norm_num)

theorem c22325R_57_1 : rowsJ2 57 58 35 300 ≤ 1301378517976263 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22325R_76 c22325R_57_2 (by norm_num)

theorem c22325R_57_0 : rowsJ2 57 58 0 300 ≤ 2417534161142054 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22325R_75 c22325R_57_1 (by norm_num)

theorem hr22325R_57 : rows2 57 58 ≤ 2417534161142054 := rows2_le_of_rowsJ2 57 58 c22325R_57_0

theorem c22325R_58_2 : rowsJ2 58 59 44 300 ≤ 886849411158127 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22325R_81 rows22325R_82 (by norm_num)

theorem c22325R_58_1 : rowsJ2 58 59 35 300 ≤ 1333012005402359 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22325R_80 c22325R_58_2 (by norm_num)

theorem c22325R_58_0 : rowsJ2 58 59 0 300 ≤ 2388896988884035 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22325R_79 c22325R_58_1 (by norm_num)

theorem hr22325R_58 : rows2 58 59 ≤ 2388896988884035 := rows2_le_of_rowsJ2 58 59 c22325R_58_0

theorem c22325R_59_2 : rowsJ2 59 60 44 300 ≤ 896612872957874 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22325R_85 rows22325R_86 (by norm_num)

theorem c22325R_59_1 : rowsJ2 59 60 35 300 ≤ 1360199896299888 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22325R_84 c22325R_59_2 (by norm_num)

theorem c22325R_59_0 : rowsJ2 59 60 0 300 ≤ 2358237654046697 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22325R_83 c22325R_59_1 (by norm_num)

theorem hr22325R_59 : rows2 59 60 ≤ 2358237654046697 := rows2_le_of_rowsJ2 59 60 c22325R_59_0

theorem c22325R_60_2 : rowsJ2 60 61 44 300 ≤ 900259503300500 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22325R_89 rows22325R_90 (by norm_num)

theorem c22325R_60_1 : rowsJ2 60 61 35 300 ≤ 1377891724990740 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22325R_88 c22325R_60_2 (by norm_num)

theorem c22325R_60_0 : rowsJ2 60 61 0 300 ≤ 2321019555308174 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22325R_87 c22325R_60_1 (by norm_num)

theorem hr22325R_60 : rows2 60 61 ≤ 2321019555308174 := rows2_le_of_rowsJ2 60 61 c22325R_60_0

theorem c22325R_61_2 : rowsJ2 61 62 45 300 ≤ 830152803220446 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22325R_93 rows22325R_94 (by norm_num)

theorem c22325R_61_1 : rowsJ2 61 62 35 300 ≤ 1390942498687983 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22325R_92 c22325R_61_2 (by norm_num)

theorem c22325R_61_0 : rowsJ2 61 62 0 300 ≤ 2281680325076260 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22325R_91 c22325R_61_1 (by norm_num)

theorem hr22325R_61 : rows2 61 62 ≤ 2281680325076260 := rows2_le_of_rowsJ2 61 62 c22325R_61_0

theorem c22325R_62_1 : rowsJ2 62 63 35 300 ≤ 1394203394603854 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22325R_96 rows22325R_97 (by norm_num)

theorem c22325R_62_0 : rowsJ2 62 63 0 300 ≤ 2236110019166204 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22325R_95 c22325R_62_1 (by norm_num)

theorem hr22325R_62 : rows2 62 63 ≤ 2236110019166204 := rows2_le_of_rowsJ2 62 63 c22325R_62_0

theorem c22325R_63_1 : rowsJ2 63 64 35 300 ≤ 1392715486158706 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22325R_99 rows22325R_100 (by norm_num)

theorem c22325R_63_0 : rowsJ2 63 64 0 300 ≤ 2188789894333006 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22325R_98 c22325R_63_1 (by norm_num)

theorem hr22325R_63 : rows2 63 64 ≤ 2188789894333006 := rows2_le_of_rowsJ2 63 64 c22325R_63_0

theorem c22325R_64_1 : rowsJ2 64 65 35 300 ≤ 1381461855826474 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22325R_102 rows22325R_103 (by norm_num)

theorem c22325R_64_0 : rowsJ2 64 65 0 300 ≤ 2135424839707271 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22325R_101 c22325R_64_1 (by norm_num)

theorem hr22325R_64 : rows2 64 65 ≤ 2135424839707271 := rows2_le_of_rowsJ2 64 65 c22325R_64_0

theorem c22325R_65_1 : rowsJ2 65 66 35 300 ≤ 1365521423860698 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22325R_105 rows22325R_106 (by norm_num)

theorem c22325R_65_0 : rowsJ2 65 66 0 300 ≤ 2081049611360420 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22325R_104 c22325R_65_1 (by norm_num)

theorem hr22325R_65 : rows2 65 66 ≤ 2081049611360420 := rows2_le_of_rowsJ2 65 66 c22325R_65_0

theorem c22325R_66_1 : rowsJ2 66 67 35 300 ≤ 1340487905467018 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22325R_108 rows22325R_109 (by norm_num)

theorem c22325R_66_0 : rowsJ2 66 67 0 300 ≤ 2021341483772186 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22325R_107 c22325R_66_1 (by norm_num)

theorem hr22325R_66 : rows2 66 67 ≤ 2021341483772186 := rows2_le_of_rowsJ2 66 67 c22325R_66_0

theorem c22325R_67_2 : rowsJ2 67 68 47 300 ≤ 614108972424577 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22325R_112 rows22325R_113 (by norm_num)

theorem c22325R_67_1 : rowsJ2 67 68 35 300 ≤ 1311538514123202 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22325R_111 c22325R_67_2 (by norm_num)

theorem c22325R_67_0 : rowsJ2 67 68 0 300 ≤ 1961067246295058 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22325R_110 c22325R_67_1 (by norm_num)

theorem hr22325R_67 : rows2 67 68 ≤ 1961067246295058 := rows2_le_of_rowsJ2 67 68 c22325R_67_0

theorem c22325R_68_2 : rowsJ2 68 69 48 300 ≤ 538469649702954 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22325R_116 rows22325R_117 (by norm_num)

theorem c22325R_68_1 : rowsJ2 68 69 35 300 ≤ 1274249455452619 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22325R_115 c22325R_68_2 (by norm_num)

theorem c22325R_68_0 : rowsJ2 68 69 0 300 ≤ 1896430616892508 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22325R_114 c22325R_68_1 (by norm_num)

theorem hr22325R_68 : rows2 68 69 ≤ 1896430616892508 := rows2_le_of_rowsJ2 68 69 c22325R_68_0

theorem c22325R_69_2 : rowsJ2 69 70 49 300 ≤ 466338951012829 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22325R_120 rows22325R_121 (by norm_num)

theorem c22325R_69_1 : rowsJ2 69 70 35 300 ≤ 1234029635955373 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22325R_119 c22325R_69_2 (by norm_num)

theorem c22325R_69_0 : rowsJ2 69 70 0 300 ≤ 1832277782709327 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22325R_118 c22325R_69_1 (by norm_num)

theorem hr22325R_69 : rows2 69 70 ≤ 1832277782709327 := rows2_le_of_rowsJ2 69 70 c22325R_69_0

theorem c22325R_70_2 : rowsJ2 70 71 50 300 ≤ 398248745316889 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22325R_124 rows22325R_125 (by norm_num)

theorem c22325R_70_1 : rowsJ2 70 71 35 300 ≤ 1186572066132953 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22325R_123 c22325R_70_2 (by norm_num)

theorem c22325R_70_0 : rowsJ2 70 71 0 300 ≤ 1764558663699992 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22325R_122 c22325R_70_1 (by norm_num)

theorem hr22325R_70 : rows2 70 71 ≤ 1764558663699992 := rows2_le_of_rowsJ2 70 71 c22325R_70_0

theorem c22325R_71_2 : rowsJ2 71 72 51 300 ≤ 334803354172864 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22325R_128 rows22325R_129 (by norm_num)

theorem c22325R_71_1 : rowsJ2 71 72 35 300 ≤ 1137423446176063 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22325R_127 c22325R_71_2 (by norm_num)

theorem c22325R_71_0 : rowsJ2 71 72 0 300 ≤ 1698811453408342 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22325R_126 c22325R_71_1 (by norm_num)

theorem hr22325R_71 : rows2 71 72 ≤ 1698811453408342 := rows2_le_of_rowsJ2 71 72 c22325R_71_0

theorem c22325R_72_2 : rowsJ2 72 73 54 300 ≤ 222298740751903 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22325R_132 rows22325R_133 (by norm_num)

theorem c22325R_72_1 : rowsJ2 72 73 35 300 ≤ 1083613459452130 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22325R_131 c22325R_72_2 (by norm_num)

theorem c22325R_72_0 : rowsJ2 72 73 0 300 ≤ 1632178886799382 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22325R_130 c22325R_72_1 (by norm_num)

theorem hr22325R_72 : rows2 72 73 ≤ 1632178886799382 := rows2_le_of_rowsJ2 72 73 c22325R_72_0

theorem c22325R_73_3 : rowsJ2 73 74 68 300 ≤ 29017937816117 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22325R_137 rows22325R_138 (by norm_num)

theorem c22325R_73_2 : rowsJ2 73 74 58 300 ≤ 122933713935506 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22325R_136 c22325R_73_3 (by norm_num)

theorem c22325R_73_1 : rowsJ2 73 74 35 300 ≤ 1032425660716147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22325R_135 c22325R_73_2 (by norm_num)

theorem c22325R_73_0 : rowsJ2 73 74 0 300 ≤ 1571259401844581 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22325R_134 c22325R_73_1 (by norm_num)

theorem hr22325R_73 : rows2 73 74 ≤ 1571259401844581 := rows2_le_of_rowsJ2 73 74 c22325R_73_0

theorem c22325R_74_3 : rowsJ2 74 75 68 300 ≤ 35159927901809 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22325R_142 rows22325R_143 (by norm_num)

theorem c22325R_74_2 : rowsJ2 74 75 59 300 ≤ 100704212586151 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22325R_141 c22325R_74_3 (by norm_num)

theorem c22325R_74_1 : rowsJ2 74 75 35 300 ≤ 979303436620127 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22325R_140 c22325R_74_2 (by norm_num)

theorem c22325R_74_0 : rowsJ2 74 75 0 300 ≤ 1512104563343075 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22325R_139 c22325R_74_1 (by norm_num)

theorem hr22325R_74 : rows2 74 75 ≤ 1512104563343075 := rows2_le_of_rowsJ2 74 75 c22325R_74_0

theorem c22325R_75_3 : rowsJ2 75 76 68 300 ≤ 39994800311877 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22325R_147 rows22325R_148 (by norm_num)

theorem c22325R_75_2 : rowsJ2 75 76 60 300 ≤ 82729337221534 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22325R_146 c22325R_75_3 (by norm_num)

theorem c22325R_75_1 : rowsJ2 75 76 35 300 ≤ 925976961989330 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22325R_145 c22325R_75_2 (by norm_num)

theorem c22325R_75_0 : rowsJ2 75 76 0 300 ≤ 1455673229961110 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22325R_144 c22325R_75_1 (by norm_num)

theorem hr22325R_75 : rows2 75 76 ≤ 1455673229961110 := rows2_le_of_rowsJ2 75 76 c22325R_75_0

theorem c22325R_76_4 : rowsJ2 76 77 72 300 ≤ 30581556645803 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22325R_153 rows22325R_154 (by norm_num)

theorem c22325R_76_3 : rowsJ2 76 77 68 300 ≤ 43508622640251 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22325R_152 c22325R_76_4 (by norm_num)

theorem c22325R_76_2 : rowsJ2 76 77 61 300 ≤ 68873366413460 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22325R_151 c22325R_76_3 (by norm_num)

theorem c22325R_76_1 : rowsJ2 76 77 35 300 ≤ 872683734685720 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22325R_150 c22325R_76_2 (by norm_num)

theorem c22325R_76_0 : rowsJ2 76 77 0 300 ≤ 1397404714244424 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22325R_149 c22325R_76_1 (by norm_num)

theorem hr22325R_76 : rows2 76 77 ≤ 1397404714244424 := rows2_le_of_rowsJ2 76 77 c22325R_76_0

theorem c22325R_77_4 : rowsJ2 77 78 72 300 ≤ 32053283792590 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22325R_159 rows22325R_160 (by norm_num)

theorem c22325R_77_3 : rowsJ2 77 78 68 300 ≤ 44869441642169 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22325R_158 c22325R_77_4 (by norm_num)

theorem c22325R_77_2 : rowsJ2 77 78 61 300 ≤ 63549832887731 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22325R_157 c22325R_77_3 (by norm_num)

theorem c22325R_77_1 : rowsJ2 77 78 35 300 ≤ 818965914057484 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22325R_156 c22325R_77_2 (by norm_num)

theorem c22325R_77_0 : rowsJ2 77 78 0 300 ≤ 1341672187149202 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22325R_155 c22325R_77_1 (by norm_num)

theorem hr22325R_77 : rows2 77 78 ≤ 1341672187149202 := rows2_le_of_rowsJ2 77 78 c22325R_77_0

theorem c22325R_78_4 : rowsJ2 78 79 72 300 ≤ 32248312174077 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22325R_165 rows22325R_166 (by norm_num)

theorem c22325R_78_3 : rowsJ2 78 79 68 300 ≤ 44955765122837 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22325R_164 c22325R_78_4 (by norm_num)

theorem c22325R_78_2 : rowsJ2 78 79 61 300 ≤ 58194717448449 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22325R_163 c22325R_78_3 (by norm_num)

theorem c22325R_78_1 : rowsJ2 78 79 35 300 ≤ 765989928942613 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22325R_162 c22325R_78_2 (by norm_num)

theorem c22325R_78_0 : rowsJ2 78 79 0 300 ≤ 1284723796195299 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22325R_161 c22325R_78_1 (by norm_num)

theorem hr22325R_78 : rows2 78 79 ≤ 1284723796195299 := rows2_le_of_rowsJ2 78 79 c22325R_78_0

theorem c22325R_79_4 : rowsJ2 79 80 72 300 ≤ 31129834352664 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22325R_171 rows22325R_172 (by norm_num)

theorem c22325R_79_3 : rowsJ2 79 80 68 300 ≤ 43728734504308 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22325R_170 c22325R_79_4 (by norm_num)

theorem c22325R_79_2 : rowsJ2 79 80 61 300 ≤ 52857333327237 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22325R_169 c22325R_79_3 (by norm_num)

theorem c22325R_79_1 : rowsJ2 79 80 35 300 ≤ 713805606036450 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22325R_168 c22325R_79_2 (by norm_num)

theorem c22325R_79_0 : rowsJ2 79 80 0 300 ≤ 1231026041339800 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22325R_167 c22325R_79_1 (by norm_num)

theorem hr22325R_79 : rows2 79 80 ≤ 1231026041339800 := rows2_le_of_rowsJ2 79 80 c22325R_79_0

theorem c22325R_80_5 : rowsJ2 80 81 76 300 ≤ 14923924860348 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22325R_178 rows22325R_179 (by norm_num)

theorem c22325R_80_4 : rowsJ2 80 81 72 300 ≤ 29715130357376 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22325R_177 c22325R_80_5 (by norm_num)

theorem c22325R_80_3 : rowsJ2 80 81 68 300 ≤ 42207675304349 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22325R_176 c22325R_80_4 (by norm_num)

theorem c22325R_80_2 : rowsJ2 80 81 62 300 ≤ 46478043794236 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22325R_175 c22325R_80_3 (by norm_num)

theorem c22325R_80_1 : rowsJ2 80 81 36 300 ≤ 614567338821086 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22325R_174 c22325R_80_2 (by norm_num)

theorem c22325R_80_0 : rowsJ2 80 81 0 300 ≤ 1177150375620606 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22325R_173 c22325R_80_1 (by norm_num)

theorem hr22325R_80 : rows2 80 81 ≤ 1177150375620606 := rows2_le_of_rowsJ2 80 81 c22325R_80_0

theorem c22325R_81_5 : rowsJ2 81 82 76 300 ≤ 16238656101629 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22325R_185 rows22325R_186 (by norm_num)

theorem c22325R_81_4 : rowsJ2 81 82 72 300 ≤ 28684632778766 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22325R_184 c22325R_81_5 (by norm_num)

theorem c22325R_81_3 : rowsJ2 81 82 68 300 ≤ 40470571333718 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22325R_183 c22325R_81_4 (by norm_num)

theorem c22325R_81_2 : rowsJ2 81 82 62 300 ≤ 43781165181565 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22325R_182 c22325R_81_3 (by norm_num)

theorem c22325R_81_1 : rowsJ2 81 82 36 300 ≤ 567980409333610 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22325R_181 c22325R_81_2 (by norm_num)

theorem c22325R_81_0 : rowsJ2 81 82 0 300 ≤ 1127629907053073 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22325R_180 c22325R_81_1 (by norm_num)

theorem hr22325R_81 : rows2 81 82 ≤ 1127629907053073 := rows2_le_of_rowsJ2 81 82 c22325R_81_0

theorem c22325R_82_5 : rowsJ2 82 83 76 300 ≤ 17871051720159 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22325R_192 rows22325R_193 (by norm_num)

theorem c22325R_82_4 : rowsJ2 82 83 72 300 ≤ 28183247944056 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22325R_191 c22325R_82_5 (by norm_num)

theorem c22325R_82_3 : rowsJ2 82 83 68 300 ≤ 39316479054479 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22325R_190 c22325R_82_4 (by norm_num)

theorem c22325R_82_2 : rowsJ2 82 83 62 300 ≤ 42284170816148 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22325R_189 c22325R_82_3 (by norm_num)

theorem c22325R_82_1 : rowsJ2 82 83 37 300 ≤ 481685988387713 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22325R_188 c22325R_82_2 (by norm_num)

theorem c22325R_82_0 : rowsJ2 82 83 0 300 ≤ 1078309319992129 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22325R_187 c22325R_82_1 (by norm_num)

theorem hr22325R_82 : rows2 82 83 ≤ 1078309319992129 := rows2_le_of_rowsJ2 82 83 c22325R_82_0

theorem c22325R_83_5 : rowsJ2 83 84 75 300 ≤ 22528874033507 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22325R_199 rows22325R_200 (by norm_num)

theorem c22325R_83_4 : rowsJ2 83 84 71 300 ≤ 31754029284357 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22325R_198 c22325R_83_5 (by norm_num)

theorem c22325R_83_3 : rowsJ2 83 84 67 300 ≤ 40467407935109 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22325R_197 c22325R_83_4 (by norm_num)

theorem c22325R_83_2 : rowsJ2 83 84 62 300 ≤ 42076543910118 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22325R_196 c22325R_83_3 (by norm_num)

theorem c22325R_83_1 : rowsJ2 83 84 37 300 ≤ 442740296075560 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22325R_195 c22325R_83_2 (by norm_num)

theorem c22325R_83_0 : rowsJ2 83 84 0 300 ≤ 1034642660498768 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22325R_194 c22325R_83_1 (by norm_num)

theorem hr22325R_83 : rows2 83 84 ≤ 1034642660498768 := rows2_le_of_rowsJ2 83 84 c22325R_83_0

theorem c22325R_84_5 : rowsJ2 84 85 75 300 ≤ 26312053623012 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22325R_206 rows22325R_207 (by norm_num)

theorem c22325R_84_4 : rowsJ2 84 85 71 300 ≤ 33732918784326 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22325R_205 c22325R_84_5 (by norm_num)

theorem c22325R_84_3 : rowsJ2 84 85 67 300 ≤ 41894302301872 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22325R_204 c22325R_84_4 (by norm_num)

theorem c22325R_84_2 : rowsJ2 84 85 62 300 ≤ 43491226847047 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22325R_203 c22325R_84_3 (by norm_num)

theorem c22325R_84_1 : rowsJ2 84 85 38 300 ≤ 371315094321486 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22325R_202 c22325R_84_2 (by norm_num)

theorem c22325R_84_0 : rowsJ2 84 85 0 300 ≤ 992189382039635 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22325R_201 c22325R_84_1 (by norm_num)

theorem hr22325R_84 : rows2 84 85 ≤ 992189382039635 := rows2_le_of_rowsJ2 84 85 c22325R_84_0

theorem c22325R_85_6 : rowsJ2 85 86 80 300 ≤ 25875142812648 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22325R_214 rows22325R_215 (by norm_num)

theorem c22325R_85_5 : rowsJ2 85 86 75 300 ≤ 32570330578539 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22325R_213 c22325R_85_6 (by norm_num)

theorem c22325R_85_4 : rowsJ2 85 86 71 300 ≤ 38387711031338 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22325R_212 c22325R_85_5 (by norm_num)

theorem c22325R_85_3 : rowsJ2 85 86 67 300 ≤ 45596132636342 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22325R_211 c22325R_85_4 (by norm_num)

theorem c22325R_85_2 : rowsJ2 85 86 62 300 ≤ 47181031811004 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22325R_210 c22325R_85_3 (by norm_num)

theorem c22325R_85_1 : rowsJ2 85 86 39 300 ≤ 310233267515821 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22325R_209 c22325R_85_2 (by norm_num)

theorem c22325R_85_0 : rowsJ2 85 86 0 300 ≤ 956122319623426 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22325R_208 c22325R_85_1 (by norm_num)

theorem hr22325R_85 : rows2 85 86 ≤ 956122319623426 := rows2_le_of_rowsJ2 85 86 c22325R_85_0

theorem c22325R_86_6 : rowsJ2 86 87 80 300 ≤ 35570992825708 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22325R_222 rows22325R_223 (by norm_num)

theorem c22325R_86_5 : rowsJ2 86 87 75 300 ≤ 41323395868776 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22325R_221 c22325R_86_6 (by norm_num)

theorem c22325R_86_4 : rowsJ2 86 87 71 300 ≤ 45734940090395 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22325R_220 c22325R_86_5 (by norm_num)

theorem c22325R_86_3 : rowsJ2 86 87 67 300 ≤ 52090905650147 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22325R_219 c22325R_86_4 (by norm_num)

theorem c22325R_86_2 : rowsJ2 86 87 62 300 ≤ 53661962355323 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22325R_218 c22325R_86_3 (by norm_num)

theorem c22325R_86_1 : rowsJ2 86 87 40 300 ≤ 259824198971689 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22325R_217 c22325R_86_2 (by norm_num)

theorem c22325R_86_0 : rowsJ2 86 87 0 300 ≤ 922607436346582 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22325R_216 c22325R_86_1 (by norm_num)

theorem hr22325R_86 : rows2 86 87 ≤ 922607436346582 := rows2_le_of_rowsJ2 86 87 c22325R_86_0

theorem c22325R_87_6 : rowsJ2 87 88 80 300 ≤ 48609124876187 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22325R_230 rows22325R_231 (by norm_num)

theorem c22325R_87_5 : rowsJ2 87 88 75 300 ≤ 53814005170753 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22325R_229 c22325R_87_6 (by norm_num)

theorem c22325R_87_4 : rowsJ2 87 88 71 300 ≤ 57016486819908 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22325R_228 c22325R_87_5 (by norm_num)

theorem c22325R_87_3 : rowsJ2 87 88 67 300 ≤ 62237205463157 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22325R_227 c22325R_87_4 (by norm_num)

theorem c22325R_87_2 : rowsJ2 87 88 62 300 ≤ 63794698152715 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22325R_226 c22325R_87_3 (by norm_num)

theorem c22325R_87_1 : rowsJ2 87 88 43 300 ≤ 178574447239500 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22325R_225 c22325R_87_2 (by norm_num)

theorem c22325R_87_0 : rowsJ2 87 88 0 300 ≤ 896780950161406 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22325R_224 c22325R_87_1 (by norm_num)

theorem hr22325R_87 : rows2 87 88 ≤ 896780950161406 := rows2_le_of_rowsJ2 87 88 c22325R_87_0

theorem c22325R_88_6 : rowsJ2 88 89 81 300 ≤ 62289343705773 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22325R_238 rows22325R_239 (by norm_num)

theorem c22325R_88_5 : rowsJ2 88 89 76 300 ≤ 69364401404617 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22325R_237 c22325R_88_6 (by norm_num)

theorem c22325R_88_4 : rowsJ2 88 89 71 300 ≤ 71847758691368 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22325R_236 c22325R_88_5 (by norm_num)

theorem c22325R_88_3 : rowsJ2 88 89 67 300 ≤ 76077819576776 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22325R_235 c22325R_88_4 (by norm_num)

theorem c22325R_88_2 : rowsJ2 88 89 62 300 ≤ 77622021956708 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22325R_234 c22325R_88_3 (by norm_num)

theorem c22325R_88_1 : rowsJ2 88 89 48 300 ≤ 108752394979360 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22325R_233 c22325R_88_2 (by norm_num)

theorem c22325R_88_0 : rowsJ2 88 89 0 300 ≤ 873863547422566 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22325R_232 c22325R_88_1 (by norm_num)

theorem hr22325R_88 : rows2 88 89 ≤ 873863547422566 := rows2_le_of_rowsJ2 88 89 c22325R_88_0

theorem c22325R_89_6 : rowsJ2 89 90 81 300 ≤ 247695626552111 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22325R_246 rows22325R_247 (by norm_num)

theorem c22325R_89_5 : rowsJ2 89 90 76 300 ≤ 255142256523869 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22325R_245 c22325R_89_6 (by norm_num)

theorem c22325R_89_4 : rowsJ2 89 90 71 300 ≤ 256657268706407 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22325R_244 c22325R_89_5 (by norm_num)

theorem c22325R_89_3 : rowsJ2 89 90 67 300 ≤ 259729673192135 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22325R_243 c22325R_89_4 (by norm_num)

theorem c22325R_89_2 : rowsJ2 89 90 62 300 ≤ 261260876853759 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22325R_242 c22325R_89_3 (by norm_num)

theorem c22325R_89_1 : rowsJ2 89 90 51 300 ≤ 267471114585802 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22325R_241 c22325R_89_2 (by norm_num)

theorem c22325R_89_0 : rowsJ2 89 90 0 300 ≤ 1024919357310162 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22325R_240 c22325R_89_1 (by norm_num)

theorem hr22325R_89 : rows2 89 90 ≤ 1024919357310162 := rows2_le_of_rowsJ2 89 90 c22325R_89_0

theorem c22325R_90_6 : rowsJ2 90 91 80 300 ≤ 506121719218607 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22325R_254 rows22325R_255 (by norm_num)

theorem c22325R_90_5 : rowsJ2 90 91 75 300 ≤ 511034005457773 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22325R_253 c22325R_90_6 (by norm_num)

theorem c22325R_90_4 : rowsJ2 90 91 70 300 ≤ 512152110175517 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22325R_252 c22325R_90_5 (by norm_num)

theorem c22325R_90_3 : rowsJ2 90 91 66 300 ≤ 514688201895513 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22325R_251 c22325R_90_4 (by norm_num)

theorem c22325R_90_2 : rowsJ2 90 91 61 300 ≤ 515395588489163 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22325R_250 c22325R_90_3 (by norm_num)

theorem c22325R_90_1 : rowsJ2 90 91 52 300 ≤ 516673292167981 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22325R_249 c22325R_90_2 (by norm_num)

theorem c22325R_90_0 : rowsJ2 90 91 0 300 ≤ 1245664249173541 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22325R_248 c22325R_90_1 (by norm_num)

theorem hr22325R_90 : rows2 90 91 ≤ 1245664249173541 := rows2_le_of_rowsJ2 90 91 c22325R_90_0

theorem c22325R_91_5 : rowsJ2 91 92 75 300 ≤ 637672922888162 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22325R_261 rows22325R_262 (by norm_num)

theorem c22325R_91_4 : rowsJ2 91 92 70 300 ≤ 638194415891543 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22325R_260 c22325R_91_5 (by norm_num)

theorem c22325R_91_3 : rowsJ2 91 92 66 300 ≤ 639861828010949 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22325R_259 c22325R_91_4 (by norm_num)

theorem c22325R_91_2 : rowsJ2 91 92 61 300 ≤ 640562179767407 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22325R_258 c22325R_91_3 (by norm_num)

theorem c22325R_91_1 : rowsJ2 91 92 53 300 ≤ 640562179767407 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22325R_257 c22325R_91_2 (by norm_num)

theorem c22325R_91_0 : rowsJ2 91 92 0 300 ≤ 1340968285949596 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22325R_256 c22325R_91_1 (by norm_num)

theorem hr22325R_91 : rows2 91 92 ≤ 1340968285949596 := rows2_le_of_rowsJ2 91 92 c22325R_91_0

theorem c22325R_92_5 : rowsJ2 92 93 75 300 ≤ 877213240910137 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22325R_268 rows22325R_269 (by norm_num)

theorem c22325R_92_4 : rowsJ2 92 93 70 300 ≤ 877378249165040 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22325R_267 c22325R_92_5 (by norm_num)

theorem c22325R_92_3 : rowsJ2 92 93 66 300 ≤ 878360734081650 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22325R_266 c22325R_92_4 (by norm_num)

theorem c22325R_92_2 : rowsJ2 92 93 61 300 ≤ 879054224607524 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22325R_265 c22325R_92_3 (by norm_num)

theorem c22325R_92_1 : rowsJ2 92 93 53 300 ≤ 879054224607524 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22325R_264 c22325R_92_2 (by norm_num)

theorem c22325R_92_0 : rowsJ2 92 93 0 300 ≤ 1548978008452052 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22325R_263 c22325R_92_1 (by norm_num)

theorem hr22325R_92 : rows2 92 93 ≤ 1548978008452052 := rows2_le_of_rowsJ2 92 93 c22325R_92_0

theorem c22325R_93_5 : rowsJ2 93 94 76 300 ≤ 990212875400332 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22325R_275 rows22325R_276 (by norm_num)

theorem c22325R_93_4 : rowsJ2 93 94 71 300 ≤ 990212875400332 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22325R_274 c22325R_93_5 (by norm_num)

theorem c22325R_93_3 : rowsJ2 93 94 66 300 ≤ 990715839975939 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22325R_273 c22325R_93_4 (by norm_num)

theorem c22325R_93_2 : rowsJ2 93 94 61 300 ≤ 991228665353466 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22325R_272 c22325R_93_3 (by norm_num)

theorem c22325R_93_1 : rowsJ2 93 94 53 300 ≤ 991228665353466 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22325R_271 c22325R_93_2 (by norm_num)

theorem c22325R_93_0 : rowsJ2 93 94 0 300 ≤ 1634155949179343 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22325R_270 c22325R_93_1 (by norm_num)

theorem hr22325R_93 : rows2 93 94 ≤ 1634155949179343 := rows2_le_of_rowsJ2 93 94 c22325R_93_0

theorem c22325R_94_5 : rowsJ2 94 95 76 300 ≤ 1214086099528556 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22325R_282 rows22325R_283 (by norm_num)

theorem c22325R_94_4 : rowsJ2 94 95 71 300 ≤ 1214086099528556 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22325R_281 c22325R_94_5 (by norm_num)

theorem c22325R_94_3 : rowsJ2 94 95 66 300 ≤ 1214245295243598 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22325R_280 c22325R_94_4 (by norm_num)

theorem c22325R_94_2 : rowsJ2 94 95 61 300 ≤ 1214623338679239 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22325R_279 c22325R_94_3 (by norm_num)

theorem c22325R_94_1 : rowsJ2 94 95 53 300 ≤ 1214623338679239 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22325R_278 c22325R_94_2 (by norm_num)

theorem c22325R_94_0 : rowsJ2 94 95 0 300 ≤ 1829526153705652 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22325R_277 c22325R_94_1 (by norm_num)

theorem hr22325R_94 : rows2 94 95 ≤ 1829526153705652 := rows2_le_of_rowsJ2 94 95 c22325R_94_0

theorem c22325R_95_5 : rowsJ2 95 96 77 300 ≤ 1313342939249036 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22325R_289 rows22325R_290 (by norm_num)

theorem c22325R_95_4 : rowsJ2 95 96 71 300 ≤ 1313963227160380 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22325R_288 c22325R_95_5 (by norm_num)

theorem c22325R_95_3 : rowsJ2 95 96 66 300 ≤ 1313985859318599 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22325R_287 c22325R_95_4 (by norm_num)

theorem c22325R_95_2 : rowsJ2 95 96 61 300 ≤ 1314164151536961 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22325R_286 c22325R_95_3 (by norm_num)

theorem c22325R_95_1 : rowsJ2 95 96 53 300 ≤ 1314164151536961 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22325R_285 c22325R_95_2 (by norm_num)

theorem c22325R_95_0 : rowsJ2 95 96 0 300 ≤ 1904785370793208 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22325R_284 c22325R_95_1 (by norm_num)

theorem hr22325R_95 : rows2 95 96 ≤ 1904785370793208 := rows2_le_of_rowsJ2 95 96 c22325R_95_0

theorem c22325R_96_5 : rowsJ2 96 97 76 300 ≤ 1253568365950567 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22325R_296 rows22325R_297 (by norm_num)

theorem c22325R_96_4 : rowsJ2 96 97 70 300 ≤ 1253568365950567 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22325R_295 c22325R_96_5 (by norm_num)

theorem c22325R_96_3 : rowsJ2 96 97 65 300 ≤ 1253568365950567 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22325R_294 c22325R_96_4 (by norm_num)

theorem c22325R_96_2 : rowsJ2 96 97 60 300 ≤ 1253634721908304 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22325R_293 c22325R_96_3 (by norm_num)

theorem c22325R_96_1 : rowsJ2 96 97 53 300 ≤ 1253634721908304 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22325R_292 c22325R_96_2 (by norm_num)

theorem c22325R_96_0 : rowsJ2 96 97 0 300 ≤ 1819175587029354 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22325R_291 c22325R_96_1 (by norm_num)

theorem hr22325R_96 : rows2 96 97 ≤ 1819175587029354 := rows2_le_of_rowsJ2 96 97 c22325R_96_0

theorem c22325R_97_5 : rowsJ2 97 98 76 300 ≤ 1123115335318139 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22325R_303 rows22325R_304 (by norm_num)

theorem c22325R_97_4 : rowsJ2 97 98 70 300 ≤ 1123115335318139 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22325R_302 c22325R_97_5 (by norm_num)

theorem c22325R_97_3 : rowsJ2 97 98 65 300 ≤ 1123115335318139 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22325R_301 c22325R_97_4 (by norm_num)

theorem c22325R_97_2 : rowsJ2 97 98 60 300 ≤ 1123115335318139 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22325R_300 c22325R_97_3 (by norm_num)

theorem c22325R_97_1 : rowsJ2 97 98 53 300 ≤ 1123115335318139 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22325R_299 c22325R_97_2 (by norm_num)

theorem c22325R_97_0 : rowsJ2 97 98 0 300 ≤ 1666729169135819 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22325R_298 c22325R_97_1 (by norm_num)

theorem hr22325R_97 : rows2 97 98 ≤ 1666729169135819 := rows2_le_of_rowsJ2 97 98 c22325R_97_0

theorem c22325R_98_5 : rowsJ2 98 99 76 300 ≤ 1107686504194052 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22325R_310 rows22325R_311 (by norm_num)

theorem c22325R_98_4 : rowsJ2 98 99 70 300 ≤ 1107686504194052 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22325R_309 c22325R_98_5 (by norm_num)

theorem c22325R_98_3 : rowsJ2 98 99 65 300 ≤ 1107686504194052 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22325R_308 c22325R_98_4 (by norm_num)

theorem c22325R_98_2 : rowsJ2 98 99 60 300 ≤ 1107686504194052 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22325R_307 c22325R_98_3 (by norm_num)

theorem c22325R_98_1 : rowsJ2 98 99 53 300 ≤ 1108069532396184 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22325R_306 c22325R_98_2 (by norm_num)

theorem c22325R_98_0 : rowsJ2 98 99 0 300 ≤ 1629039055175193 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22325R_305 c22325R_98_1 (by norm_num)

theorem hr22325R_98 : rows2 98 99 ≤ 1629039055175193 := rows2_le_of_rowsJ2 98 99 c22325R_98_0

theorem c22325R_99_5 : rowsJ2 99 100 76 300 ≤ 980465612779603 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22325R_317 rows22325R_318 (by norm_num)

theorem c22325R_99_4 : rowsJ2 99 100 70 300 ≤ 980465612779603 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22325R_316 c22325R_99_5 (by norm_num)

theorem c22325R_99_3 : rowsJ2 99 100 65 300 ≤ 980465612779603 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22325R_315 c22325R_99_4 (by norm_num)

theorem c22325R_99_2 : rowsJ2 99 100 60 300 ≤ 980465612779603 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22325R_314 c22325R_99_3 (by norm_num)

theorem c22325R_99_1 : rowsJ2 99 100 53 300 ≤ 981666354488043 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22325R_313 c22325R_99_2 (by norm_num)

theorem c22325R_99_0 : rowsJ2 99 100 0 300 ≤ 1482748825218079 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22325R_312 c22325R_99_1 (by norm_num)

theorem hr22325R_99 : rows2 99 100 ≤ 1482748825218079 := rows2_le_of_rowsJ2 99 100 c22325R_99_0

theorem c22325R_100_4 : rowsJ2 100 101 70 300 ≤ 966382496897180 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22325R_323 rows22325R_324 (by norm_num)

theorem c22325R_100_3 : rowsJ2 100 101 65 300 ≤ 966382496897180 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22325R_322 c22325R_100_4 (by norm_num)

theorem c22325R_100_2 : rowsJ2 100 101 60 300 ≤ 966382496897180 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22325R_321 c22325R_100_3 (by norm_num)

theorem c22325R_100_1 : rowsJ2 100 101 53 300 ≤ 969012598119802 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22325R_320 c22325R_100_2 (by norm_num)

theorem c22325R_100_0 : rowsJ2 100 101 0 300 ≤ 1448836681731784 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22325R_319 c22325R_100_1 (by norm_num)

theorem hr22325R_100 : rows2 100 101 ≤ 1448836681731784 := rows2_le_of_rowsJ2 100 101 c22325R_100_0

theorem c22325R_101_4 : rowsJ2 101 102 69 300 ≤ 842325729768152 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22325R_329 rows22325R_330 (by norm_num)

theorem c22325R_101_3 : rowsJ2 101 102 64 300 ≤ 842325729768152 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22325R_328 c22325R_101_4 (by norm_num)

theorem c22325R_101_2 : rowsJ2 101 102 59 300 ≤ 842325729768152 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22325R_327 c22325R_101_3 (by norm_num)

theorem c22325R_101_1 : rowsJ2 101 102 53 300 ≤ 846972815978983 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22325R_326 c22325R_101_2 (by norm_num)

theorem c22325R_101_0 : rowsJ2 101 102 0 300 ≤ 1308420307137739 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22325R_325 c22325R_101_1 (by norm_num)

theorem hr22325R_101 : rows2 101 102 ≤ 1308420307137739 := rows2_le_of_rowsJ2 101 102 c22325R_101_0

theorem c22325R_102_4 : rowsJ2 102 103 70 300 ≤ 829628881316737 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22325R_335 rows22325R_336 (by norm_num)

theorem c22325R_102_3 : rowsJ2 102 103 64 300 ≤ 829628881316737 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22325R_334 c22325R_102_4 (by norm_num)

theorem c22325R_102_2 : rowsJ2 102 103 59 300 ≤ 829628881316737 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22325R_333 c22325R_102_3 (by norm_num)

theorem c22325R_102_1 : rowsJ2 102 103 53 300 ≤ 837148040273236 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22325R_332 c22325R_102_2 (by norm_num)

theorem c22325R_102_0 : rowsJ2 102 103 0 300 ≤ 1278857742246502 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22325R_331 c22325R_102_1 (by norm_num)

theorem hr22325R_102 : rows2 102 103 ≤ 1278857742246502 := rows2_le_of_rowsJ2 102 103 c22325R_102_0

theorem c22325R_103_4 : rowsJ2 103 104 70 300 ≤ 708591210123288 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22325R_341 rows22325R_342 (by norm_num)

theorem c22325R_103_3 : rowsJ2 103 104 64 300 ≤ 708591210123288 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22325R_340 c22325R_103_4 (by norm_num)

theorem c22325R_103_2 : rowsJ2 103 104 59 300 ≤ 708591210123288 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22325R_339 c22325R_103_3 (by norm_num)

theorem c22325R_103_1 : rowsJ2 103 104 52 300 ≤ 722378311802968 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22325R_338 c22325R_103_2 (by norm_num)

theorem c22325R_103_0 : rowsJ2 103 104 0 300 ≤ 1144481100413017 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22325R_337 c22325R_103_1 (by norm_num)

theorem hr22325R_103 : rows2 103 104 ≤ 1144481100413017 := rows2_le_of_rowsJ2 103 104 c22325R_103_0

theorem c22325R_104_4 : rowsJ2 104 105 69 300 ≤ 697339485848962 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22325R_347 rows22325R_348 (by norm_num)

theorem c22325R_104_3 : rowsJ2 104 105 63 300 ≤ 697339485848962 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22325R_346 c22325R_104_4 (by norm_num)

theorem c22325R_104_2 : rowsJ2 104 105 58 300 ≤ 699657723220165 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22325R_345 c22325R_104_3 (by norm_num)

theorem c22325R_104_1 : rowsJ2 104 105 52 300 ≤ 716362921695168 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22325R_344 c22325R_104_2 (by norm_num)

theorem c22325R_104_0 : rowsJ2 104 105 0 300 ≤ 1119905905727381 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22325R_343 c22325R_104_1 (by norm_num)

theorem hr22325R_104 : rows2 104 105 ≤ 1119905905727381 := rows2_le_of_rowsJ2 104 105 c22325R_104_0

theorem c22325R_105_4 : rowsJ2 105 106 69 300 ≤ 579275893397173 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22325R_353 rows22325R_354 (by norm_num)

theorem c22325R_105_3 : rowsJ2 105 106 63 300 ≤ 579275893397173 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22325R_352 c22325R_105_4 (by norm_num)

theorem c22325R_105_2 : rowsJ2 105 106 58 300 ≤ 583829159519681 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22325R_351 c22325R_105_3 (by norm_num)

theorem c22325R_105_1 : rowsJ2 105 106 52 300 ≤ 604219664261012 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22325R_350 c22325R_105_2 (by norm_num)

theorem c22325R_105_0 : rowsJ2 105 106 0 300 ≤ 991853968375335 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22325R_349 c22325R_105_1 (by norm_num)

theorem hr22325R_105 : rows2 105 106 ≤ 991853968375335 := rows2_le_of_rowsJ2 105 106 c22325R_105_0

theorem c22325R_106_4 : rowsJ2 106 107 69 300 ≤ 569548581628083 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22325R_359 rows22325R_360 (by norm_num)

theorem c22325R_106_3 : rowsJ2 106 107 63 300 ≤ 569548581628083 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22325R_358 c22325R_106_4 (by norm_num)

theorem c22325R_106_2 : rowsJ2 106 107 58 300 ≤ 576954905154873 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22325R_357 c22325R_106_3 (by norm_num)

theorem c22325R_106_1 : rowsJ2 106 107 52 300 ≤ 601337034034791 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22325R_356 c22325R_106_2 (by norm_num)

theorem c22325R_106_0 : rowsJ2 106 107 0 300 ≤ 971932515969088 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22325R_355 c22325R_106_1 (by norm_num)

theorem hr22325R_106 : rows2 106 107 ≤ 971932515969088 := rows2_le_of_rowsJ2 106 107 c22325R_106_0

theorem c22325R_107_4 : rowsJ2 107 108 69 300 ≤ 454335568047210 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22325R_365 rows22325R_366 (by norm_num)

theorem c22325R_107_3 : rowsJ2 107 108 63 300 ≤ 454335568047210 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22325R_364 c22325R_107_4 (by norm_num)

theorem c22325R_107_2 : rowsJ2 107 108 58 300 ≤ 464646688476555 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22325R_363 c22325R_107_3 (by norm_num)

theorem c22325R_107_1 : rowsJ2 107 108 52 300 ≤ 493072318677370 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22325R_362 c22325R_107_2 (by norm_num)

theorem c22325R_107_0 : rowsJ2 107 108 0 300 ≤ 849418489085766 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22325R_361 c22325R_107_1 (by norm_num)

theorem hr22325R_107 : rows2 107 108 ≤ 849418489085766 := rows2_le_of_rowsJ2 107 108 c22325R_107_0

theorem c22325R_108_4 : rowsJ2 108 109 68 300 ≤ 446234738660011 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22325R_371 rows22325R_372 (by norm_num)

theorem c22325R_108_3 : rowsJ2 108 109 62 300 ≤ 447867227512555 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22325R_370 c22325R_108_4 (by norm_num)

theorem c22325R_108_2 : rowsJ2 108 109 57 300 ≤ 464957215690077 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22325R_369 c22325R_108_3 (by norm_num)

theorem c22325R_108_1 : rowsJ2 108 109 51 300 ≤ 497581764499605 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22325R_368 c22325R_108_2 (by norm_num)

theorem c22325R_108_0 : rowsJ2 108 109 0 300 ≤ 833510695963508 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22325R_367 c22325R_108_1 (by norm_num)

theorem hr22325R_108 : rows2 108 109 ≤ 833510695963508 := rows2_le_of_rowsJ2 108 109 c22325R_108_0

theorem c22325R_109_3 : rowsJ2 109 110 63 300 ≤ 335254652168307 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22325R_376 rows22325R_377 (by norm_num)

theorem c22325R_109_2 : rowsJ2 109 110 57 300 ≤ 356104567531148 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22325R_375 c22325R_109_3 (by norm_num)

theorem c22325R_109_1 : rowsJ2 109 110 51 300 ≤ 392862391579688 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22325R_374 c22325R_109_2 (by norm_num)

theorem c22325R_109_0 : rowsJ2 109 110 0 300 ≤ 715535199557380 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22325R_373 c22325R_109_1 (by norm_num)

theorem hr22325R_109 : rows2 109 110 ≤ 715535199557380 := rows2_le_of_rowsJ2 109 110 c22325R_109_0

theorem c22325R_110_3 : rowsJ2 110 111 63 300 ≤ 330076334221006 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22325R_381 rows22325R_382 (by norm_num)

theorem c22325R_110_2 : rowsJ2 110 111 57 300 ≤ 353301339904627 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22325R_380 c22325R_110_3 (by norm_num)

theorem c22325R_110_1 : rowsJ2 110 111 51 300 ≤ 394525783321579 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22325R_379 c22325R_110_2 (by norm_num)

theorem c22325R_110_0 : rowsJ2 110 111 0 300 ≤ 703081876603650 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22325R_378 c22325R_110_1 (by norm_num)

theorem hr22325R_110 : rows2 110 111 ≤ 703081876603650 := rows2_le_of_rowsJ2 110 111 c22325R_110_0

theorem c22325R_111_3 : rowsJ2 111 112 63 300 ≤ 222582270183040 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22325R_386 rows22325R_387 (by norm_num)

theorem c22325R_111_2 : rowsJ2 111 112 57 300 ≤ 247651105418766 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22325R_385 c22325R_111_3 (by norm_num)

theorem c22325R_111_1 : rowsJ2 111 112 51 300 ≤ 292840373331291 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22325R_384 c22325R_111_2 (by norm_num)

theorem c22325R_111_0 : rowsJ2 111 112 0 300 ≤ 589814016966968 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22325R_383 c22325R_111_1 (by norm_num)

theorem hr22325R_111 : rows2 111 112 ≤ 589814016966968 := rows2_le_of_rowsJ2 111 112 c22325R_111_0

theorem c22325R_112_3 : rowsJ2 112 113 62 300 ≤ 223820820050454 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22325R_391 rows22325R_392 (by norm_num)

theorem c22325R_112_2 : rowsJ2 112 113 56 300 ≤ 255688498494296 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22325R_390 c22325R_112_3 (by norm_num)

theorem c22325R_112_1 : rowsJ2 112 113 50 300 ≤ 304362186730383 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22325R_389 c22325R_112_2 (by norm_num)

theorem c22325R_112_0 : rowsJ2 112 113 0 300 ≤ 581936590775767 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22325R_388 c22325R_112_1 (by norm_num)

theorem hr22325R_112 : rows2 112 113 ≤ 581936590775767 := rows2_le_of_rowsJ2 112 113 c22325R_112_0

theorem c22325R_113_3 : rowsJ2 113 114 62 300 ≤ 117038027166551 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22325R_396 rows22325R_397 (by norm_num)

theorem c22325R_113_2 : rowsJ2 113 114 56 300 ≤ 149969562795964 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22325R_395 c22325R_113_3 (by norm_num)

theorem c22325R_113_1 : rowsJ2 113 114 50 300 ≤ 202579978711214 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22325R_394 c22325R_113_2 (by norm_num)

theorem c22325R_113_0 : rowsJ2 113 114 0 300 ≤ 469781929754581 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22325R_393 c22325R_113_1 (by norm_num)

theorem hr22325R_113 : rows2 113 114 ≤ 469781929754581 := rows2_le_of_rowsJ2 113 114 c22325R_113_0

theorem c22325R_114_3 : rowsJ2 114 115 62 300 ≤ 116821392583892 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22325R_401 rows22325R_402 (by norm_num)

theorem c22325R_114_2 : rowsJ2 114 115 56 300 ≤ 150566769355730 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22325R_400 c22325R_114_3 (by norm_num)

theorem c22325R_114_1 : rowsJ2 114 115 50 300 ≤ 207375096270926 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22325R_399 c22325R_114_2 (by norm_num)

theorem c22325R_114_0 : rowsJ2 114 115 0 300 ≤ 463363090515364 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22325R_398 c22325R_114_1 (by norm_num)

theorem hr22325R_114 : rows2 114 115 ≤ 463363090515364 := rows2_le_of_rowsJ2 114 115 c22325R_114_0

theorem c22325R_115_3 : rowsJ2 115 116 61 300 ≤ 13702141525583 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22325R_406 rows22325R_407 (by norm_num)

theorem c22325R_115_2 : rowsJ2 115 116 55 300 ≤ 53483065345367 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22325R_405 c22325R_115_3 (by norm_num)

theorem c22325R_115_1 : rowsJ2 115 116 49 300 ≤ 112592128543398 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22325R_404 c22325R_115_2 (by norm_num)

theorem c22325R_115_0 : rowsJ2 115 116 0 300 ≤ 351637713076605 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22325R_403 c22325R_115_1 (by norm_num)

theorem hr22325R_115 : rows2 115 116 ≤ 351637713076605 := rows2_le_of_rowsJ2 115 116 c22325R_115_0

theorem c22325R_116_3 : rowsJ2 116 117 62 300 ≤ 10190601664116 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22325R_411 rows22325R_412 (by norm_num)

theorem c22325R_116_2 : rowsJ2 116 117 55 300 ≤ 53575214354631 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22325R_410 c22325R_116_3 (by norm_num)

theorem c22325R_116_1 : rowsJ2 116 117 49 300 ≤ 116885527616663 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22325R_409 c22325R_116_2 (by norm_num)

theorem c22325R_116_0 : rowsJ2 116 117 0 300 ≤ 346027652697928 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22325R_408 c22325R_116_1 (by norm_num)

theorem hr22325R_116 : rows2 116 117 ≤ 346027652697928 := rows2_le_of_rowsJ2 116 117 c22325R_116_0

theorem c22325R_117_3 : rowsJ2 117 118 62 300 ≤ 9497501405567 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22325R_416 rows22325R_417 (by norm_num)

theorem c22325R_117_2 : rowsJ2 117 118 55 300 ≤ 52352159381647 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22325R_415 c22325R_117_3 (by norm_num)

theorem c22325R_117_1 : rowsJ2 117 118 49 300 ≤ 118822235940365 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22325R_414 c22325R_117_2 (by norm_num)

theorem c22325R_117_0 : rowsJ2 117 118 0 300 ≤ 340446861772516 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22325R_413 c22325R_117_1 (by norm_num)

theorem hr22325R_117 : rows2 117 118 ≤ 340446861772516 := rows2_le_of_rowsJ2 117 118 c22325R_117_0

theorem c22325R_118_3 : rowsJ2 118 119 62 300 ≤ 110047587097646 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22325R_421 rows22325R_422 (by norm_num)

theorem c22325R_118_2 : rowsJ2 118 119 55 300 ≤ 152106816543787 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22325R_420 c22325R_118_3 (by norm_num)

theorem c22325R_118_1 : rowsJ2 118 119 49 300 ≤ 221926542657036 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22325R_419 c22325R_118_2 (by norm_num)

theorem c22325R_118_0 : rowsJ2 118 119 0 300 ≤ 435532737383229 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22325R_418 c22325R_118_1 (by norm_num)

theorem hr22325R_118 : rows2 118 119 ≤ 435532737383229 := rows2_le_of_rowsJ2 118 119 c22325R_118_0

theorem c22325R_119_2 : rowsJ2 119 120 55 300 ≤ 349574739312673 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22325R_425 rows22325R_426 (by norm_num)

theorem c22325R_119_1 : rowsJ2 119 120 48 300 ≤ 431726014716990 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22325R_424 c22325R_119_2 (by norm_num)

theorem c22325R_119_0 : rowsJ2 119 120 0 300 ≤ 629593458020938 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22325R_423 c22325R_119_1 (by norm_num)

theorem hr22325R_119 : rows2 119 120 ≤ 629593458020938 := rows2_le_of_rowsJ2 119 120 c22325R_119_0

theorem c22325R_120_2 : rowsJ2 120 121 55 300 ≤ 542813704574148 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22325R_429 rows22325R_430 (by norm_num)

theorem c22325R_120_1 : rowsJ2 120 121 48 300 ≤ 627970471891225 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22325R_428 c22325R_120_2 (by norm_num)

theorem c22325R_120_0 : rowsJ2 120 121 0 300 ≤ 819088906294997 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22325R_427 c22325R_120_1 (by norm_num)

theorem hr22325R_120 : rows2 120 121 ≤ 819088906294997 := rows2_le_of_rowsJ2 120 121 c22325R_120_0

theorem c22325R_121_2 : rowsJ2 121 122 55 300 ≤ 731357637694332 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22325R_433 rows22325R_434 (by norm_num)

theorem c22325R_121_1 : rowsJ2 121 122 48 300 ≤ 817992604182642 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22325R_432 c22325R_121_2 (by norm_num)

theorem c22325R_121_0 : rowsJ2 121 122 0 300 ≤ 1004742627802269 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22325R_431 c22325R_121_1 (by norm_num)

theorem hr22325R_121 : rows2 121 122 ≤ 1004742627802269 := rows2_le_of_rowsJ2 121 122 c22325R_121_0

theorem c22325R_122_2 : rowsJ2 122 123 54 300 ≤ 925393263267334 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22325R_437 rows22325R_438 (by norm_num)

theorem c22325R_122_1 : rowsJ2 122 123 47 300 ≤ 1015863905780111 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22325R_436 c22325R_122_2 (by norm_num)

theorem c22325R_122_0 : rowsJ2 122 123 0 300 ≤ 1186596110292051 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22325R_435 c22325R_122_1 (by norm_num)

theorem hr22325R_122 : rows2 122 123 ≤ 1186596110292051 := rows2_le_of_rowsJ2 122 123 c22325R_122_0

theorem c22325R_123_2 : rowsJ2 123 124 54 300 ≤ 1105488617272039 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22325R_441 rows22325R_442 (by norm_num)

theorem c22325R_123_1 : rowsJ2 123 124 47 300 ≤ 1197065568546361 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22325R_440 c22325R_123_2 (by norm_num)

theorem c22325R_123_0 : rowsJ2 123 124 0 300 ≤ 1364648610420825 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22325R_439 c22325R_123_1 (by norm_num)

theorem hr22325R_123 : rows2 123 124 ≤ 1364648610420825 := rows2_le_of_rowsJ2 123 124 c22325R_123_0

theorem c22325R_124_2 : rowsJ2 124 125 54 300 ≤ 1282195292133518 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22325R_445 rows22325R_446 (by norm_num)

theorem c22325R_124_1 : rowsJ2 124 125 47 300 ≤ 1374975366358669 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22325R_444 c22325R_124_2 (by norm_num)

theorem c22325R_124_0 : rowsJ2 124 125 0 300 ≤ 1539317557232482 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22325R_443 c22325R_124_1 (by norm_num)

theorem hr22325R_124 : rows2 124 125 ≤ 1539317557232482 := rows2_le_of_rowsJ2 124 125 c22325R_124_0

theorem c22325R_125_2 : rowsJ2 125 126 53 300 ≤ 1464218717566321 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22325R_449 rows22325R_450 (by norm_num)

theorem c22325R_125_1 : rowsJ2 125 126 46 300 ≤ 1559969947275496 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22325R_448 c22325R_125_2 (by norm_num)

theorem c22325R_125_0 : rowsJ2 125 126 0 300 ≤ 1710544941753547 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22325R_447 c22325R_125_1 (by norm_num)

theorem hr22325R_125 : rows2 125 126 ≤ 1710544941753547 := rows2_le_of_rowsJ2 125 126 c22325R_125_0

theorem c22325R_126_2 : rowsJ2 126 127 53 300 ≤ 1633398073477113 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22325R_453 rows22325R_454 (by norm_num)

theorem c22325R_126_1 : rowsJ2 126 127 46 300 ≤ 1730041652942137 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22325R_452 c22325R_126_2 (by norm_num)

theorem c22325R_126_0 : rowsJ2 126 127 0 300 ≤ 1878740558546322 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22325R_451 c22325R_126_1 (by norm_num)

theorem hr22325R_126 : rows2 126 127 ≤ 1878740558546322 := rows2_le_of_rowsJ2 126 127 c22325R_126_0

theorem c22325R_127_2 : rowsJ2 127 128 53 300 ≤ 1789886931128277 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22325R_457 rows22325R_458 (by norm_num)

theorem c22325R_127_1 : rowsJ2 127 128 46 300 ≤ 1885484694751173 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22325R_456 c22325R_127_2 (by norm_num)

theorem c22325R_127_0 : rowsJ2 127 128 0 300 ≤ 2034476455977362 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22325R_455 c22325R_127_1 (by norm_num)

theorem hr22325R_127 : rows2 127 128 ≤ 2034476455977362 := rows2_le_of_rowsJ2 127 128 c22325R_127_0

theorem c22325R_128_1 : rowsJ2 128 129 45 300 ≤ 2053959366458335 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22325R_460 rows22325R_461 (by norm_num)

theorem c22325R_128_0 : rowsJ2 128 129 0 300 ≤ 2189130851985012 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22325R_459 c22325R_128_1 (by norm_num)

theorem hr22325R_128 : rows2 128 129 ≤ 2189130851985012 := rows2_le_of_rowsJ2 128 129 c22325R_128_0

theorem c22325R_129_1 : rowsJ2 129 130 45 300 ≤ 2195603076511059 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22325R_463 rows22325R_464 (by norm_num)

theorem c22325R_129_0 : rowsJ2 129 130 0 300 ≤ 2332359551129306 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22325R_462 c22325R_129_1 (by norm_num)

theorem hr22325R_129 : rows2 129 130 ≤ 2332359551129306 := rows2_le_of_rowsJ2 129 130 c22325R_129_0

theorem c22325R_130_1 : rowsJ2 130 131 45 300 ≤ 2345401520104246 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22325R_466 rows22325R_467 (by norm_num)

theorem c22325R_130_0 : rowsJ2 130 131 0 300 ≤ 2484016025509076 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22325R_465 c22325R_130_1 (by norm_num)

theorem hr22325R_130 : rows2 130 131 ≤ 2484016025509076 := rows2_le_of_rowsJ2 130 131 c22325R_130_0

theorem c22325R_131_1 : rowsJ2 131 132 44 300 ≤ 2507029593271625 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22325R_469 rows22325R_470 (by norm_num)

theorem c22325R_131_0 : rowsJ2 131 132 0 300 ≤ 2633596092569297 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22325R_468 c22325R_131_1 (by norm_num)

theorem hr22325R_131 : rows2 131 132 ≤ 2633596092569297 := rows2_le_of_rowsJ2 131 132 c22325R_131_0

theorem c22325R_132_1 : rowsJ2 132 133 44 300 ≤ 2643210850002384 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22325R_472 rows22325R_473 (by norm_num)

theorem c22325R_132_0 : rowsJ2 132 133 0 300 ≤ 2773021535842135 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22325R_471 c22325R_132_1 (by norm_num)

theorem hr22325R_132 : rows2 132 133 ≤ 2773021535842135 := rows2_le_of_rowsJ2 132 133 c22325R_132_0

theorem c22325R_133_1 : rowsJ2 133 134 44 300 ≤ 2784506495866771 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22325R_475 rows22325R_476 (by norm_num)

theorem c22325R_133_0 : rowsJ2 133 134 0 300 ≤ 2919515405268319 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22325R_474 c22325R_133_1 (by norm_num)

theorem hr22325R_133 : rows2 133 134 ≤ 2919515405268319 := rows2_le_of_rowsJ2 133 134 c22325R_133_0

theorem c22325R_134_1 : rowsJ2 134 135 43 300 ≤ 2942442940478197 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22325R_478 rows22325R_479 (by norm_num)

theorem c22325R_134_0 : rowsJ2 134 135 0 300 ≤ 3065406649152083 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22325R_477 c22325R_134_1 (by norm_num)

theorem hr22325R_134 : rows2 134 135 ≤ 3065406649152083 := rows2_le_of_rowsJ2 134 135 c22325R_134_0

theorem c22325R_135_1 : rowsJ2 135 136 43 300 ≤ 2923289372279237 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22325R_481 rows22325R_482 (by norm_num)

theorem c22325R_135_0 : rowsJ2 135 136 0 300 ≤ 3052718230844751 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22325R_480 c22325R_135_1 (by norm_num)

theorem hr22325R_135 : rows2 135 136 ≤ 3052718230844751 := rows2_le_of_rowsJ2 135 136 c22325R_135_0

theorem c22325R_136_1 : rowsJ2 136 137 43 300 ≤ 2914628346848798 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22325R_484 rows22325R_485 (by norm_num)

theorem c22325R_136_0 : rowsJ2 136 137 0 300 ≤ 3051256605242079 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22325R_483 c22325R_136_1 (by norm_num)

theorem hr22325R_136 : rows2 136 137 ≤ 3051256605242079 := rows2_le_of_rowsJ2 136 137 c22325R_136_0

theorem c22325R_137_1 : rowsJ2 137 138 42 300 ≤ 2924081313261621 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22325R_487 rows22325R_488 (by norm_num)

theorem c22325R_137_0 : rowsJ2 137 138 0 300 ≤ 3049749621585431 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22325R_486 c22325R_137_1 (by norm_num)

theorem hr22325R_137 : rows2 137 138 ≤ 3049749621585431 := rows2_le_of_rowsJ2 137 138 c22325R_137_0

theorem c22325R_138_1 : rowsJ2 138 139 42 300 ≤ 2906788937935423 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22325R_490 rows22325R_491 (by norm_num)

theorem c22325R_138_0 : rowsJ2 138 139 0 300 ≤ 3041027629243963 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22325R_489 c22325R_138_1 (by norm_num)

theorem hr22325R_138 : rows2 138 139 ≤ 3041027629243963 := rows2_le_of_rowsJ2 138 139 c22325R_138_0

theorem c22325R_139_0 : rowsJ2 139 140 0 300 ≤ 3041150692714696 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22325R_492 rows22325R_493 (by norm_num)

theorem hr22325R_139 : rows2 139 140 ≤ 3041150692714696 := rows2_le_of_rowsJ2 139 140 c22325R_139_0

theorem c22325R_140_0 : rowsJ2 140 141 0 300 ≤ 3043500290232713 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22325R_494 rows22325R_495 (by norm_num)

theorem hr22325R_140 : rows2 140 141 ≤ 3043500290232713 := rows2_le_of_rowsJ2 140 141 c22325R_140_0

theorem c22325R_141_0 : rowsJ2 141 142 0 300 ≤ 3035958826866628 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22325R_496 rows22325R_497 (by norm_num)

theorem hr22325R_141 : rows2 141 142 ≤ 3035958826866628 := rows2_le_of_rowsJ2 141 142 c22325R_141_0

theorem c22325R_142_0 : rowsJ2 142 143 0 300 ≤ 3041695970225391 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22325R_498 rows22325R_499 (by norm_num)

theorem hr22325R_142 : rows2 142 143 ≤ 3041695970225391 := rows2_le_of_rowsJ2 142 143 c22325R_142_0

theorem c22325R_143_0 : rowsJ2 143 144 0 300 ≤ 3048419116814418 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22325R_500 rows22325R_501 (by norm_num)

theorem hr22325R_143 : rows2 143 144 ≤ 3048419116814418 := rows2_le_of_rowsJ2 143 144 c22325R_143_0

theorem c22325R_144_0 : rowsJ2 144 145 0 300 ≤ 3050153839035533 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22325R_502 rows22325R_503 (by norm_num)

theorem hr22325R_144 : rows2 144 145 ≤ 3050153839035533 := rows2_le_of_rowsJ2 144 145 c22325R_144_0

theorem c22325R_145_0 : rowsJ2 145 146 0 300 ≤ 3061548859121400 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22325R_504 rows22325R_505 (by norm_num)

theorem hr22325R_145 : rows2 145 146 ≤ 3061548859121400 := rows2_le_of_rowsJ2 145 146 c22325R_145_0

theorem c22325R_146_0 : rowsJ2 146 147 0 300 ≤ 3076797524267719 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22325R_506 rows22325R_507 (by norm_num)

theorem hr22325R_146 : rows2 146 147 ≤ 3076797524267719 := rows2_le_of_rowsJ2 146 147 c22325R_146_0

theorem c22325R_147_0 : rowsJ2 147 148 0 300 ≤ 3082992216820678 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22325R_508 rows22325R_509 (by norm_num)

theorem hr22325R_147 : rows2 147 148 ≤ 3082992216820678 := rows2_le_of_rowsJ2 147 148 c22325R_147_0

theorem c22325R_148_0 : rowsJ2 148 149 0 300 ≤ 3102092148463477 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22325R_510 rows22325R_511 (by norm_num)

theorem hr22325R_148 : rows2 148 149 ≤ 3102092148463477 := rows2_le_of_rowsJ2 148 149 c22325R_148_0

theorem c22325R_149_0 : rowsJ2 149 150 0 300 ≤ 3120909268460847 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22325R_512 rows22325R_513 (by norm_num)

theorem hr22325R_149 : rows2 149 150 ≤ 3120909268460847 := rows2_le_of_rowsJ2 149 150 c22325R_149_0

theorem c22325R_150_0 : rowsJ2 150 151 0 300 ≤ 3134458931933079 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22325R_514 rows22325R_515 (by norm_num)

theorem hr22325R_150 : rows2 150 151 ≤ 3134458931933079 := rows2_le_of_rowsJ2 150 151 c22325R_150_0

theorem c22325R_151_0 : rowsJ2 151 152 0 300 ≤ 3146424457082513 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22325R_516 rows22325R_517 (by norm_num)

theorem hr22325R_151 : rows2 151 152 ≤ 3146424457082513 := rows2_le_of_rowsJ2 151 152 c22325R_151_0

theorem c22325R_152_0 : rowsJ2 152 153 0 300 ≤ 3160679015570839 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22325R_518 rows22325R_519 (by norm_num)

theorem hr22325R_152 : rows2 152 153 ≤ 3160679015570839 := rows2_le_of_rowsJ2 152 153 c22325R_152_0

theorem c22325R_153_0 : rowsJ2 153 154 0 300 ≤ 3174109237391037 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22325R_520 rows22325R_521 (by norm_num)

theorem hr22325R_153 : rows2 153 154 ≤ 3174109237391037 := rows2_le_of_rowsJ2 153 154 c22325R_153_0

theorem t22325R_168 : rows2 293 300 ≤ 97904218871846398 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_559 rows22325R_560 (by norm_num)

theorem t22325R_167 : rows2 289 300 ≤ 148515077131875120 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_558 t22325R_168 (by norm_num)

theorem t22325R_166 : rows2 284 300 ≤ 207121507076245597 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_557 t22325R_167 (by norm_num)

theorem t22325R_165 : rows2 234 300 ≤ 249358342099524902 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_556 t22325R_166 (by norm_num)

theorem t22325R_164 : rows2 230 300 ≤ 291234326476752886 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_555 t22325R_165 (by norm_num)

theorem t22325R_163 : rows2 227 300 ≤ 322312647718793031 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_554 t22325R_164 (by norm_num)

theorem t22325R_162 : rows2 224 300 ≤ 353267503792273127 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_553 t22325R_163 (by norm_num)

theorem t22325R_161 : rows2 221 300 ≤ 383855313191321053 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_552 t22325R_162 (by norm_num)

theorem t22325R_160 : rows2 218 300 ≤ 414294245816475262 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_551 t22325R_161 (by norm_num)

theorem t22325R_159 : rows2 215 300 ≤ 444381554237996195 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_550 t22325R_160 (by norm_num)

theorem t22325R_158 : rows2 212 300 ≤ 474349341034540306 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_549 t22325R_159 (by norm_num)

theorem t22325R_157 : rows2 209 300 ≤ 503988171164936153 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_548 t22325R_158 (by norm_num)

theorem t22325R_156 : rows2 206 300 ≤ 533480536960572020 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_547 t22325R_157 (by norm_num)

theorem t22325R_155 : rows2 203 300 ≤ 562160657188008230 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_546 t22325R_156 (by norm_num)

theorem t22325R_154 : rows2 200 300 ≤ 589554906013973171 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_545 t22325R_155 (by norm_num)

theorem t22325R_153 : rows2 197 300 ≤ 615815463579198508 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_544 t22325R_154 (by norm_num)

theorem t22325R_152 : rows2 194 300 ≤ 640962694361397070 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_543 t22325R_153 (by norm_num)

theorem t22325R_151 : rows2 191 300 ≤ 665174673915871737 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_542 t22325R_152 (by norm_num)

theorem t22325R_150 : rows2 188 300 ≤ 688499528664604349 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_541 t22325R_151 (by norm_num)

theorem t22325R_149 : rows2 184 300 ≤ 718472263725204822 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_540 t22325R_150 (by norm_num)

theorem t22325R_148 : rows2 180 300 ≤ 746297396765602774 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_539 t22325R_149 (by norm_num)

theorem t22325R_147 : rows2 177 300 ≤ 765525224407620860 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_538 t22325R_148 (by norm_num)

theorem t22325R_146 : rows2 174 300 ≤ 783389674936601750 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_537 t22325R_147 (by norm_num)

theorem t22325R_145 : rows2 171 300 ≤ 799921947770111113 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_536 t22325R_146 (by norm_num)

theorem t22325R_144 : rows2 169 300 ≤ 810207288243304052 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_535 t22325R_145 (by norm_num)

theorem t22325R_143 : rows2 167 300 ≤ 819903453220427449 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_534 t22325R_144 (by norm_num)

theorem t22325R_142 : rows2 165 300 ≤ 829011512453989014 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_533 t22325R_143 (by norm_num)

theorem t22325R_141 : rows2 164 300 ≤ 833345578915540627 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_532 t22325R_142 (by norm_num)

theorem t22325R_140 : rows2 163 300 ≤ 837533458711942883 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_531 t22325R_141 (by norm_num)

theorem t22325R_139 : rows2 162 300 ≤ 841575534910180145 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_530 t22325R_140 (by norm_num)

theorem t22325R_138 : rows2 161 300 ≤ 845472198238079398 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_529 t22325R_139 (by norm_num)

theorem t22325R_137 : rows2 160 300 ≤ 849223783050489317 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_528 t22325R_138 (by norm_num)

theorem t22325R_136 : rows2 159 300 ≤ 852830628534216725 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_527 t22325R_137 (by norm_num)

theorem t22325R_135 : rows2 158 300 ≤ 856290760897627383 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_526 t22325R_136 (by norm_num)

theorem t22325R_134 : rows2 157 300 ≤ 859598973121750679 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_525 t22325R_135 (by norm_num)

theorem t22325R_133 : rows2 156 300 ≤ 862822538038238975 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_524 t22325R_134 (by norm_num)

theorem t22325R_132 : rows2 155 300 ≤ 866028269659529657 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_523 t22325R_133 (by norm_num)

theorem t22325R_131 : rows2 154 300 ≤ 869218726543500214 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_522 t22325R_132 (by norm_num)

theorem t22325R_130 : rows2 153 300 ≤ 872392835780891251 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_153 t22325R_131 (by norm_num)

theorem t22325R_129 : rows2 152 300 ≤ 875553514796462090 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_152 t22325R_130 (by norm_num)

theorem t22325R_128 : rows2 151 300 ≤ 878699939253544603 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_151 t22325R_129 (by norm_num)

theorem t22325R_127 : rows2 150 300 ≤ 881834398185477682 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_150 t22325R_128 (by norm_num)

theorem t22325R_126 : rows2 149 300 ≤ 884955307453938529 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_149 t22325R_127 (by norm_num)

theorem t22325R_125 : rows2 148 300 ≤ 888057399602402006 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_148 t22325R_126 (by norm_num)

theorem t22325R_124 : rows2 147 300 ≤ 891140391819222684 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_147 t22325R_125 (by norm_num)

theorem t22325R_123 : rows2 146 300 ≤ 894217189343490403 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_146 t22325R_124 (by norm_num)

theorem t22325R_122 : rows2 145 300 ≤ 897278738202611803 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_145 t22325R_123 (by norm_num)

theorem t22325R_121 : rows2 144 300 ≤ 900328892041647336 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_144 t22325R_122 (by norm_num)

theorem t22325R_120 : rows2 143 300 ≤ 903377311158461754 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_143 t22325R_121 (by norm_num)

theorem t22325R_119 : rows2 142 300 ≤ 906419007128687145 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_142 t22325R_120 (by norm_num)

theorem t22325R_118 : rows2 141 300 ≤ 909454965955553773 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_141 t22325R_119 (by norm_num)

theorem t22325R_117 : rows2 140 300 ≤ 912498466245786486 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_140 t22325R_118 (by norm_num)

theorem t22325R_116 : rows2 139 300 ≤ 915539616938501182 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_139 t22325R_117 (by norm_num)

theorem t22325R_115 : rows2 138 300 ≤ 918580644567745145 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_138 t22325R_116 (by norm_num)

theorem t22325R_114 : rows2 137 300 ≤ 921630394189330576 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_137 t22325R_115 (by norm_num)

theorem t22325R_113 : rows2 136 300 ≤ 924681650794572655 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_136 t22325R_114 (by norm_num)

theorem t22325R_112 : rows2 135 300 ≤ 927734369025417406 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_135 t22325R_113 (by norm_num)

theorem t22325R_111 : rows2 134 300 ≤ 930799775674569489 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_134 t22325R_112 (by norm_num)

theorem t22325R_110 : rows2 133 300 ≤ 933719291079837808 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_133 t22325R_111 (by norm_num)

theorem t22325R_109 : rows2 132 300 ≤ 936492312615679943 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_132 t22325R_110 (by norm_num)

theorem t22325R_108 : rows2 131 300 ≤ 939125908708249240 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_131 t22325R_109 (by norm_num)

theorem t22325R_107 : rows2 130 300 ≤ 941609924733758316 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_130 t22325R_108 (by norm_num)

theorem t22325R_106 : rows2 129 300 ≤ 943942284284887622 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_129 t22325R_107 (by norm_num)

theorem t22325R_105 : rows2 128 300 ≤ 946131415136872634 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_128 t22325R_106 (by norm_num)

theorem t22325R_104 : rows2 127 300 ≤ 948165891592849996 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_127 t22325R_105 (by norm_num)

theorem t22325R_103 : rows2 126 300 ≤ 950044632151396318 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_126 t22325R_104 (by norm_num)

theorem t22325R_102 : rows2 125 300 ≤ 951755177093149865 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_125 t22325R_103 (by norm_num)

theorem t22325R_101 : rows2 124 300 ≤ 953294494650382347 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_124 t22325R_102 (by norm_num)

theorem t22325R_100 : rows2 123 300 ≤ 954659143260803172 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_123 t22325R_101 (by norm_num)

theorem t22325R_99 : rows2 122 300 ≤ 955845739371095223 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_122 t22325R_100 (by norm_num)

theorem t22325R_98 : rows2 121 300 ≤ 956850481998897492 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_121 t22325R_99 (by norm_num)

theorem t22325R_97 : rows2 120 300 ≤ 957669570905192489 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_120 t22325R_98 (by norm_num)

theorem t22325R_96 : rows2 119 300 ≤ 958299164363213427 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_119 t22325R_97 (by norm_num)

theorem t22325R_95 : rows2 118 300 ≤ 958734697100596656 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_118 t22325R_96 (by norm_num)

theorem t22325R_94 : rows2 117 300 ≤ 959075143962369172 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_117 t22325R_95 (by norm_num)

theorem t22325R_93 : rows2 116 300 ≤ 959421171615067100 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_116 t22325R_94 (by norm_num)

theorem t22325R_92 : rows2 115 300 ≤ 959772809328143705 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_115 t22325R_93 (by norm_num)

theorem t22325R_91 : rows2 114 300 ≤ 960236172418659069 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_114 t22325R_92 (by norm_num)

theorem t22325R_90 : rows2 113 300 ≤ 960705954348413650 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_113 t22325R_91 (by norm_num)

theorem t22325R_89 : rows2 112 300 ≤ 961287890939189417 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_112 t22325R_90 (by norm_num)

theorem t22325R_88 : rows2 111 300 ≤ 961877704956156385 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_111 t22325R_89 (by norm_num)

theorem t22325R_87 : rows2 110 300 ≤ 962580786832760035 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_110 t22325R_88 (by norm_num)

theorem t22325R_86 : rows2 109 300 ≤ 963296322032317415 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_109 t22325R_87 (by norm_num)

theorem t22325R_85 : rows2 108 300 ≤ 964129832728280923 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_108 t22325R_86 (by norm_num)

theorem t22325R_84 : rows2 107 300 ≤ 964979251217366689 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_107 t22325R_85 (by norm_num)

theorem t22325R_83 : rows2 106 300 ≤ 965951183733335777 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_106 t22325R_84 (by norm_num)

theorem t22325R_82 : rows2 105 300 ≤ 966943037701711112 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_105 t22325R_83 (by norm_num)

theorem t22325R_81 : rows2 104 300 ≤ 968062943607438493 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_104 t22325R_82 (by norm_num)

theorem t22325R_80 : rows2 103 300 ≤ 969207424707851510 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_103 t22325R_81 (by norm_num)

theorem t22325R_79 : rows2 102 300 ≤ 970486282450098012 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_102 t22325R_80 (by norm_num)

theorem t22325R_78 : rows2 101 300 ≤ 971794702757235751 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_101 t22325R_79 (by norm_num)

theorem t22325R_77 : rows2 100 300 ≤ 973243539438967535 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_100 t22325R_78 (by norm_num)

theorem t22325R_76 : rows2 99 300 ≤ 974726288264185614 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_99 t22325R_77 (by norm_num)

theorem t22325R_75 : rows2 98 300 ≤ 976355327319360807 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_98 t22325R_76 (by norm_num)

theorem t22325R_74 : rows2 97 300 ≤ 978022056488496626 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_97 t22325R_75 (by norm_num)

theorem t22325R_73 : rows2 96 300 ≤ 979841232075525980 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_96 t22325R_74 (by norm_num)

theorem t22325R_72 : rows2 95 300 ≤ 981746017446319188 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_95 t22325R_73 (by norm_num)

theorem t22325R_71 : rows2 94 300 ≤ 983575543600024840 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_94 t22325R_72 (by norm_num)

theorem t22325R_70 : rows2 93 300 ≤ 985209699549204183 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_93 t22325R_71 (by norm_num)

theorem t22325R_69 : rows2 92 300 ≤ 986758677557656235 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_92 t22325R_70 (by norm_num)

theorem t22325R_68 : rows2 91 300 ≤ 988099645843605831 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_91 t22325R_69 (by norm_num)

theorem t22325R_67 : rows2 90 300 ≤ 989345310092779372 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_90 t22325R_68 (by norm_num)

theorem t22325R_66 : rows2 89 300 ≤ 990370229450089534 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_89 t22325R_67 (by norm_num)

theorem t22325R_65 : rows2 88 300 ≤ 991244092997512100 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_88 t22325R_66 (by norm_num)

theorem t22325R_64 : rows2 87 300 ≤ 992140873947673506 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_87 t22325R_65 (by norm_num)

theorem t22325R_63 : rows2 86 300 ≤ 993063481384020088 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_86 t22325R_64 (by norm_num)

theorem t22325R_62 : rows2 85 300 ≤ 994019603703643514 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_85 t22325R_63 (by norm_num)

theorem t22325R_61 : rows2 84 300 ≤ 995011793085683149 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_84 t22325R_62 (by norm_num)

theorem t22325R_60 : rows2 83 300 ≤ 996046435746181917 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_83 t22325R_61 (by norm_num)

theorem t22325R_59 : rows2 82 300 ≤ 997124745066174046 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_82 t22325R_60 (by norm_num)

theorem t22325R_58 : rows2 81 300 ≤ 998252374973227119 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_81 t22325R_59 (by norm_num)

theorem t22325R_57 : rows2 80 300 ≤ 999429525348847725 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_80 t22325R_58 (by norm_num)

theorem t22325R_56 : rows2 79 300 ≤ 1000660551390187525 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_79 t22325R_57 (by norm_num)

theorem t22325R_55 : rows2 78 300 ≤ 1001945275186382824 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_78 t22325R_56 (by norm_num)

theorem t22325R_54 : rows2 77 300 ≤ 1003286947373532026 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_77 t22325R_55 (by norm_num)

theorem t22325R_53 : rows2 76 300 ≤ 1004684352087776450 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_76 t22325R_54 (by norm_num)

theorem t22325R_52 : rows2 75 300 ≤ 1006140025317737560 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_75 t22325R_53 (by norm_num)

theorem t22325R_51 : rows2 74 300 ≤ 1007652129881080635 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_74 t22325R_52 (by norm_num)

theorem t22325R_50 : rows2 73 300 ≤ 1009223389282925216 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_73 t22325R_51 (by norm_num)

theorem t22325R_49 : rows2 72 300 ≤ 1010855568169724598 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_72 t22325R_50 (by norm_num)

theorem t22325R_48 : rows2 71 300 ≤ 1012554379623132940 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_71 t22325R_49 (by norm_num)

theorem t22325R_47 : rows2 70 300 ≤ 1014318938286832932 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_70 t22325R_48 (by norm_num)

theorem t22325R_46 : rows2 69 300 ≤ 1016151216069542259 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_69 t22325R_47 (by norm_num)

theorem t22325R_45 : rows2 68 300 ≤ 1018047646686434767 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_68 t22325R_46 (by norm_num)

theorem t22325R_44 : rows2 67 300 ≤ 1020008713932729825 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_67 t22325R_45 (by norm_num)

theorem t22325R_43 : rows2 66 300 ≤ 1022030055416502011 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_66 t22325R_44 (by norm_num)

theorem t22325R_42 : rows2 65 300 ≤ 1024111105027862431 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_65 t22325R_43 (by norm_num)

theorem t22325R_41 : rows2 64 300 ≤ 1026246529867569702 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_64 t22325R_42 (by norm_num)

theorem t22325R_40 : rows2 63 300 ≤ 1028435319761902708 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_63 t22325R_41 (by norm_num)

theorem t22325R_39 : rows2 62 300 ≤ 1030671429781068912 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_62 t22325R_40 (by norm_num)

theorem t22325R_38 : rows2 61 300 ≤ 1032953110106145172 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_61 t22325R_39 (by norm_num)

theorem t22325R_37 : rows2 60 300 ≤ 1035274129661453346 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_60 t22325R_38 (by norm_num)

theorem t22325R_36 : rows2 59 300 ≤ 1037632367315500043 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_59 t22325R_37 (by norm_num)

theorem t22325R_35 : rows2 58 300 ≤ 1040021264304384078 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_58 t22325R_36 (by norm_num)

theorem t22325R_34 : rows2 57 300 ≤ 1042438798465526132 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_57 t22325R_35 (by norm_num)

theorem t22325R_33 : rows2 56 300 ≤ 1044878204872729925 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_56 t22325R_34 (by norm_num)

theorem t22325R_32 : rows2 55 300 ≤ 1047337195250365799 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_55 t22325R_33 (by norm_num)

theorem t22325R_31 : rows2 54 300 ≤ 1049809413420174873 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_54 t22325R_32 (by norm_num)

theorem t22325R_30 : rows2 53 300 ≤ 1052292970432687144 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_53 t22325R_31 (by norm_num)

theorem t22325R_29 : rows2 52 300 ≤ 1054781900792297496 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_52 t22325R_30 (by norm_num)

theorem t22325R_28 : rows2 51 300 ≤ 1057275041786966522 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_51 t22325R_29 (by norm_num)

theorem t22325R_27 : rows2 50 300 ≤ 1059766804780346351 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_50 t22325R_28 (by norm_num)

theorem t22325R_26 : rows2 49 300 ≤ 1062256304477581592 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_49 t22325R_27 (by norm_num)

theorem t22325R_25 : rows2 48 300 ≤ 1064738569467099601 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_48 t22325R_26 (by norm_num)

theorem t22325R_24 : rows2 47 300 ≤ 1067211519159057518 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_47 t22325R_25 (by norm_num)

theorem t22325R_23 : rows2 46 300 ≤ 1069686732348122333 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_46 t22325R_24 (by norm_num)

theorem t22325R_22 : rows2 45 300 ≤ 1072179694752183697 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_45 t22325R_23 (by norm_num)

theorem t22325R_21 : rows2 44 300 ≤ 1074703070845366746 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_44 t22325R_22 (by norm_num)

theorem t22325R_20 : rows2 43 300 ≤ 1077266554726693100 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_43 t22325R_21 (by norm_num)

theorem t22325R_19 : rows2 42 300 ≤ 1079877417430687918 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_42 t22325R_20 (by norm_num)

theorem t22325R_18 : rows2 41 300 ≤ 1082539311608941479 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_41 t22325R_19 (by norm_num)

theorem t22325R_17 : rows2 40 300 ≤ 1085253041684783166 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_40 t22325R_18 (by norm_num)

theorem t22325R_16 : rows2 39 300 ≤ 1088016354732233637 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_39 t22325R_17 (by norm_num)

theorem t22325R_15 : rows2 38 300 ≤ 1090824032248100485 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_38 t22325R_16 (by norm_num)

theorem t22325R_14 : rows2 37 300 ≤ 1093667782355177083 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_37 t22325R_15 (by norm_num)

theorem t22325R_13 : rows2 36 300 ≤ 1096536811667498514 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_36 t22325R_14 (by norm_num)

theorem t22325R_12 : rows2 35 300 ≤ 1099416999920281013 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22325R_35 t22325R_13 (by norm_num)

theorem t22325R_11 : rows2 34 300 ≤ 1102291576607353572 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_11 t22325R_12 (by norm_num)

theorem t22325R_10 : rows2 33 300 ≤ 1105141023656925203 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_10 t22325R_11 (by norm_num)

theorem t22325R_9 : rows2 32 300 ≤ 1107944051872809066 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_9 t22325R_10 (by norm_num)

theorem t22325R_8 : rows2 31 300 ≤ 1110677931764196555 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_8 t22325R_9 (by norm_num)

theorem t22325R_7 : rows2 30 300 ≤ 1113322590591874292 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_7 t22325R_8 (by norm_num)

theorem t22325R_6 : rows2 29 300 ≤ 1115861349411068777 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_6 t22325R_7 (by norm_num)

theorem t22325R_5 : rows2 28 300 ≤ 1118280950375582863 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_5 t22325R_6 (by norm_num)

theorem t22325R_4 : rows2 27 300 ≤ 1120571381767835831 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_4 t22325R_5 (by norm_num)

theorem t22325R_3 : rows2 25 300 ≤ 1124739187260870448 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_3 t22325R_4 (by norm_num)

theorem t22325R_2 : rows2 23 300 ≤ 1128343541021292690 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_2 t22325R_3 (by norm_num)

theorem t22325R_1 : rows2 19 300 ≤ 1133948915105036591 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_1 t22325R_2 (by norm_num)

theorem t22325R_0 : rows2 0 300 ≤ 1141112704303444843 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22325R_0 t22325R_1 (by norm_num)

/-- **The refined certificate on `grid22325R`**: the loss's bound is less than `K`, the 561 parts checked by the
kernel. -/
theorem total2_lt_22325R : total2 < K := by
  rw [total2_eq_rows2_full]
  exact lt_of_le_of_lt t22325R_0 (by decide +kernel)

end

end SieveCert

#print axioms SieveCert.total2_lt_22325R
