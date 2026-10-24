/-
# The refined certificate of the sieve route's loss at `L = 4467/2000` with `n = 300`: `total2 < K`

On `SieveGrid22335R.grid22335R` (`U1 = ⌈(40993/100000)DEN⌉`, `U2 = ⌊(47746/100000)DEN⌋`, `n = 300`),
`SieveCert.total2` is less than `K` (it is below `0.98816K`, rounded up; the certificate of `SieveCertDefs.lean` on
the same grid totals `1.09890K`): `total2` is `rows2 0 n` (`SieveCert2.total2_eq_rows2_full`), and its bound is
assembled one step at a time from the 549 parts' bounds (`rows22335R_0` … `rows22335R_548`, each by `decide +kernel`
in one of the 140 part files): a heavy row's bound from its column pieces' (`rowsJ2_le_of_split`,
`rows2_le_of_rowsJ2`), then the 170 ranges of rows from the last to the first (`rows2_le_of_split`), every bound a
literal and every step a theorem of its own (`c22335R_…`, `hr22335R_…`, `t22335R_…`); the bounds, `⌈1.001 × part⌉`
computed exactly in integers, sum to `1140404967899637341`, less than `K` by `decide +kernel` (`total2_lt_22335R`).

The file imports `SieveCert2.lean` and `SieveCert22335RP1.lean` … `SieveCert22335RP140.lean`.
-/
import SieveCert2
import SieveCert22335RP1
import SieveCert22335RP2
import SieveCert22335RP3
import SieveCert22335RP4
import SieveCert22335RP5
import SieveCert22335RP6
import SieveCert22335RP7
import SieveCert22335RP8
import SieveCert22335RP9
import SieveCert22335RP10
import SieveCert22335RP11
import SieveCert22335RP12
import SieveCert22335RP13
import SieveCert22335RP14
import SieveCert22335RP15
import SieveCert22335RP16
import SieveCert22335RP17
import SieveCert22335RP18
import SieveCert22335RP19
import SieveCert22335RP20
import SieveCert22335RP21
import SieveCert22335RP22
import SieveCert22335RP23
import SieveCert22335RP24
import SieveCert22335RP25
import SieveCert22335RP26
import SieveCert22335RP27
import SieveCert22335RP28
import SieveCert22335RP29
import SieveCert22335RP30
import SieveCert22335RP31
import SieveCert22335RP32
import SieveCert22335RP33
import SieveCert22335RP34
import SieveCert22335RP35
import SieveCert22335RP36
import SieveCert22335RP37
import SieveCert22335RP38
import SieveCert22335RP39
import SieveCert22335RP40
import SieveCert22335RP41
import SieveCert22335RP42
import SieveCert22335RP43
import SieveCert22335RP44
import SieveCert22335RP45
import SieveCert22335RP46
import SieveCert22335RP47
import SieveCert22335RP48
import SieveCert22335RP49
import SieveCert22335RP50
import SieveCert22335RP51
import SieveCert22335RP52
import SieveCert22335RP53
import SieveCert22335RP54
import SieveCert22335RP55
import SieveCert22335RP56
import SieveCert22335RP57
import SieveCert22335RP58
import SieveCert22335RP59
import SieveCert22335RP60
import SieveCert22335RP61
import SieveCert22335RP62
import SieveCert22335RP63
import SieveCert22335RP64
import SieveCert22335RP65
import SieveCert22335RP66
import SieveCert22335RP67
import SieveCert22335RP68
import SieveCert22335RP69
import SieveCert22335RP70
import SieveCert22335RP71
import SieveCert22335RP72
import SieveCert22335RP73
import SieveCert22335RP74
import SieveCert22335RP75
import SieveCert22335RP76
import SieveCert22335RP77
import SieveCert22335RP78
import SieveCert22335RP79
import SieveCert22335RP80
import SieveCert22335RP81
import SieveCert22335RP82
import SieveCert22335RP83
import SieveCert22335RP84
import SieveCert22335RP85
import SieveCert22335RP86
import SieveCert22335RP87
import SieveCert22335RP88
import SieveCert22335RP89
import SieveCert22335RP90
import SieveCert22335RP91
import SieveCert22335RP92
import SieveCert22335RP93
import SieveCert22335RP94
import SieveCert22335RP95
import SieveCert22335RP96
import SieveCert22335RP97
import SieveCert22335RP98
import SieveCert22335RP99
import SieveCert22335RP100
import SieveCert22335RP101
import SieveCert22335RP102
import SieveCert22335RP103
import SieveCert22335RP104
import SieveCert22335RP105
import SieveCert22335RP106
import SieveCert22335RP107
import SieveCert22335RP108
import SieveCert22335RP109
import SieveCert22335RP110
import SieveCert22335RP111
import SieveCert22335RP112
import SieveCert22335RP113
import SieveCert22335RP114
import SieveCert22335RP115
import SieveCert22335RP116
import SieveCert22335RP117
import SieveCert22335RP118
import SieveCert22335RP119
import SieveCert22335RP120
import SieveCert22335RP121
import SieveCert22335RP122
import SieveCert22335RP123
import SieveCert22335RP124
import SieveCert22335RP125
import SieveCert22335RP126
import SieveCert22335RP127
import SieveCert22335RP128
import SieveCert22335RP129
import SieveCert22335RP130
import SieveCert22335RP131
import SieveCert22335RP132
import SieveCert22335RP133
import SieveCert22335RP134
import SieveCert22335RP135
import SieveCert22335RP136
import SieveCert22335RP137
import SieveCert22335RP138
import SieveCert22335RP139
import SieveCert22335RP140

namespace SieveCert

section

attribute [local instance] grid22335R

/-! The chain of bounds: `c22335R_{i}_{m}` for the heavy row `i` from its `m`-th column piece on, `hr22335R_{i}` for
the heavy row `i`, `t22335R_{m}` for the rows from the `m`-th range on; each a theorem of its own, its name distinct
from the other certificates' chains in the same namespace. -/

theorem c22335R_35_0 : rowsJ2 35 36 0 300 ≤ 2876485103522262 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22335R_12 rows22335R_13 (by norm_num)

theorem hr22335R_35 : rows2 35 36 ≤ 2876485103522262 := rows2_le_of_rowsJ2 35 36 c22335R_35_0

theorem c22335R_36_0 : rowsJ2 36 37 0 300 ≤ 2865343606651047 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22335R_14 rows22335R_15 (by norm_num)

theorem hr22335R_36 : rows2 36 37 ≤ 2865343606651047 := rows2_le_of_rowsJ2 36 37 c22335R_36_0

theorem c22335R_37_0 : rowsJ2 37 38 0 300 ≤ 2840099734831551 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22335R_16 rows22335R_17 (by norm_num)

theorem hr22335R_37 : rows2 37 38 ≤ 2840099734831551 := rows2_le_of_rowsJ2 37 38 c22335R_37_0

theorem c22335R_38_0 : rowsJ2 38 39 0 300 ≤ 2804076747591715 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22335R_18 rows22335R_19 (by norm_num)

theorem hr22335R_38 : rows2 38 39 ≤ 2804076747591715 := rows2_le_of_rowsJ2 38 39 c22335R_38_0

theorem c22335R_39_0 : rowsJ2 39 40 0 300 ≤ 2759773489534451 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22335R_20 rows22335R_21 (by norm_num)

theorem hr22335R_39 : rows2 39 40 ≤ 2759773489534451 := rows2_le_of_rowsJ2 39 40 c22335R_39_0

theorem c22335R_40_0 : rowsJ2 40 41 0 300 ≤ 2710259989500697 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22335R_22 rows22335R_23 (by norm_num)

theorem hr22335R_40 : rows2 40 41 ≤ 2710259989500697 := rows2_le_of_rowsJ2 40 41 c22335R_40_0

theorem c22335R_41_0 : rowsJ2 41 42 0 300 ≤ 2658498645146369 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22335R_24 rows22335R_25 (by norm_num)

theorem hr22335R_41 : rows2 41 42 ≤ 2658498645146369 := rows2_le_of_rowsJ2 41 42 c22335R_41_0

theorem c22335R_42_0 : rowsJ2 42 43 0 300 ≤ 2607543414413695 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22335R_26 rows22335R_27 (by norm_num)

theorem hr22335R_42 : rows2 42 43 ≤ 2607543414413695 := rows2_le_of_rowsJ2 42 43 c22335R_42_0

theorem c22335R_43_0 : rowsJ2 43 44 0 300 ≤ 2560239413019382 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22335R_28 rows22335R_29 (by norm_num)

theorem hr22335R_43 : rows2 43 44 ≤ 2560239413019382 := rows2_le_of_rowsJ2 43 44 c22335R_43_0

theorem c22335R_44_1 : rowsJ2 44 45 35 300 ≤ 463255318830745 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22335R_31 rows22335R_32 (by norm_num)

theorem c22335R_44_0 : rowsJ2 44 45 0 300 ≤ 2520200915714949 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22335R_30 c22335R_44_1 (by norm_num)

theorem hr22335R_44 : rows2 44 45 ≤ 2520200915714949 := rows2_le_of_rowsJ2 44 45 c22335R_44_0

theorem c22335R_45_1 : rowsJ2 45 46 35 300 ≤ 512479820953052 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22335R_34 rows22335R_35 (by norm_num)

theorem c22335R_45_0 : rowsJ2 45 46 0 300 ≤ 2489848036616882 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22335R_33 c22335R_45_1 (by norm_num)

theorem hr22335R_45 : rows2 45 46 ≤ 2489848036616882 := rows2_le_of_rowsJ2 45 46 c22335R_45_0

theorem c22335R_46_1 : rowsJ2 46 47 35 300 ≤ 573488329195113 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22335R_37 rows22335R_38 (by norm_num)

theorem c22335R_46_0 : rowsJ2 46 47 0 300 ≤ 2472147391749288 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22335R_36 c22335R_46_1 (by norm_num)

theorem hr22335R_46 : rows2 46 47 ≤ 2472147391749288 := rows2_le_of_rowsJ2 46 47 c22335R_46_0

theorem c22335R_47_1 : rowsJ2 47 48 35 300 ≤ 649216137530008 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22335R_40 rows22335R_41 (by norm_num)

theorem c22335R_47_0 : rowsJ2 47 48 0 300 ≤ 2469916573009813 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22335R_39 c22335R_47_1 (by norm_num)

theorem hr22335R_47 : rows2 47 48 ≤ 2469916573009813 := rows2_le_of_rowsJ2 47 48 c22335R_47_0

theorem c22335R_48_1 : rowsJ2 48 49 35 300 ≤ 735366210103868 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22335R_43 rows22335R_44 (by norm_num)

theorem c22335R_48_0 : rowsJ2 48 49 0 300 ≤ 2479251945292071 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22335R_42 c22335R_48_1 (by norm_num)

theorem hr22335R_48 : rows2 48 49 ≤ 2479251945292071 := rows2_le_of_rowsJ2 48 49 c22335R_48_0

theorem c22335R_49_1 : rowsJ2 49 50 35 300 ≤ 818706895298609 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22335R_46 rows22335R_47 (by norm_num)

theorem c22335R_49_0 : rowsJ2 49 50 0 300 ≤ 2486507485676819 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22335R_45 c22335R_49_1 (by norm_num)

theorem hr22335R_49 : rows2 49 50 ≤ 2486507485676819 := rows2_le_of_rowsJ2 49 50 c22335R_49_0

theorem c22335R_50_1 : rowsJ2 50 51 35 300 ≤ 895506070112463 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22335R_49 rows22335R_50 (by norm_num)

theorem c22335R_50_0 : rowsJ2 50 51 0 300 ≤ 2488794773632266 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22335R_48 c22335R_50_1 (by norm_num)

theorem hr22335R_50 : rows2 50 51 ≤ 2488794773632266 := rows2_le_of_rowsJ2 50 51 c22335R_50_0

theorem c22335R_51_2 : rowsJ2 51 52 44 300 ≤ 610275230045627 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22335R_53 rows22335R_54 (by norm_num)

theorem c22335R_51_1 : rowsJ2 51 52 35 300 ≤ 970394369060069 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22335R_52 c22335R_51_2 (by norm_num)

theorem c22335R_51_0 : rowsJ2 51 52 0 300 ≤ 2490195921523082 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22335R_51 c22335R_51_1 (by norm_num)

theorem hr22335R_51 : rows2 51 52 ≤ 2490195921523082 := rows2_le_of_rowsJ2 51 52 c22335R_51_0

theorem c22335R_52_2 : rowsJ2 52 53 44 300 ≤ 673545428848735 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22335R_57 rows22335R_58 (by norm_num)

theorem c22335R_52_1 : rowsJ2 52 53 35 300 ≤ 1038115305284479 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22335R_56 c22335R_52_2 (by norm_num)

theorem c22335R_52_0 : rowsJ2 52 53 0 300 ≤ 2486012319897673 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22335R_55 c22335R_52_1 (by norm_num)

theorem hr22335R_52 : rows2 52 53 ≤ 2486012319897673 := rows2_le_of_rowsJ2 52 53 c22335R_52_0

theorem c22335R_53_2 : rowsJ2 53 54 44 300 ≤ 731009064961739 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22335R_61 rows22335R_62 (by norm_num)

theorem c22335R_53_1 : rowsJ2 53 54 35 300 ≤ 1103193484831679 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22335R_60 c22335R_53_2 (by norm_num)

theorem c22335R_53_0 : rowsJ2 53 54 0 300 ≤ 2480665504479103 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22335R_59 c22335R_53_1 (by norm_num)

theorem hr22335R_53 : rows2 53 54 ≤ 2480665504479103 := rows2_le_of_rowsJ2 53 54 c22335R_53_0

theorem c22335R_54_2 : rowsJ2 54 55 44 300 ≤ 777871454719036 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22335R_65 rows22335R_66 (by norm_num)

theorem c22335R_54_1 : rowsJ2 54 55 35 300 ≤ 1160387806251109 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22335R_64 c22335R_54_2 (by norm_num)

theorem c22335R_54_0 : rowsJ2 54 55 0 300 ≤ 2469357539124909 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22335R_63 c22335R_54_1 (by norm_num)

theorem hr22335R_54 : rows2 54 55 ≤ 2469357539124909 := rows2_le_of_rowsJ2 54 55 c22335R_54_0

theorem c22335R_55_2 : rowsJ2 55 56 44 300 ≤ 818281057647434 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22335R_69 rows22335R_70 (by norm_num)

theorem c22335R_55_1 : rowsJ2 55 56 35 300 ≤ 1214189186869261 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22335R_68 c22335R_55_2 (by norm_num)

theorem c22335R_55_0 : rowsJ2 55 56 0 300 ≤ 2456160989755308 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22335R_67 c22335R_55_1 (by norm_num)

theorem hr22335R_55 : rows2 55 56 ≤ 2456160989755308 := rows2_le_of_rowsJ2 55 56 c22335R_55_0

theorem c22335R_56_2 : rowsJ2 56 57 44 300 ≤ 847386884508494 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22335R_73 rows22335R_74 (by norm_num)

theorem c22335R_56_1 : rowsJ2 56 57 35 300 ≤ 1259208174045342 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22335R_72 c22335R_56_2 (by norm_num)

theorem c22335R_56_0 : rowsJ2 56 57 0 300 ≤ 2436613095813824 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22335R_71 c22335R_56_1 (by norm_num)

theorem hr22335R_56 : rows2 56 57 ≤ 2436613095813824 := rows2_le_of_rowsJ2 56 57 c22335R_56_0

theorem c22335R_57_2 : rowsJ2 57 58 44 300 ≤ 869877824393405 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22335R_77 rows22335R_78 (by norm_num)

theorem c22335R_57_1 : rowsJ2 57 58 35 300 ≤ 1300065355096584 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22335R_76 c22335R_57_2 (by norm_num)

theorem c22335R_57_0 : rowsJ2 57 58 0 300 ≤ 2414777818792172 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22335R_75 c22335R_57_1 (by norm_num)

theorem hr22335R_57 : rows2 57 58 ≤ 2414777818792172 := rows2_le_of_rowsJ2 57 58 c22335R_57_0

theorem c22335R_58_2 : rowsJ2 58 59 44 300 ≤ 885942518109374 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22335R_81 rows22335R_82 (by norm_num)

theorem c22335R_58_1 : rowsJ2 58 59 35 300 ≤ 1331662455422535 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22335R_80 c22335R_58_2 (by norm_num)

theorem c22335R_58_0 : rowsJ2 58 59 0 300 ≤ 2386183101303835 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22335R_79 c22335R_58_1 (by norm_num)

theorem hr22335R_58 : rows2 58 59 ≤ 2386183101303835 := rows2_le_of_rowsJ2 58 59 c22335R_58_0

theorem c22335R_59_2 : rowsJ2 59 60 44 300 ≤ 895691072746107 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22335R_85 rows22335R_86 (by norm_num)

theorem c22335R_59_1 : rowsJ2 59 60 35 300 ≤ 1358817589048331 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22335R_84 c22335R_59_2 (by norm_num)

theorem c22335R_59_0 : rowsJ2 59 60 0 300 ≤ 2355567068667866 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22335R_83 c22335R_59_1 (by norm_num)

theorem hr22335R_59 : rows2 59 60 ≤ 2355567068667866 := rows2_le_of_rowsJ2 59 60 c22335R_59_0

theorem c22335R_60_2 : rowsJ2 60 61 44 300 ≤ 899328788390663 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22335R_89 rows22335R_90 (by norm_num)

theorem c22335R_60_1 : rowsJ2 60 61 35 300 ≤ 1376485639801651 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22335R_88 c22335R_60_2 (by norm_num)

theorem c22335R_60_0 : rowsJ2 60 61 0 300 ≤ 2318397795351189 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22335R_87 c22335R_60_1 (by norm_num)

theorem hr22335R_60 : rows2 60 61 ≤ 2318397795351189 := rows2_le_of_rowsJ2 60 61 c22335R_60_0

theorem c22335R_61_2 : rowsJ2 61 62 45 300 ≤ 829287703435788 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22335R_93 rows22335R_94 (by norm_num)

theorem c22335R_61_1 : rowsJ2 61 62 35 300 ≤ 1389516827284405 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22335R_92 c22335R_61_2 (by norm_num)

theorem c22335R_61_0 : rowsJ2 61 62 0 300 ≤ 2279108650480000 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22335R_91 c22335R_61_1 (by norm_num)

theorem hr22335R_61 : rows2 61 62 ≤ 2279108650480000 := rows2_le_of_rowsJ2 61 62 c22335R_61_0

theorem c22335R_62_1 : rowsJ2 62 63 35 300 ≤ 1392767802770523 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22335R_96 rows22335R_97 (by norm_num)

theorem c22335R_62_0 : rowsJ2 62 63 0 300 ≤ 2233593881670769 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22335R_95 c22335R_62_1 (by norm_num)

theorem hr22335R_62 : rows2 62 63 ≤ 2233593881670769 := rows2_le_of_rowsJ2 62 63 c22335R_62_0

theorem c22335R_63_1 : rowsJ2 63 64 35 300 ≤ 1391274705053386 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22335R_99 rows22335R_100 (by norm_num)

theorem c22335R_63_0 : rowsJ2 63 64 0 300 ≤ 2186330470691421 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22335R_98 c22335R_63_1 (by norm_num)

theorem hr22335R_63 : rows2 63 64 ≤ 2186330470691421 := rows2_le_of_rowsJ2 63 64 c22335R_63_0

theorem c22335R_64_1 : rowsJ2 64 65 35 300 ≤ 1380026042201095 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22335R_102 rows22335R_103 (by norm_num)

theorem c22335R_64_0 : rowsJ2 64 65 0 300 ≤ 2133027810288622 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22335R_101 c22335R_64_1 (by norm_num)

theorem hr22335R_64 : rows2 64 65 ≤ 2133027810288622 := rows2_le_of_rowsJ2 64 65 c22335R_64_0

theorem c22335R_65_1 : rowsJ2 65 66 35 300 ≤ 1364095771553433 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22335R_105 rows22335R_106 (by norm_num)

theorem c22335R_65_0 : rowsJ2 65 66 0 300 ≤ 2078715762511082 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22335R_104 c22335R_65_1 (by norm_num)

theorem hr22335R_65 : rows2 65 66 ≤ 2078715762511082 := rows2_le_of_rowsJ2 65 66 c22335R_65_0

theorem c22335R_66_1 : rowsJ2 66 67 35 300 ≤ 1339082282969625 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22335R_108 rows22335R_109 (by norm_num)

theorem c22335R_66_0 : rowsJ2 66 67 0 300 ≤ 2019076146019287 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22335R_107 c22335R_66_1 (by norm_num)

theorem hr22335R_66 : rows2 66 67 ≤ 2019076146019287 := rows2_le_of_rowsJ2 66 67 c22335R_66_0

theorem c22335R_67_2 : rowsJ2 67 68 47 300 ≤ 613441862077435 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22335R_112 rows22335R_113 (by norm_num)

theorem c22335R_67_1 : rowsJ2 67 68 35 300 ≤ 1310157715476185 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22335R_111 c22335R_67_2 (by norm_num)

theorem c22335R_67_0 : rowsJ2 67 68 0 300 ≤ 1958871186911036 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22335R_110 c22335R_67_1 (by norm_num)

theorem hr22335R_67 : rows2 67 68 ≤ 1958871186911036 := rows2_le_of_rowsJ2 67 68 c22335R_67_0

theorem c22335R_68_2 : rowsJ2 68 69 48 300 ≤ 537880119829066 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22335R_116 rows22335R_117 (by norm_num)

theorem c22335R_68_1 : rowsJ2 68 69 35 300 ≤ 1272902951522219 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22335R_115 c22335R_68_2 (by norm_num)

theorem c22335R_68_0 : rowsJ2 68 69 0 300 ≤ 1894308517665536 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22335R_114 c22335R_68_1 (by norm_num)

theorem hr22335R_68 : rows2 68 69 ≤ 1894308517665536 := rows2_le_of_rowsJ2 68 69 c22335R_68_0

theorem c22335R_69_2 : rowsJ2 69 70 49 300 ≤ 465825025196613 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22335R_120 rows22335R_121 (by norm_num)

theorem c22335R_69_1 : rowsJ2 69 70 35 300 ≤ 1232721570052258 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22335R_119 c22335R_69_2 (by norm_num)

theorem c22335R_69_0 : rowsJ2 69 70 0 300 ≤ 1830229658635063 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22335R_118 c22335R_69_1 (by norm_num)

theorem hr22335R_69 : rows2 69 70 ≤ 1830229658635063 := rows2_le_of_rowsJ2 69 70 c22335R_69_0

theorem c22335R_70_2 : rowsJ2 70 71 50 300 ≤ 397807931763102 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22335R_124 rows22335R_125 (by norm_num)

theorem c22335R_70_1 : rowsJ2 70 71 35 300 ≤ 1185311120917419 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22335R_123 c22335R_70_2 (by norm_num)

theorem c22335R_70_0 : rowsJ2 70 71 0 300 ≤ 1762588756094780 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22335R_122 c22335R_70_1 (by norm_num)

theorem hr22335R_70 : rows2 70 71 ≤ 1762588756094780 := rows2_le_of_rowsJ2 70 71 c22335R_70_0

theorem c22335R_71_2 : rowsJ2 71 72 51 300 ≤ 334432520650590 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22335R_128 rows22335R_129 (by norm_num)

theorem c22335R_71_1 : rowsJ2 71 72 35 300 ≤ 1136212763837434 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22335R_127 c22335R_71_2 (by norm_num)

theorem c22335R_71_0 : rowsJ2 71 72 0 300 ≤ 1696918476313122 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22335R_126 c22335R_71_1 (by norm_num)

theorem hr22335R_71 : rows2 71 72 ≤ 1696918476313122 := rows2_le_of_rowsJ2 71 72 c22335R_71_0

theorem c22335R_72_2 : rowsJ2 72 73 54 300 ≤ 222053860687290 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22335R_132 rows22335R_133 (by norm_num)

theorem c22335R_72_1 : rowsJ2 72 73 35 300 ≤ 1082459000752853 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22335R_131 c22335R_72_2 (by norm_num)

theorem c22335R_72_0 : rowsJ2 72 73 0 300 ≤ 1630364194508334 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22335R_130 c22335R_72_1 (by norm_num)

theorem hr22335R_72 : rows2 72 73 ≤ 1630364194508334 := rows2_le_of_rowsJ2 72 73 c22335R_72_0

theorem c22335R_73_3 : rowsJ2 73 74 68 300 ≤ 28997167117218 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22335R_137 rows22335R_138 (by norm_num)

theorem c22335R_73_2 : rowsJ2 73 74 58 300 ≤ 122804083106286 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22335R_136 c22335R_73_3 (by norm_num)

theorem c22335R_73_1 : rowsJ2 73 74 35 300 ≤ 1031325529853785 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22335R_135 c22335R_73_2 (by norm_num)

theorem c22335R_73_0 : rowsJ2 73 74 0 300 ≤ 1569517328318809 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22335R_134 c22335R_73_1 (by norm_num)

theorem hr22335R_73 : rows2 73 74 ≤ 1569517328318809 := rows2_le_of_rowsJ2 73 74 c22335R_73_0

theorem c22335R_74_3 : rowsJ2 74 75 68 300 ≤ 34282550326034 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22335R_142 rows22335R_143 (by norm_num)

theorem c22335R_74_2 : rowsJ2 74 75 59 300 ≤ 99750530139329 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22335R_141 c22335R_74_3 (by norm_num)

theorem c22335R_74_1 : rowsJ2 74 75 35 300 ≤ 977406557106532 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22335R_140 c22335R_74_2 (by norm_num)

theorem c22335R_74_0 : rowsJ2 74 75 0 300 ≤ 1509579468662933 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22335R_139 c22335R_74_1 (by norm_num)

theorem hr22335R_74 : rows2 74 75 ≤ 1509579468662933 := rows2_le_of_rowsJ2 74 75 c22335R_74_0

theorem c22335R_75_3 : rowsJ2 75 76 68 300 ≤ 38384195841738 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22335R_147 rows22335R_148 (by norm_num)

theorem c22335R_75_2 : rowsJ2 75 76 60 300 ≤ 81069024208366 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22335R_146 c22335R_75_3 (by norm_num)

theorem c22335R_75_1 : rowsJ2 75 76 35 300 ≤ 923406014223047 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22335R_145 c22335R_75_2 (by norm_num)

theorem c22335R_75_0 : rowsJ2 75 76 0 300 ≤ 1452484170929742 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22335R_144 c22335R_75_1 (by norm_num)

theorem hr22335R_75 : rows2 75 76 ≤ 1452484170929742 := rows2_le_of_rowsJ2 75 76 c22335R_75_0

theorem c22335R_76_4 : rowsJ2 76 77 72 300 ≤ 27599141537148 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22335R_153 rows22335R_154 (by norm_num)

theorem c22335R_76_3 : rowsJ2 76 77 68 300 ≤ 40517788645277 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22335R_152 c22335R_76_4 (by norm_num)

theorem c22335R_76_2 : rowsJ2 76 77 61 300 ≤ 65853406109112 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22335R_151 c22335R_76_3 (by norm_num)

theorem c22335R_76_1 : rowsJ2 76 77 35 300 ≤ 868790716346237 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22335R_150 c22335R_76_2 (by norm_num)

theorem c22335R_76_0 : rowsJ2 76 77 0 300 ≤ 1392904941065375 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22335R_149 c22335R_76_1 (by norm_num)

theorem hr22335R_76 : rows2 76 77 ≤ 1392904941065375 := rows2_le_of_rowsJ2 76 77 c22335R_76_0

theorem c22335R_77_4 : rowsJ2 77 78 72 300 ≤ 28629415253007 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22335R_159 rows22335R_160 (by norm_num)

theorem c22335R_77_3 : rowsJ2 77 78 68 300 ≤ 41437269260788 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22335R_158 c22335R_77_4 (by norm_num)

theorem c22335R_77_2 : rowsJ2 77 78 61 300 ≤ 60096545678450 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22335R_157 c22335R_77_3 (by norm_num)

theorem c22335R_77_1 : rowsJ2 77 78 35 300 ≤ 814688260474579 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22335R_156 c22335R_77_2 (by norm_num)

theorem c22335R_77_0 : rowsJ2 77 78 0 300 ≤ 1336795455815113 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22335R_155 c22335R_77_1 (by norm_num)

theorem hr22335R_77 : rows2 77 78 ≤ 1336795455815113 := rows2_le_of_rowsJ2 77 78 c22335R_77_0

theorem c22335R_78_4 : rowsJ2 78 79 72 300 ≤ 27814336139526 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22335R_165 rows22335R_166 (by norm_num)

theorem c22335R_78_3 : rowsJ2 78 79 68 300 ≤ 40513598412293 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22335R_164 c22335R_78_4 (by norm_num)

theorem c22335R_78_2 : rowsJ2 78 79 61 300 ≤ 53738013819668 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22335R_163 c22335R_78_3 (by norm_num)

theorem c22335R_78_1 : rowsJ2 78 79 35 300 ≤ 760757172879396 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22335R_162 c22335R_78_2 (by norm_num)

theorem c22335R_78_0 : rowsJ2 78 79 0 300 ≤ 1278900982382537 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22335R_161 c22335R_78_1 (by norm_num)

theorem hr22335R_78 : rows2 78 79 ≤ 1278900982382537 := rows2_le_of_rowsJ2 78 79 c22335R_78_0

theorem c22335R_79_4 : rowsJ2 79 80 72 300 ≤ 26599683557571 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22335R_171 rows22335R_172 (by norm_num)

theorem c22335R_79_3 : rowsJ2 79 80 68 300 ≤ 39190511238306 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22335R_170 c22335R_79_4 (by norm_num)

theorem c22335R_79_2 : rowsJ2 79 80 61 300 ≤ 48309573309963 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22335R_169 c22335R_79_3 (by norm_num)

theorem c22335R_79_1 : rowsJ2 79 80 35 300 ≤ 708529757693641 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22335R_168 c22335R_79_2 (by norm_num)

theorem c22335R_79_0 : rowsJ2 79 80 0 300 ≤ 1225166096664948 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22335R_167 c22335R_79_1 (by norm_num)

theorem hr22335R_79 : rows2 79 80 ≤ 1225166096664948 := rows2_le_of_rowsJ2 79 80 c22335R_79_0

theorem c22335R_80_5 : rowsJ2 80 81 76 300 ≤ 12793089709840 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22335R_178 rows22335R_179 (by norm_num)

theorem c22335R_80_4 : rowsJ2 80 81 72 300 ≤ 25335680156710 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22335R_177 c22335R_80_5 (by norm_num)

theorem c22335R_80_3 : rowsJ2 80 81 68 300 ≤ 37214161826493 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22335R_176 c22335R_80_4 (by norm_num)

theorem c22335R_80_2 : rowsJ2 80 81 62 300 ≤ 41480969847919 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22335R_175 c22335R_80_3 (by norm_num)

theorem c22335R_80_1 : rowsJ2 80 81 36 300 ≤ 608939218863351 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22335R_174 c22335R_80_2 (by norm_num)

theorem c22335R_80_0 : rowsJ2 80 81 0 300 ≤ 1170893510991334 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22335R_173 c22335R_80_1 (by norm_num)

theorem hr22335R_80 : rows2 80 81 ≤ 1170893510991334 := rows2_le_of_rowsJ2 80 81 c22335R_80_0

theorem c22335R_81_5 : rowsJ2 81 82 76 300 ≤ 14325689091402 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22335R_185 rows22335R_186 (by norm_num)

theorem c22335R_81_4 : rowsJ2 81 82 72 300 ≤ 24717565171766 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22335R_184 c22335R_81_5 (by norm_num)

theorem c22335R_81_3 : rowsJ2 81 82 68 300 ≤ 35938021024922 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22335R_183 c22335R_81_4 (by norm_num)

theorem c22335R_81_2 : rowsJ2 81 82 62 300 ≤ 39246242741336 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22335R_182 c22335R_81_3 (by norm_num)

theorem c22335R_81_1 : rowsJ2 81 82 36 300 ≤ 562860574538032 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22335R_181 c22335R_81_2 (by norm_num)

theorem c22335R_81_0 : rowsJ2 81 82 0 300 ≤ 1121887371181639 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22335R_180 c22335R_81_1 (by norm_num)

theorem hr22335R_81 : rows2 81 82 ≤ 1121887371181639 := rows2_le_of_rowsJ2 81 82 c22335R_81_0

theorem c22335R_82_5 : rowsJ2 82 83 76 300 ≤ 16451179031015 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22335R_192 rows22335R_193 (by norm_num)

theorem c22335R_82_4 : rowsJ2 82 83 72 300 ≤ 24901504001783 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22335R_191 c22335R_82_5 (by norm_num)

theorem c22335R_82_3 : rowsJ2 82 83 68 300 ≤ 34988141728242 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22335R_190 c22335R_82_4 (by norm_num)

theorem c22335R_82_2 : rowsJ2 82 83 62 300 ≤ 37953884716271 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22335R_189 c22335R_82_3 (by norm_num)

theorem c22335R_82_1 : rowsJ2 82 83 37 300 ≤ 476861464252422 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22335R_188 c22335R_82_2 (by norm_num)

theorem c22335R_82_0 : rowsJ2 82 83 0 300 ≤ 1072824439496194 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22335R_187 c22335R_82_1 (by norm_num)

theorem hr22335R_82 : rows2 82 83 ≤ 1072824439496194 := rows2_le_of_rowsJ2 82 83 c22335R_82_0

theorem c22335R_83_5 : rowsJ2 83 84 75 300 ≤ 21499662574873 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22335R_199 rows22335R_200 (by norm_num)

theorem c22335R_83_4 : rowsJ2 83 84 71 300 ≤ 28977509754631 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22335R_198 c22335R_83_5 (by norm_num)

theorem c22335R_83_3 : rowsJ2 83 84 67 300 ≤ 37203229913840 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22335R_197 c22335R_83_4 (by norm_num)

theorem c22335R_83_2 : rowsJ2 83 84 62 300 ≤ 38811306979862 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22335R_196 c22335R_83_3 (by norm_num)

theorem c22335R_83_1 : rowsJ2 83 84 37 300 ≤ 439022354158093 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22335R_195 c22335R_83_2 (by norm_num)

theorem c22335R_83_0 : rowsJ2 83 84 0 300 ≤ 1030271082329479 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22335R_194 c22335R_83_1 (by norm_num)

theorem hr22335R_83 : rows2 83 84 ≤ 1030271082329479 := rows2_le_of_rowsJ2 83 84 c22335R_83_0

theorem c22335R_84_5 : rowsJ2 84 85 75 300 ≤ 26348288871157 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22335R_206 rows22335R_207 (by norm_num)

theorem c22335R_84_4 : rowsJ2 84 85 71 300 ≤ 32209634124176 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22335R_205 c22335R_84_5 (by norm_num)

theorem c22335R_84_3 : rowsJ2 84 85 67 300 ≤ 39475755058282 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22335R_204 c22335R_84_4 (by norm_num)

theorem c22335R_84_2 : rowsJ2 84 85 62 300 ≤ 41071630276237 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22335R_203 c22335R_84_3 (by norm_num)

theorem c22335R_84_1 : rowsJ2 84 85 38 300 ≤ 368521977076104 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22335R_202 c22335R_84_2 (by norm_num)

theorem c22335R_84_0 : rowsJ2 84 85 0 300 ≤ 988711789453790 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22335R_201 c22335R_84_1 (by norm_num)

theorem hr22335R_84 : rows2 84 85 ≤ 988711789453790 := rows2_le_of_rowsJ2 84 85 c22335R_84_0

theorem c22335R_85_5 : rowsJ2 85 86 75 300 ≤ 33986753163647 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22335R_213 rows22335R_214 (by norm_num)

theorem c22335R_85_4 : rowsJ2 85 86 71 300 ≤ 38430549571960 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22335R_212 c22335R_85_5 (by norm_num)

theorem c22335R_85_3 : rowsJ2 85 86 67 300 ≤ 44836232650618 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22335R_211 c22335R_85_4 (by norm_num)

theorem c22335R_85_2 : rowsJ2 85 86 62 300 ≤ 46420091911888 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22335R_210 c22335R_85_3 (by norm_num)

theorem c22335R_85_1 : rowsJ2 85 86 39 300 ≤ 309169992855156 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22335R_209 c22335R_85_2 (by norm_num)

theorem c22335R_85_0 : rowsJ2 85 86 0 300 ≤ 954347261225442 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22335R_208 c22335R_85_1 (by norm_num)

theorem hr22335R_85 : rows2 85 86 ≤ 954347261225442 := rows2_le_of_rowsJ2 85 86 c22335R_85_0

theorem c22335R_86_5 : rowsJ2 86 87 76 300 ≤ 43728113690090 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22335R_220 rows22335R_221 (by norm_num)

theorem c22335R_86_4 : rowsJ2 86 87 71 300 ≤ 47582273576754 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22335R_219 c22335R_86_5 (by norm_num)

theorem c22335R_86_3 : rowsJ2 86 87 67 300 ≤ 52845212946474 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22335R_218 c22335R_86_4 (by norm_num)

theorem c22335R_86_2 : rowsJ2 86 87 62 300 ≤ 54415245892053 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22335R_217 c22335R_86_3 (by norm_num)

theorem c22335R_86_1 : rowsJ2 86 87 40 300 ≤ 260338391563606 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22335R_216 c22335R_86_2 (by norm_num)

theorem c22335R_86_0 : rowsJ2 86 87 0 300 ≤ 922390376804211 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22335R_215 c22335R_86_1 (by norm_num)

theorem hr22335R_86 : rows2 86 87 ≤ 922390376804211 := rows2_le_of_rowsJ2 86 87 c22335R_86_0

theorem c22335R_87_6 : rowsJ2 87 88 81 300 ≤ 50056049186728 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22335R_228 rows22335R_229 (by norm_num)

theorem c22335R_87_5 : rowsJ2 87 88 76 300 ≤ 58091956052277 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22335R_227 c22335R_87_6 (by norm_num)

theorem c22335R_87_4 : rowsJ2 87 88 71 300 ≤ 60794223443811 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22335R_226 c22335R_87_5 (by norm_num)

theorem c22335R_87_3 : rowsJ2 87 88 67 300 ≤ 65057900106177 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22335R_225 c22335R_87_4 (by norm_num)

theorem c22335R_87_2 : rowsJ2 87 88 62 300 ≤ 66614384968962 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22335R_224 c22335R_87_3 (by norm_num)

theorem c22335R_87_1 : rowsJ2 87 88 43 300 ≤ 181258585471579 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22335R_223 c22335R_87_2 (by norm_num)

theorem c22335R_87_0 : rowsJ2 87 88 0 300 ≤ 898669640373675 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22335R_222 c22335R_87_1 (by norm_num)

theorem hr22335R_87 : rows2 87 88 ≤ 898669640373675 := rows2_le_of_rowsJ2 87 88 c22335R_87_0

theorem c22335R_88_5 : rowsJ2 88 89 76 300 ≤ 75876284217958 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22335R_235 rows22335R_236 (by norm_num)

theorem c22335R_88_4 : rowsJ2 88 89 71 300 ≤ 77607582043929 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22335R_234 c22335R_88_5 (by norm_num)

theorem c22335R_88_3 : rowsJ2 88 89 67 300 ≤ 80704146027846 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22335R_233 c22335R_88_4 (by norm_num)

theorem c22335R_88_2 : rowsJ2 88 89 62 300 ≤ 82247356298791 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22335R_232 c22335R_88_3 (by norm_num)

theorem c22335R_88_1 : rowsJ2 88 89 48 300 ≤ 113339876306511 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22335R_231 c22335R_88_2 (by norm_num)

theorem c22335R_88_0 : rowsJ2 88 89 0 300 ≤ 877597845409010 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22335R_230 c22335R_88_1 (by norm_num)

theorem hr22335R_88 : rows2 88 89 ≤ 877597845409010 := rows2_le_of_rowsJ2 88 89 c22335R_88_0

theorem c22335R_89_5 : rowsJ2 89 90 76 300 ≤ 262429896858547 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22335R_242 rows22335R_243 (by norm_num)

theorem c22335R_89_4 : rowsJ2 89 90 71 300 ≤ 263504682196127 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22335R_241 c22335R_89_5 (by norm_num)

theorem c22335R_89_3 : rowsJ2 89 90 67 300 ≤ 265621685706128 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22335R_240 c22335R_89_4 (by norm_num)

theorem c22335R_89_2 : rowsJ2 89 90 62 300 ≤ 267151912753379 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22335R_239 c22335R_89_3 (by norm_num)

theorem c22335R_89_1 : rowsJ2 89 90 51 300 ≤ 273354444287232 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22335R_238 c22335R_89_2 (by norm_num)

theorem c22335R_89_0 : rowsJ2 89 90 0 300 ≤ 1029954711352975 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22335R_237 c22335R_89_1 (by norm_num)

theorem hr22335R_89 : rows2 89 90 ≤ 1029954711352975 := rows2_le_of_rowsJ2 89 90 c22335R_89_0

theorem c22335R_90_5 : rowsJ2 90 91 75 300 ≤ 518319434355640 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22335R_249 rows22335R_250 (by norm_num)

theorem c22335R_90_4 : rowsJ2 90 91 70 300 ≤ 518844390711248 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22335R_248 c22335R_90_5 (by norm_num)

theorem c22335R_90_3 : rowsJ2 90 91 66 300 ≤ 520524637857289 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22335R_247 c22335R_90_4 (by norm_num)

theorem c22335R_90_2 : rowsJ2 90 91 61 300 ≤ 521231566386853 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22335R_246 c22335R_90_3 (by norm_num)

theorem c22335R_90_1 : rowsJ2 90 91 52 300 ≤ 522507669789218 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22335R_245 c22335R_90_2 (by norm_num)

theorem c22335R_90_0 : rowsJ2 90 91 0 300 ≤ 1250680524022632 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22335R_244 c22335R_90_1 (by norm_num)

theorem hr22335R_90 : rows2 90 91 ≤ 1250680524022632 := rows2_le_of_rowsJ2 90 91 c22335R_90_0

theorem c22335R_91_5 : rowsJ2 91 92 76 300 ≤ 645336957186186 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22335R_256 rows22335R_257 (by norm_num)

theorem c22335R_91_4 : rowsJ2 91 92 71 300 ≤ 645768749918907 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22335R_255 c22335R_91_5 (by norm_num)

theorem c22335R_91_3 : rowsJ2 91 92 66 300 ≤ 646852074921965 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22335R_254 c22335R_91_4 (by norm_num)

theorem c22335R_91_2 : rowsJ2 91 92 61 300 ≤ 647551979462284 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22335R_253 c22335R_91_3 (by norm_num)

theorem c22335R_91_1 : rowsJ2 91 92 53 300 ≤ 647551979462284 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22335R_252 c22335R_91_2 (by norm_num)

theorem c22335R_91_0 : rowsJ2 91 92 0 300 ≤ 1347170559714667 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22335R_251 c22335R_91_1 (by norm_num)

theorem hr22335R_91 : rows2 91 92 ≤ 1347170559714667 := rows2_le_of_rowsJ2 91 92 c22335R_91_0

theorem c22335R_92_5 : rowsJ2 92 93 76 300 ≤ 884438286163365 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22335R_263 rows22335R_264 (by norm_num)

theorem c22335R_92_4 : rowsJ2 92 93 71 300 ≤ 884806156134925 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22335R_262 c22335R_92_5 (by norm_num)

theorem c22335R_92_3 : rowsJ2 92 93 66 300 ≤ 885312410815749 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22335R_261 c22335R_92_4 (by norm_num)

theorem c22335R_92_2 : rowsJ2 92 93 61 300 ≤ 885830519604632 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22335R_260 c22335R_92_3 (by norm_num)

theorem c22335R_92_1 : rowsJ2 92 93 53 300 ≤ 885830519604632 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22335R_259 c22335R_92_2 (by norm_num)

theorem c22335R_92_0 : rowsJ2 92 93 0 300 ≤ 1554999363303850 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22335R_258 c22335R_92_1 (by norm_num)

theorem hr22335R_92 : rows2 92 93 ≤ 1554999363303850 := rows2_le_of_rowsJ2 92 93 c22335R_92_0

theorem c22335R_93_5 : rowsJ2 93 94 77 300 ≤ 996991761575983 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22335R_270 rows22335R_271 (by norm_num)

theorem c22335R_93_4 : rowsJ2 93 94 71 300 ≤ 998419290459663 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22335R_269 c22335R_93_5 (by norm_num)

theorem c22335R_93_3 : rowsJ2 93 94 66 300 ≤ 998579519446407 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22335R_268 c22335R_93_4 (by norm_num)

theorem c22335R_93_2 : rowsJ2 93 94 61 300 ≤ 998959933087835 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22335R_267 c22335R_93_3 (by norm_num)

theorem c22335R_93_1 : rowsJ2 93 94 53 300 ≤ 998959933087835 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22335R_266 c22335R_93_2 (by norm_num)

theorem c22335R_93_0 : rowsJ2 93 94 0 300 ≤ 1641161080243037 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22335R_265 c22335R_93_1 (by norm_num)

theorem hr22335R_93 : rows2 93 94 ≤ 1641161080243037 := rows2_le_of_rowsJ2 93 94 c22335R_93_0

theorem c22335R_94_5 : rowsJ2 94 95 77 300 ≤ 1220246773215443 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22335R_277 rows22335R_278 (by norm_num)

theorem c22335R_94_4 : rowsJ2 94 95 71 300 ≤ 1221780134234157 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22335R_276 c22335R_94_5 (by norm_num)

theorem c22335R_94_3 : rowsJ2 94 95 66 300 ≤ 1221802912151959 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22335R_275 c22335R_94_4 (by norm_num)

theorem c22335R_94_2 : rowsJ2 94 95 61 300 ≤ 1221982353057760 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22335R_274 c22335R_94_3 (by norm_num)

theorem c22335R_94_1 : rowsJ2 94 95 53 300 ≤ 1221982353057760 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22335R_273 c22335R_94_2 (by norm_num)

theorem c22335R_94_0 : rowsJ2 94 95 0 300 ≤ 1836188928321462 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22335R_272 c22335R_94_1 (by norm_num)

theorem hr22335R_94 : rows2 94 95 ≤ 1836188928321462 := rows2_le_of_rowsJ2 94 95 c22335R_94_0

theorem c22335R_95_5 : rowsJ2 95 96 77 300 ≤ 1320583949432200 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22335R_284 rows22335R_285 (by norm_num)

theorem c22335R_95_4 : rowsJ2 95 96 71 300 ≤ 1322299551909228 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22335R_283 c22335R_95_5 (by norm_num)

theorem c22335R_95_3 : rowsJ2 95 96 66 300 ≤ 1322299551909228 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22335R_282 c22335R_95_4 (by norm_num)

theorem c22335R_95_2 : rowsJ2 95 96 61 300 ≤ 1322366332120399 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22335R_281 c22335R_95_3 (by norm_num)

theorem c22335R_95_1 : rowsJ2 95 96 53 300 ≤ 1322366332120399 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22335R_280 c22335R_95_2 (by norm_num)

theorem c22335R_95_0 : rowsJ2 95 96 0 300 ≤ 1912317147751748 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22335R_279 c22335R_95_1 (by norm_num)

theorem hr22335R_95 : rows2 95 96 ≤ 1912317147751748 := rows2_le_of_rowsJ2 95 96 c22335R_95_0

theorem c22335R_96_5 : rowsJ2 96 97 76 300 ≤ 1260831787233941 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22335R_291 rows22335R_292 (by norm_num)

theorem c22335R_96_4 : rowsJ2 96 97 70 300 ≤ 1261386268928564 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22335R_290 c22335R_96_5 (by norm_num)

theorem c22335R_96_3 : rowsJ2 96 97 65 300 ≤ 1261386268928564 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22335R_289 c22335R_96_4 (by norm_num)

theorem c22335R_96_2 : rowsJ2 96 97 60 300 ≤ 1261386268928564 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22335R_288 c22335R_96_3 (by norm_num)

theorem c22335R_96_1 : rowsJ2 96 97 53 300 ≤ 1261386268928564 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22335R_287 c22335R_96_2 (by norm_num)

theorem c22335R_96_0 : rowsJ2 96 97 0 300 ≤ 1826283490698619 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22335R_286 c22335R_96_1 (by norm_num)

theorem hr22335R_96 : rows2 96 97 ≤ 1826283490698619 := rows2_le_of_rowsJ2 96 97 c22335R_96_0

theorem c22335R_97_5 : rowsJ2 97 98 76 300 ≤ 1130942720430543 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22335R_298 rows22335R_299 (by norm_num)

theorem c22335R_97_4 : rowsJ2 97 98 70 300 ≤ 1131586270072815 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22335R_297 c22335R_97_5 (by norm_num)

theorem c22335R_97_3 : rowsJ2 97 98 65 300 ≤ 1131586270072815 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22335R_296 c22335R_97_4 (by norm_num)

theorem c22335R_97_2 : rowsJ2 97 98 60 300 ≤ 1131586270072815 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22335R_295 c22335R_97_3 (by norm_num)

theorem c22335R_97_1 : rowsJ2 97 98 53 300 ≤ 1131586270072815 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22335R_294 c22335R_97_2 (by norm_num)

theorem c22335R_97_0 : rowsJ2 97 98 0 300 ≤ 1674580018799521 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22335R_293 c22335R_97_1 (by norm_num)

theorem hr22335R_97 : rows2 97 98 ≤ 1674580018799521 := rows2_le_of_rowsJ2 97 98 c22335R_97_0

theorem c22335R_98_5 : rowsJ2 98 99 76 300 ≤ 1114870321037736 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22335R_305 rows22335R_306 (by norm_num)

theorem c22335R_98_4 : rowsJ2 98 99 70 300 ≤ 1115529189517057 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22335R_304 c22335R_98_5 (by norm_num)

theorem c22335R_98_3 : rowsJ2 98 99 65 300 ≤ 1115529189517057 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22335R_303 c22335R_98_4 (by norm_num)

theorem c22335R_98_2 : rowsJ2 98 99 60 300 ≤ 1115529189517057 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22335R_302 c22335R_98_3 (by norm_num)

theorem c22335R_98_1 : rowsJ2 98 99 53 300 ≤ 1115911927355542 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22335R_301 c22335R_98_2 (by norm_num)

theorem c22335R_98_0 : rowsJ2 98 99 0 300 ≤ 1636285710674981 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22335R_300 c22335R_98_1 (by norm_num)

theorem hr22335R_98 : rows2 98 99 ≤ 1636285710674981 := rows2_le_of_rowsJ2 98 99 c22335R_98_0

theorem c22335R_99_4 : rowsJ2 99 100 71 300 ≤ 988978759804720 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22335R_311 rows22335R_312 (by norm_num)

theorem c22335R_99_3 : rowsJ2 99 100 65 300 ≤ 988978759804720 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22335R_310 c22335R_99_4 (by norm_num)

theorem c22335R_99_2 : rowsJ2 99 100 60 300 ≤ 988978759804720 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22335R_309 c22335R_99_3 (by norm_num)

theorem c22335R_99_1 : rowsJ2 99 100 53 300 ≤ 990178588770968 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22335R_308 c22335R_99_2 (by norm_num)

theorem c22335R_99_0 : rowsJ2 99 100 0 300 ≤ 1490686771290047 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22335R_307 c22335R_99_1 (by norm_num)

theorem hr22335R_99 : rows2 99 100 ≤ 1490686771290047 := rows2_le_of_rowsJ2 99 100 c22335R_99_0

theorem c22335R_100_4 : rowsJ2 100 101 71 300 ≤ 974158407854019 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22335R_317 rows22335R_318 (by norm_num)

theorem c22335R_100_3 : rowsJ2 100 101 65 300 ≤ 974158407854019 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22335R_316 c22335R_100_4 (by norm_num)

theorem c22335R_100_2 : rowsJ2 100 101 60 300 ≤ 974158407854019 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22335R_315 c22335R_100_3 (by norm_num)

theorem c22335R_100_1 : rowsJ2 100 101 53 300 ≤ 976786505313941 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22335R_314 c22335R_100_2 (by norm_num)

theorem c22335R_100_0 : rowsJ2 100 101 0 300 ≤ 1456059513012159 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22335R_313 c22335R_100_1 (by norm_num)

theorem hr22335R_100 : rows2 100 101 ≤ 1456059513012159 := rows2_le_of_rowsJ2 100 101 c22335R_100_0

theorem c22335R_101_4 : rowsJ2 101 102 70 300 ≤ 850697136305927 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22335R_323 rows22335R_324 (by norm_num)

theorem c22335R_101_3 : rowsJ2 101 102 64 300 ≤ 850697136305927 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22335R_322 c22335R_101_4 (by norm_num)

theorem c22335R_101_2 : rowsJ2 101 102 59 300 ≤ 850697136305927 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22335R_321 c22335R_101_3 (by norm_num)

theorem c22335R_101_1 : rowsJ2 101 102 53 300 ≤ 855340672251222 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22335R_320 c22335R_101_2 (by norm_num)

theorem c22335R_101_0 : rowsJ2 101 102 0 300 ≤ 1316257241425072 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22335R_319 c22335R_101_1 (by norm_num)

theorem hr22335R_101 : rows2 101 102 ≤ 1316257241425072 := rows2_le_of_rowsJ2 101 102 c22335R_101_0

theorem c22335R_102_4 : rowsJ2 102 103 70 300 ≤ 837144626961601 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22335R_329 rows22335R_330 (by norm_num)

theorem c22335R_102_3 : rowsJ2 102 103 64 300 ≤ 837144626961601 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22335R_328 c22335R_102_4 (by norm_num)

theorem c22335R_102_2 : rowsJ2 102 103 59 300 ≤ 837144626961601 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22335R_327 c22335R_102_3 (by norm_num)

theorem c22335R_102_1 : rowsJ2 102 103 53 300 ≤ 844658026183971 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22335R_326 c22335R_102_2 (by norm_num)

theorem c22335R_102_0 : rowsJ2 102 103 0 300 ≤ 1285858744022863 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22335R_325 c22335R_102_1 (by norm_num)

theorem hr22335R_102 : rows2 102 103 ≤ 1285858744022863 := rows2_le_of_rowsJ2 102 103 c22335R_102_0

theorem c22335R_103_4 : rowsJ2 103 104 70 300 ≤ 716711052510403 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22335R_335 rows22335R_336 (by norm_num)

theorem c22335R_103_3 : rowsJ2 103 104 64 300 ≤ 716711052510403 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22335R_334 c22335R_103_4 (by norm_num)

theorem c22335R_103_2 : rowsJ2 103 104 59 300 ≤ 716711052510403 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22335R_333 c22335R_103_3 (by norm_num)

theorem c22335R_103_1 : rowsJ2 103 104 52 300 ≤ 730487573508562 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22335R_332 c22335R_103_2 (by norm_num)

theorem c22335R_103_0 : rowsJ2 103 104 0 300 ≤ 1152102373804066 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22335R_331 c22335R_103_1 (by norm_num)

theorem hr22335R_103 : rows2 103 104 ≤ 1152102373804066 := rows2_le_of_rowsJ2 103 104 c22335R_103_0

theorem c22335R_104_4 : rowsJ2 104 105 69 300 ≤ 704474712517231 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22335R_341 rows22335R_342 (by norm_num)

theorem c22335R_104_3 : rowsJ2 104 105 63 300 ≤ 704474712517231 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22335R_340 c22335R_104_4 (by norm_num)

theorem c22335R_104_2 : rowsJ2 104 105 58 300 ≤ 706739091455975 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22335R_339 c22335R_104_3 (by norm_num)

theorem c22335R_104_1 : rowsJ2 104 105 52 300 ≤ 723431448521854 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22335R_338 c22335R_104_2 (by norm_num)

theorem c22335R_104_0 : rowsJ2 104 105 0 300 ≤ 1126507327213416 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22335R_337 c22335R_104_1 (by norm_num)

theorem hr22335R_104 : rows2 104 105 ≤ 1126507327213416 := rows2_le_of_rowsJ2 104 105 c22335R_104_0

theorem c22335R_105_4 : rowsJ2 105 106 69 300 ≤ 586926569398883 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22335R_347 rows22335R_348 (by norm_num)

theorem c22335R_105_3 : rowsJ2 105 106 63 300 ≤ 586926569398883 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22335R_346 c22335R_105_4 (by norm_num)

theorem c22335R_105_2 : rowsJ2 105 106 58 300 ≤ 591322509368177 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22335R_345 c22335R_105_3 (by norm_num)

theorem c22335R_105_1 : rowsJ2 105 106 52 300 ≤ 611697303700430 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22335R_344 c22335R_105_2 (by norm_num)

theorem c22335R_105_0 : rowsJ2 105 106 0 300 ≤ 998882538597154 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22335R_343 c22335R_105_1 (by norm_num)

theorem hr22335R_105 : rows2 105 106 ≤ 998882538597154 := rows2_le_of_rowsJ2 105 106 c22335R_105_0

theorem c22335R_106_3 : rowsJ2 106 107 64 300 ≤ 576073709355507 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22335R_352 rows22335R_353 (by norm_num)

theorem c22335R_106_2 : rowsJ2 106 107 58 300 ≤ 582964563787398 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22335R_351 c22335R_106_3 (by norm_num)

theorem c22335R_106_1 : rowsJ2 106 107 52 300 ≤ 607327864054124 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22335R_350 c22335R_106_2 (by norm_num)

theorem c22335R_106_0 : rowsJ2 106 107 0 300 ≤ 977493887551234 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22335R_349 c22335R_106_1 (by norm_num)

theorem hr22335R_106 : rows2 106 107 ≤ 977493887551234 := rows2_le_of_rowsJ2 106 107 c22335R_106_0

theorem c22335R_107_3 : rowsJ2 107 108 64 300 ≤ 461372274973843 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22335R_357 rows22335R_358 (by norm_num)

theorem c22335R_107_2 : rowsJ2 107 108 58 300 ≤ 470921910267248 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22335R_356 c22335R_107_3 (by norm_num)

theorem c22335R_107_1 : rowsJ2 107 108 52 300 ≤ 499325537092523 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22335R_355 c22335R_107_2 (by norm_num)

theorem c22335R_107_0 : rowsJ2 107 108 0 300 ≤ 855258825769634 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22335R_354 c22335R_107_1 (by norm_num)

theorem hr22335R_107 : rows2 107 108 ≤ 855258825769634 := rows2_le_of_rowsJ2 107 108 c22335R_107_0

theorem c22335R_108_3 : rowsJ2 108 109 63 300 ≤ 452470313330052 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22335R_362 rows22335R_363 (by norm_num)

theorem c22335R_108_2 : rowsJ2 108 109 57 300 ≤ 469299901296242 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22335R_361 c22335R_108_3 (by norm_num)

theorem c22335R_108_1 : rowsJ2 108 109 51 300 ≤ 501899184876089 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22335R_360 c22335R_108_2 (by norm_num)

theorem c22335R_108_0 : rowsJ2 108 109 0 300 ≤ 837437298939463 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22335R_359 c22335R_108_1 (by norm_num)

theorem hr22335R_108 : rows2 108 109 ≤ 837437298939463 := rows2_le_of_rowsJ2 108 109 c22335R_108_0

theorem c22335R_109_3 : rowsJ2 109 110 63 300 ≤ 341274634633878 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22335R_367 rows22335R_368 (by norm_num)

theorem c22335R_109_2 : rowsJ2 109 110 57 300 ≤ 360474071335774 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22335R_366 c22335R_109_3 (by norm_num)

theorem c22335R_109_1 : rowsJ2 109 110 51 300 ≤ 397203357933226 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22335R_365 c22335R_109_2 (by norm_num)

theorem c22335R_109_0 : rowsJ2 109 110 0 300 ≤ 719501037713627 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22335R_364 c22335R_109_1 (by norm_num)

theorem hr22335R_109 : rows2 109 110 ≤ 719501037713627 := rows2_le_of_rowsJ2 109 110 c22335R_109_0

theorem c22335R_110_3 : rowsJ2 110 111 63 300 ≤ 334508922221617 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22335R_372 rows22335R_373 (by norm_num)

theorem c22335R_110_2 : rowsJ2 110 111 57 300 ≤ 355804363864458 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22335R_371 c22335R_110_3 (by norm_num)

theorem c22335R_110_1 : rowsJ2 110 111 51 300 ≤ 396485552333928 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22335R_370 c22335R_110_2 (by norm_num)

theorem c22335R_110_0 : rowsJ2 110 111 0 300 ≤ 704683522004767 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22335R_369 c22335R_110_1 (by norm_num)

theorem hr22335R_110 : rows2 110 111 ≤ 704683522004767 := rows2_le_of_rowsJ2 110 111 c22335R_110_0

theorem c22335R_111_3 : rowsJ2 111 112 63 300 ≤ 227217764163075 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22335R_377 rows22335R_378 (by norm_num)

theorem c22335R_111_2 : rowsJ2 111 112 57 300 ≤ 250082925438208 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22335R_376 c22335R_111_3 (by norm_num)

theorem c22335R_111_1 : rowsJ2 111 112 51 300 ≤ 294679844921250 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22335R_375 c22335R_111_2 (by norm_num)

theorem c22335R_111_0 : rowsJ2 111 112 0 300 ≤ 591309576650197 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22335R_374 c22335R_111_1 (by norm_num)

theorem hr22335R_111 : rows2 111 112 ≤ 591309576650197 := rows2_le_of_rowsJ2 111 112 c22335R_111_0

theorem c22335R_112_3 : rowsJ2 112 113 62 300 ≤ 226318025039397 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22335R_382 rows22335R_383 (by norm_num)

theorem c22335R_112_2 : rowsJ2 112 113 56 300 ≤ 255384096419228 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22335R_381 c22335R_112_3 (by norm_num)

theorem c22335R_112_1 : rowsJ2 112 113 50 300 ≤ 303357620827684 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22335R_380 c22335R_112_2 (by norm_num)

theorem c22335R_112_0 : rowsJ2 112 113 0 300 ≤ 580609084113199 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22335R_379 c22335R_112_1 (by norm_num)

theorem hr22335R_112 : rows2 112 113 ≤ 580609084113199 := rows2_le_of_rowsJ2 112 113 c22335R_112_0

theorem c22335R_113_3 : rowsJ2 113 114 63 300 ≤ 116989543257392 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22335R_387 rows22335R_388 (by norm_num)

theorem c22335R_113_2 : rowsJ2 113 114 56 300 ≤ 149203280035552 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22335R_386 c22335R_113_3 (by norm_num)

theorem c22335R_113_1 : rowsJ2 113 114 50 300 ≤ 201065656016532 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22335R_385 c22335R_113_2 (by norm_num)

theorem c22335R_113_0 : rowsJ2 113 114 0 300 ≤ 467957709801957 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22335R_384 c22335R_113_1 (by norm_num)

theorem hr22335R_113 : rows2 113 114 ≤ 467957709801957 := rows2_le_of_rowsJ2 113 114 c22335R_113_0

theorem c22335R_114_3 : rowsJ2 114 115 63 300 ≤ 114498118907875 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22335R_392 rows22335R_393 (by norm_num)

theorem c22335R_114_2 : rowsJ2 114 115 56 300 ≤ 147351371441342 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22335R_391 c22335R_114_3 (by norm_num)

theorem c22335R_114_1 : rowsJ2 114 115 50 300 ≤ 202551196457224 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22335R_390 c22335R_114_2 (by norm_num)

theorem c22335R_114_0 : rowsJ2 114 115 0 300 ≤ 458243689022790 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22335R_389 c22335R_114_1 (by norm_num)

theorem hr22335R_114 : rows2 114 115 ≤ 458243689022790 := rows2_le_of_rowsJ2 114 115 c22335R_114_0

theorem c22335R_115_3 : rowsJ2 115 116 62 300 ≤ 9960837088658 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22335R_397 rows22335R_398 (by norm_num)

theorem c22335R_115_2 : rowsJ2 115 116 55 300 ≤ 48884230222223 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22335R_396 c22335R_115_3 (by norm_num)

theorem c22335R_115_1 : rowsJ2 115 116 49 300 ≤ 107090127230811 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22335R_395 c22335R_115_2 (by norm_num)

theorem c22335R_115_0 : rowsJ2 115 116 0 300 ≤ 345858245640678 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22335R_394 c22335R_115_1 (by norm_num)

theorem hr22335R_115 : rows2 115 116 ≤ 345858245640678 := rows2_le_of_rowsJ2 115 116 c22335R_115_0

theorem c22335R_116_3 : rowsJ2 116 117 62 300 ≤ 7868683831466 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22335R_402 rows22335R_403 (by norm_num)

theorem c22335R_116_2 : rowsJ2 116 117 55 300 ≤ 46564998137232 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22335R_401 c22335R_116_3 (by norm_num)

theorem c22335R_116_1 : rowsJ2 116 117 49 300 ≤ 107961341178121 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22335R_400 c22335R_116_2 (by norm_num)

theorem c22335R_116_0 : rowsJ2 116 117 0 300 ≤ 336839108299749 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22335R_399 c22335R_116_1 (by norm_num)

theorem hr22335R_116 : rows2 116 117 ≤ 336839108299749 := rows2_le_of_rowsJ2 116 117 c22335R_116_0

theorem c22335R_117_3 : rowsJ2 117 118 62 300 ≤ 7009518253105 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22335R_407 rows22335R_408 (by norm_num)

theorem c22335R_117_2 : rowsJ2 117 118 55 300 ≤ 44881505057291 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22335R_406 c22335R_117_3 (by norm_num)

theorem c22335R_117_1 : rowsJ2 117 118 49 300 ≤ 109349499428639 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22335R_405 c22335R_117_2 (by norm_num)

theorem c22335R_117_0 : rowsJ2 117 118 0 300 ≤ 330720167841113 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22335R_404 c22335R_117_1 (by norm_num)

theorem hr22335R_117 : rows2 117 118 ≤ 330720167841113 := rows2_le_of_rowsJ2 117 118 c22335R_117_0

theorem c22335R_118_2 : rowsJ2 118 119 56 300 ≤ 136099881383177 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22335R_411 rows22335R_412 (by norm_num)

theorem c22335R_118_1 : rowsJ2 118 119 49 300 ≤ 210889529276969 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22335R_410 c22335R_118_2 (by norm_num)

theorem c22335R_118_0 : rowsJ2 118 119 0 300 ≤ 424253168643314 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22335R_409 c22335R_118_1 (by norm_num)

theorem hr22335R_118 : rows2 118 119 ≤ 424253168643314 := rows2_le_of_rowsJ2 118 119 c22335R_118_0

theorem c22335R_119_2 : rowsJ2 119 120 55 300 ≤ 341524100409939 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22335R_415 rows22335R_416 (by norm_num)

theorem c22335R_119_1 : rowsJ2 119 120 48 300 ≤ 420333575927739 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22335R_414 c22335R_119_2 (by norm_num)

theorem c22335R_119_0 : rowsJ2 119 120 0 300 ≤ 617975116488650 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22335R_413 c22335R_119_1 (by norm_num)

theorem hr22335R_119 : rows2 119 120 ≤ 617975116488650 := rows2_le_of_rowsJ2 119 120 c22335R_119_0

theorem c22335R_120_2 : rowsJ2 120 121 55 300 ≤ 534662412817042 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22335R_419 rows22335R_420 (by norm_num)

theorem c22335R_120_1 : rowsJ2 120 121 48 300 ≤ 615079972520562 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22335R_418 c22335R_120_2 (by norm_num)

theorem c22335R_120_0 : rowsJ2 120 121 0 300 ≤ 805982633863002 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22335R_417 c22335R_120_1 (by norm_num)

theorem hr22335R_120 : rows2 120 121 ≤ 805982633863002 := rows2_le_of_rowsJ2 120 121 c22335R_120_0

theorem c22335R_121_2 : rowsJ2 121 122 55 300 ≤ 723266852189917 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22335R_423 rows22335R_424 (by norm_num)

theorem c22335R_121_1 : rowsJ2 121 122 48 300 ≤ 804995633483179 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22335R_422 c22335R_121_2 (by norm_num)

theorem c22335R_121_0 : rowsJ2 121 122 0 300 ≤ 991537244215171 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22335R_421 c22335R_121_1 (by norm_num)

theorem hr22335R_121 : rows2 121 122 ≤ 991537244215171 := rows2_le_of_rowsJ2 121 122 c22335R_121_0

theorem c22335R_122_2 : rowsJ2 122 123 54 300 ≤ 916318325434835 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22335R_427 rows22335R_428 (by norm_num)

theorem c22335R_122_1 : rowsJ2 122 123 47 300 ≤ 1001439556769440 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22335R_426 c22335R_122_2 (by norm_num)

theorem c22335R_122_0 : rowsJ2 122 123 0 300 ≤ 1171980610659398 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22335R_425 c22335R_122_1 (by norm_num)

theorem hr22335R_122 : rows2 122 123 ≤ 1171980610659398 := rows2_le_of_rowsJ2 122 123 c22335R_122_0

theorem c22335R_123_2 : rowsJ2 123 124 54 300 ≤ 1096703849217477 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22335R_431 rows22335R_432 (by norm_num)

theorem c22335R_123_1 : rowsJ2 123 124 47 300 ≤ 1182766072836067 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22335R_430 c22335R_123_2 (by norm_num)

theorem c22335R_123_0 : rowsJ2 123 124 0 300 ≤ 1350164054849930 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22335R_429 c22335R_123_1 (by norm_num)

theorem hr22335R_123 : rows2 123 124 ≤ 1350164054849930 := rows2_le_of_rowsJ2 123 124 c22335R_123_0

theorem c22335R_124_2 : rowsJ2 124 125 54 300 ≤ 1273808712562409 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22335R_435 rows22335R_436 (by norm_num)

theorem c22335R_124_1 : rowsJ2 124 125 47 300 ≤ 1359326194878633 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22335R_434 c22335R_124_2 (by norm_num)

theorem c22335R_124_0 : rowsJ2 124 125 0 300 ≤ 1523489991433646 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22335R_433 c22335R_124_1 (by norm_num)

theorem hr22335R_124 : rows2 124 125 ≤ 1523489991433646 := rows2_le_of_rowsJ2 124 125 c22335R_124_0

theorem c22335R_125_2 : rowsJ2 125 126 53 300 ≤ 1455006448128721 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22335R_439 rows22335R_440 (by norm_num)

theorem c22335R_125_1 : rowsJ2 125 126 46 300 ≤ 1544659432682296 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22335R_438 c22335R_125_2 (by norm_num)

theorem c22335R_125_0 : rowsJ2 125 126 0 300 ≤ 1695070432803917 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22335R_437 c22335R_125_1 (by norm_num)

theorem hr22335R_125 : rows2 125 126 ≤ 1695070432803917 := rows2_le_of_rowsJ2 125 126 c22335R_125_0

theorem c22335R_126_1 : rowsJ2 126 127 46 300 ≤ 1713489825552793 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22335R_442 rows22335R_443 (by norm_num)

theorem c22335R_126_0 : rowsJ2 126 127 0 300 ≤ 1862029941875420 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22335R_441 c22335R_126_1 (by norm_num)

theorem hr22335R_126 : rows2 126 127 ≤ 1862029941875420 := rows2_le_of_rowsJ2 126 127 c22335R_126_0

theorem c22335R_127_1 : rowsJ2 127 128 46 300 ≤ 1869560169130038 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22335R_445 rows22335R_446 (by norm_num)

theorem c22335R_127_0 : rowsJ2 127 128 0 300 ≤ 2018395730887405 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22335R_444 c22335R_127_1 (by norm_num)

theorem hr22335R_127 : rows2 127 128 ≤ 2018395730887405 := rows2_le_of_rowsJ2 127 128 c22335R_127_0

theorem c22335R_128_1 : rowsJ2 128 129 45 300 ≤ 2036863831536392 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22335R_448 rows22335R_449 (by norm_num)

theorem c22335R_128_0 : rowsJ2 128 129 0 300 ≤ 2171968263872857 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22335R_447 c22335R_128_1 (by norm_num)

theorem hr22335R_128 : rows2 128 129 ≤ 2171968263872857 := rows2_le_of_rowsJ2 128 129 c22335R_128_0

theorem c22335R_129_1 : rowsJ2 129 130 45 300 ≤ 2179252750420579 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22335R_451 rows22335R_452 (by norm_num)

theorem c22335R_129_0 : rowsJ2 129 130 0 300 ≤ 2315944867636361 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22335R_450 c22335R_129_1 (by norm_num)

theorem hr22335R_129 : rows2 129 130 ≤ 2315944867636361 := rows2_le_of_rowsJ2 129 130 c22335R_129_0

theorem c22335R_130_1 : rowsJ2 130 131 45 300 ≤ 2327900673918598 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22335R_454 rows22335R_455 (by norm_num)

theorem c22335R_130_0 : rowsJ2 130 131 0 300 ≤ 2466530292610032 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22335R_453 c22335R_130_1 (by norm_num)

theorem hr22335R_130 : rows2 130 131 ≤ 2466530292610032 := rows2_le_of_rowsJ2 130 131 c22335R_130_0

theorem c22335R_131_1 : rowsJ2 131 132 44 300 ≤ 2490335233161277 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22335R_457 rows22335R_458 (by norm_num)

theorem c22335R_131_0 : rowsJ2 131 132 0 300 ≤ 2617009453166736 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22335R_456 c22335R_131_1 (by norm_num)

theorem hr22335R_131 : rows2 131 132 ≤ 2617009453166736 := rows2_le_of_rowsJ2 131 132 c22335R_131_0

theorem c22335R_132_1 : rowsJ2 132 133 44 300 ≤ 2625386990392755 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22335R_460 rows22335R_461 (by norm_num)

theorem c22335R_132_0 : rowsJ2 132 133 0 300 ≤ 2755388927378221 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22335R_459 c22335R_132_1 (by norm_num)

theorem hr22335R_132 : rows2 132 133 ≤ 2755388927378221 := rows2_le_of_rowsJ2 132 133 c22335R_132_0

theorem c22335R_133_1 : rowsJ2 133 134 44 300 ≤ 2767593802304473 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22335R_463 rows22335R_464 (by norm_num)

theorem c22335R_133_0 : rowsJ2 133 134 0 300 ≤ 2902877570455121 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22335R_462 c22335R_133_1 (by norm_num)

theorem hr22335R_133 : rows2 133 134 ≤ 2902877570455121 := rows2_le_of_rowsJ2 133 134 c22335R_133_0

theorem c22335R_134_1 : rowsJ2 134 135 43 300 ≤ 2924392720864405 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22335R_466 rows22335R_467 (by norm_num)

theorem c22335R_134_0 : rowsJ2 134 135 0 300 ≤ 3047813585238123 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22335R_465 c22335R_134_1 (by norm_num)

theorem hr22335R_134 : rows2 134 135 ≤ 3047813585238123 := rows2_le_of_rowsJ2 134 135 c22335R_134_0

theorem c22335R_135_1 : rowsJ2 135 136 43 300 ≤ 2906278787344060 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22335R_469 rows22335R_470 (by norm_num)

theorem c22335R_135_0 : rowsJ2 135 136 0 300 ≤ 3036255128696008 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22335R_468 c22335R_135_1 (by norm_num)

theorem hr22335R_135 : rows2 135 136 ≤ 3036255128696008 := rows2_le_of_rowsJ2 135 136 c22335R_135_0

theorem c22335R_136_1 : rowsJ2 136 137 43 300 ≤ 2896534440204203 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22335R_472 rows22335R_473 (by norm_num)

theorem c22335R_136_0 : rowsJ2 136 137 0 300 ≤ 3033886610783152 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22335R_471 c22335R_136_1 (by norm_num)

theorem hr22335R_136 : rows2 136 137 ≤ 3033886610783152 := rows2_le_of_rowsJ2 136 137 c22335R_136_0

theorem c22335R_137_1 : rowsJ2 137 138 42 300 ≤ 2907110528541719 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22335R_475 rows22335R_476 (by norm_num)

theorem c22335R_137_0 : rowsJ2 137 138 0 300 ≤ 3033699862494171 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22335R_474 c22335R_137_1 (by norm_num)

theorem hr22335R_137 : rows2 137 138 ≤ 3033699862494171 := rows2_le_of_rowsJ2 137 138 c22335R_137_0

theorem c22335R_138_1 : rowsJ2 138 139 42 300 ≤ 2888768566562655 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22335R_478 rows22335R_479 (by norm_num)

theorem c22335R_138_0 : rowsJ2 138 139 0 300 ≤ 3024116978294639 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22335R_477 c22335R_138_1 (by norm_num)

theorem hr22335R_138 : rows2 138 139 ≤ 3024116978294639 := rows2_le_of_rowsJ2 138 139 c22335R_138_0

theorem c22335R_139_0 : rowsJ2 139 140 0 300 ≤ 3025693921450182 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22335R_480 rows22335R_481 (by norm_num)

theorem hr22335R_139 : rows2 139 140 ≤ 3025693921450182 := rows2_le_of_rowsJ2 139 140 c22335R_139_0

theorem c22335R_140_0 : rowsJ2 140 141 0 300 ≤ 3027304011687528 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22335R_482 rows22335R_483 (by norm_num)

theorem hr22335R_140 : rows2 140 141 ≤ 3027304011687528 := rows2_le_of_rowsJ2 140 141 c22335R_140_0

theorem c22335R_141_0 : rowsJ2 141 142 0 300 ≤ 3021375450031396 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22335R_484 rows22335R_485 (by norm_num)

theorem hr22335R_141 : rows2 141 142 ≤ 3021375450031396 := rows2_le_of_rowsJ2 141 142 c22335R_141_0

theorem c22335R_142_0 : rowsJ2 142 143 0 300 ≤ 3026431313565397 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22335R_486 rows22335R_487 (by norm_num)

theorem hr22335R_142 : rows2 142 143 ≤ 3026431313565397 := rows2_le_of_rowsJ2 142 143 c22335R_142_0

theorem c22335R_143_0 : rowsJ2 143 144 0 300 ≤ 3035013257019848 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22335R_488 rows22335R_489 (by norm_num)

theorem hr22335R_143 : rows2 143 144 ≤ 3035013257019848 := rows2_le_of_rowsJ2 143 144 c22335R_143_0

theorem c22335R_144_0 : rowsJ2 144 145 0 300 ≤ 3036146781681232 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22335R_490 rows22335R_491 (by norm_num)

theorem hr22335R_144 : rows2 144 145 ≤ 3036146781681232 := rows2_le_of_rowsJ2 144 145 c22335R_144_0

theorem c22335R_145_0 : rowsJ2 145 146 0 300 ≤ 3049590258385181 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22335R_492 rows22335R_493 (by norm_num)

theorem hr22335R_145 : rows2 145 146 ≤ 3049590258385181 := rows2_le_of_rowsJ2 145 146 c22335R_145_0

theorem c22335R_146_0 : rowsJ2 146 147 0 300 ≤ 3064406632745870 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22335R_494 rows22335R_495 (by norm_num)

theorem hr22335R_146 : rows2 146 147 ≤ 3064406632745870 := rows2_le_of_rowsJ2 146 147 c22335R_146_0

theorem c22335R_147_0 : rowsJ2 147 148 0 300 ≤ 3072873397751998 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22335R_496 rows22335R_497 (by norm_num)

theorem hr22335R_147 : rows2 147 148 ≤ 3072873397751998 := rows2_le_of_rowsJ2 147 148 c22335R_147_0

theorem c22335R_148_0 : rowsJ2 148 149 0 300 ≤ 3091647224775119 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22335R_498 rows22335R_499 (by norm_num)

theorem hr22335R_148 : rows2 148 149 ≤ 3091647224775119 := rows2_le_of_rowsJ2 148 149 c22335R_148_0

theorem c22335R_149_0 : rowsJ2 149 150 0 300 ≤ 3113064149957428 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22335R_500 rows22335R_501 (by norm_num)

theorem hr22335R_149 : rows2 149 150 ≤ 3113064149957428 := rows2_le_of_rowsJ2 149 150 c22335R_149_0

theorem c22335R_150_0 : rowsJ2 150 151 0 300 ≤ 3126424200121464 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22335R_502 rows22335R_503 (by norm_num)

theorem hr22335R_150 : rows2 150 151 ≤ 3126424200121464 := rows2_le_of_rowsJ2 150 151 c22335R_150_0

theorem c22335R_151_0 : rowsJ2 151 152 0 300 ≤ 3141273129408497 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22335R_504 rows22335R_505 (by norm_num)

theorem hr22335R_151 : rows2 151 152 ≤ 3141273129408497 := rows2_le_of_rowsJ2 151 152 c22335R_151_0

theorem c22335R_152_0 : rowsJ2 152 153 0 300 ≤ 3155589729807194 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22335R_506 rows22335R_507 (by norm_num)

theorem hr22335R_152 : rows2 152 153 ≤ 3155589729807194 := rows2_le_of_rowsJ2 152 153 c22335R_152_0

theorem c22335R_153_0 : rowsJ2 153 154 0 300 ≤ 3172213967013077 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22335R_508 rows22335R_509 (by norm_num)

theorem hr22335R_153 : rows2 153 154 ≤ 3172213967013077 := rows2_le_of_rowsJ2 153 154 c22335R_153_0

theorem t22335R_168 : rows2 293 300 ≤ 97875234515503460 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_547 rows22335R_548 (by norm_num)

theorem t22335R_167 : rows2 289 300 ≤ 148472304022686095 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_546 t22335R_168 (by norm_num)

theorem t22335R_166 : rows2 284 300 ≤ 207063745540186428 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_545 t22335R_167 (by norm_num)

theorem t22335R_165 : rows2 234 300 ≤ 249287986305253499 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_544 t22335R_166 (by norm_num)

theorem t22335R_164 : rows2 230 300 ≤ 291151641803095399 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_543 t22335R_165 (by norm_num)

theorem t22335R_163 : rows2 227 300 ≤ 322220946386036148 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_542 t22335R_164 (by norm_num)

theorem t22335R_162 : rows2 224 300 ≤ 353166880004040756 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_541 t22335R_163 (by norm_num)

theorem t22335R_161 : rows2 221 300 ≤ 383746005937818446 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_540 t22335R_162 (by norm_num)

theorem t22335R_160 : rows2 218 300 ≤ 414176358456569410 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_539 t22335R_161 (by norm_num)

theorem t22335R_159 : rows2 215 300 ≤ 444255295665895896 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_538 t22335R_160 (by norm_num)

theorem t22335R_158 : rows2 212 300 ≤ 474214757984405566 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_537 t22335R_159 (by norm_num)

theorem t22335R_157 : rows2 209 300 ≤ 503845425620273984 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_536 t22335R_158 (by norm_num)

theorem t22335R_156 : rows2 206 300 ≤ 533329681629062686 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_535 t22335R_157 (by norm_num)

theorem t22335R_155 : rows2 203 300 ≤ 562002068141849808 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_534 t22335R_156 (by norm_num)

theorem t22335R_154 : rows2 200 300 ≤ 589389145410846858 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_533 t22335R_155 (by norm_num)

theorem t22335R_153 : rows2 197 300 ≤ 615643015689264312 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_532 t22335R_154 (by norm_num)

theorem t22335R_152 : rows2 194 300 ≤ 640784003828725601 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_531 t22335R_153 (by norm_num)

theorem t22335R_151 : rows2 191 300 ≤ 664990117246229490 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_530 t22335R_152 (by norm_num)

theorem t22335R_150 : rows2 188 300 ≤ 688309449820436812 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_529 t22335R_151 (by norm_num)

theorem t22335R_149 : rows2 184 300 ≤ 718275268161375608 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_528 t22335R_150 (by norm_num)

theorem t22335R_148 : rows2 180 300 ≤ 746094046103945791 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_527 t22335R_149 (by norm_num)

theorem t22335R_147 : rows2 177 300 ≤ 765317449803883608 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_526 t22335R_148 (by norm_num)

theorem t22335R_146 : rows2 174 300 ≤ 783178782051871782 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_525 t22335R_147 (by norm_num)

theorem t22335R_145 : rows2 171 300 ≤ 799711640450910181 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_524 t22335R_146 (by norm_num)

theorem t22335R_144 : rows2 169 300 ≤ 810000639516951892 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_523 t22335R_145 (by norm_num)

theorem t22335R_143 : rows2 167 300 ≤ 819703874164821427 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_522 t22335R_144 (by norm_num)

theorem t22335R_142 : rows2 165 300 ≤ 828823054547782653 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_521 t22335R_143 (by norm_num)

theorem t22335R_141 : rows2 164 300 ≤ 833164468466376511 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_520 t22335R_142 (by norm_num)

theorem t22335R_140 : rows2 163 300 ≤ 837360932584985113 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_519 t22335R_141 (by norm_num)

theorem t22335R_139 : rows2 162 300 ≤ 841412955395908403 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_518 t22335R_140 (by norm_num)

theorem t22335R_138 : rows2 161 300 ≤ 845320870948522734 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_517 t22335R_139 (by norm_num)

theorem t22335R_137 : rows2 160 300 ≤ 849085020661890408 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_516 t22335R_138 (by norm_num)

theorem t22335R_136 : rows2 159 300 ≤ 852703499278450673 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_515 t22335R_137 (by norm_num)

theorem t22335R_135 : rows2 158 300 ≤ 856171293606655043 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_514 t22335R_136 (by norm_num)

theorem t22335R_134 : rows2 157 300 ≤ 859486177884560390 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_513 t22335R_135 (by norm_num)

theorem t22335R_133 : rows2 156 300 ≤ 862712369236644791 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_512 t22335R_134 (by norm_num)

theorem t22335R_132 : rows2 155 300 ≤ 865920099684071246 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_511 t22335R_133 (by norm_num)

theorem t22335R_131 : rows2 154 300 ≤ 869108905401660636 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_510 t22335R_132 (by norm_num)

theorem t22335R_130 : rows2 153 300 ≤ 872281119368673713 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_153 t22335R_131 (by norm_num)

theorem t22335R_129 : rows2 152 300 ≤ 875436709098480907 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_152 t22335R_130 (by norm_num)

theorem t22335R_128 : rows2 151 300 ≤ 878577982227889404 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_151 t22335R_129 (by norm_num)

theorem t22335R_127 : rows2 150 300 ≤ 881704406428010868 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_150 t22335R_128 (by norm_num)

theorem t22335R_126 : rows2 149 300 ≤ 884817470577968296 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_149 t22335R_127 (by norm_num)

theorem t22335R_125 : rows2 148 300 ≤ 887909117802743415 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_148 t22335R_126 (by norm_num)

theorem t22335R_124 : rows2 147 300 ≤ 890981991200495413 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_147 t22335R_125 (by norm_num)

theorem t22335R_123 : rows2 146 300 ≤ 894046397833241283 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_146 t22335R_124 (by norm_num)

theorem t22335R_122 : rows2 145 300 ≤ 897095988091626464 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_145 t22335R_123 (by norm_num)

theorem t22335R_121 : rows2 144 300 ≤ 900132134873307696 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_144 t22335R_122 (by norm_num)

theorem t22335R_120 : rows2 143 300 ≤ 903167148130327544 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_143 t22335R_121 (by norm_num)

theorem t22335R_119 : rows2 142 300 ≤ 906193579443892941 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_142 t22335R_120 (by norm_num)

theorem t22335R_118 : rows2 141 300 ≤ 909214954893924337 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_141 t22335R_119 (by norm_num)

theorem t22335R_117 : rows2 140 300 ≤ 912242258905611865 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_140 t22335R_118 (by norm_num)

theorem t22335R_116 : rows2 139 300 ≤ 915267952827062047 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_139 t22335R_117 (by norm_num)

theorem t22335R_115 : rows2 138 300 ≤ 918292069805356686 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_138 t22335R_116 (by norm_num)

theorem t22335R_114 : rows2 137 300 ≤ 921325769667850857 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_137 t22335R_115 (by norm_num)

theorem t22335R_113 : rows2 136 300 ≤ 924359656278634009 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_136 t22335R_114 (by norm_num)

theorem t22335R_112 : rows2 135 300 ≤ 927395911407330017 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_135 t22335R_113 (by norm_num)

theorem t22335R_111 : rows2 134 300 ≤ 930443724992568140 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_134 t22335R_112 (by norm_num)

theorem t22335R_110 : rows2 133 300 ≤ 933346602563023261 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_133 t22335R_111 (by norm_num)

theorem t22335R_109 : rows2 132 300 ≤ 936101991490401482 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_132 t22335R_110 (by norm_num)

theorem t22335R_108 : rows2 131 300 ≤ 938719000943568218 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_131 t22335R_109 (by norm_num)

theorem t22335R_107 : rows2 130 300 ≤ 941185531236178250 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_130 t22335R_108 (by norm_num)

theorem t22335R_106 : rows2 129 300 ≤ 943501476103814611 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_129 t22335R_107 (by norm_num)

theorem t22335R_105 : rows2 128 300 ≤ 945673444367687468 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_128 t22335R_106 (by norm_num)

theorem t22335R_104 : rows2 127 300 ≤ 947691840098574873 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_127 t22335R_105 (by norm_num)

theorem t22335R_103 : rows2 126 300 ≤ 949553870040450293 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_126 t22335R_104 (by norm_num)

theorem t22335R_102 : rows2 125 300 ≤ 951248940473254210 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_125 t22335R_103 (by norm_num)

theorem t22335R_101 : rows2 124 300 ≤ 952772430464687856 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_124 t22335R_102 (by norm_num)

theorem t22335R_100 : rows2 123 300 ≤ 954122594519537786 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_123 t22335R_101 (by norm_num)

theorem t22335R_99 : rows2 122 300 ≤ 955294575130197184 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_122 t22335R_100 (by norm_num)

theorem t22335R_98 : rows2 121 300 ≤ 956286112374412355 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_121 t22335R_99 (by norm_num)

theorem t22335R_97 : rows2 120 300 ≤ 957092095008275357 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_120 t22335R_98 (by norm_num)

theorem t22335R_96 : rows2 119 300 ≤ 957710070124764007 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_119 t22335R_97 (by norm_num)

theorem t22335R_95 : rows2 118 300 ≤ 958134323293407321 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_118 t22335R_96 (by norm_num)

theorem t22335R_94 : rows2 117 300 ≤ 958465043461248434 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_117 t22335R_95 (by norm_num)

theorem t22335R_93 : rows2 116 300 ≤ 958801882569548183 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_116 t22335R_94 (by norm_num)

theorem t22335R_92 : rows2 115 300 ≤ 959147740815188861 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_115 t22335R_93 (by norm_num)

theorem t22335R_91 : rows2 114 300 ≤ 959605984504211651 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_114 t22335R_92 (by norm_num)

theorem t22335R_90 : rows2 113 300 ≤ 960073942214013608 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_113 t22335R_91 (by norm_num)

theorem t22335R_89 : rows2 112 300 ≤ 960654551298126807 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_112 t22335R_90 (by norm_num)

theorem t22335R_88 : rows2 111 300 ≤ 961245860874777004 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_111 t22335R_89 (by norm_num)

theorem t22335R_87 : rows2 110 300 ≤ 961950544396781771 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_110 t22335R_88 (by norm_num)

theorem t22335R_86 : rows2 109 300 ≤ 962670045434495398 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_109 t22335R_87 (by norm_num)

theorem t22335R_85 : rows2 108 300 ≤ 963507482733434861 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_108 t22335R_86 (by norm_num)

theorem t22335R_84 : rows2 107 300 ≤ 964362741559204495 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_107 t22335R_85 (by norm_num)

theorem t22335R_83 : rows2 106 300 ≤ 965340235446755729 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_106 t22335R_84 (by norm_num)

theorem t22335R_82 : rows2 105 300 ≤ 966339117985352883 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_105 t22335R_83 (by norm_num)

theorem t22335R_81 : rows2 104 300 ≤ 967465625312566299 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_104 t22335R_82 (by norm_num)

theorem t22335R_80 : rows2 103 300 ≤ 968617727686370365 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_103 t22335R_81 (by norm_num)

theorem t22335R_79 : rows2 102 300 ≤ 969903586430393228 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_102 t22335R_80 (by norm_num)

theorem t22335R_78 : rows2 101 300 ≤ 971219843671818300 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_101 t22335R_79 (by norm_num)

theorem t22335R_77 : rows2 100 300 ≤ 972675903184830459 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_100 t22335R_78 (by norm_num)

theorem t22335R_76 : rows2 99 300 ≤ 974166589956120506 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_99 t22335R_77 (by norm_num)

theorem t22335R_75 : rows2 98 300 ≤ 975802875666795487 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_98 t22335R_76 (by norm_num)

theorem t22335R_74 : rows2 97 300 ≤ 977477455685595008 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_97 t22335R_75 (by norm_num)

theorem t22335R_73 : rows2 96 300 ≤ 979303739176293627 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_96 t22335R_74 (by norm_num)

theorem t22335R_72 : rows2 95 300 ≤ 981216056324045375 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_95 t22335R_73 (by norm_num)

theorem t22335R_71 : rows2 94 300 ≤ 983052245252366837 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_94 t22335R_72 (by norm_num)

theorem t22335R_70 : rows2 93 300 ≤ 984693406332609874 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_93 t22335R_71 (by norm_num)

theorem t22335R_69 : rows2 92 300 ≤ 986248405695913724 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_92 t22335R_70 (by norm_num)

theorem t22335R_68 : rows2 91 300 ≤ 987595576255628391 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_91 t22335R_69 (by norm_num)

theorem t22335R_67 : rows2 90 300 ≤ 988846256779651023 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_90 t22335R_68 (by norm_num)

theorem t22335R_66 : rows2 89 300 ≤ 989876211491003998 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_89 t22335R_67 (by norm_num)

theorem t22335R_65 : rows2 88 300 ≤ 990753809336413008 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_88 t22335R_66 (by norm_num)

theorem t22335R_64 : rows2 87 300 ≤ 991652478976786683 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_87 t22335R_65 (by norm_num)

theorem t22335R_63 : rows2 86 300 ≤ 992574869353590894 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_86 t22335R_64 (by norm_num)

theorem t22335R_62 : rows2 85 300 ≤ 993529216614816336 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_85 t22335R_63 (by norm_num)

theorem t22335R_61 : rows2 84 300 ≤ 994517928404270126 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_84 t22335R_62 (by norm_num)

theorem t22335R_60 : rows2 83 300 ≤ 995548199486599605 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_83 t22335R_61 (by norm_num)

theorem t22335R_59 : rows2 82 300 ≤ 996621023926095799 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_82 t22335R_60 (by norm_num)

theorem t22335R_58 : rows2 81 300 ≤ 997742911297277438 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_81 t22335R_59 (by norm_num)

theorem t22335R_57 : rows2 80 300 ≤ 998913804808268772 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_80 t22335R_58 (by norm_num)

theorem t22335R_56 : rows2 79 300 ≤ 1000138970904933720 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_79 t22335R_57 (by norm_num)

theorem t22335R_55 : rows2 78 300 ≤ 1001417871887316257 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_78 t22335R_56 (by norm_num)

theorem t22335R_54 : rows2 77 300 ≤ 1002754667343131370 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_77 t22335R_55 (by norm_num)

theorem t22335R_53 : rows2 76 300 ≤ 1004147572284196745 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_76 t22335R_54 (by norm_num)

theorem t22335R_52 : rows2 75 300 ≤ 1005600056455126487 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_75 t22335R_53 (by norm_num)

theorem t22335R_51 : rows2 74 300 ≤ 1007109635923789420 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_74 t22335R_52 (by norm_num)

theorem t22335R_50 : rows2 73 300 ≤ 1008679153252108229 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_73 t22335R_51 (by norm_num)

theorem t22335R_49 : rows2 72 300 ≤ 1010309517446616563 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_72 t22335R_50 (by norm_num)

theorem t22335R_48 : rows2 71 300 ≤ 1012006435922929685 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_71 t22335R_49 (by norm_num)

theorem t22335R_47 : rows2 70 300 ≤ 1013769024679024465 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_70 t22335R_48 (by norm_num)

theorem t22335R_46 : rows2 69 300 ≤ 1015599254337659528 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_69 t22335R_47 (by norm_num)

theorem t22335R_45 : rows2 68 300 ≤ 1017493562855325064 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_68 t22335R_46 (by norm_num)

theorem t22335R_44 : rows2 67 300 ≤ 1019452434042236100 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_67 t22335R_45 (by norm_num)

theorem t22335R_43 : rows2 66 300 ≤ 1021471510188255387 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_66 t22335R_44 (by norm_num)

theorem t22335R_42 : rows2 65 300 ≤ 1023550225950766469 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_65 t22335R_43 (by norm_num)

theorem t22335R_41 : rows2 64 300 ≤ 1025683253761055091 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_64 t22335R_42 (by norm_num)

theorem t22335R_40 : rows2 63 300 ≤ 1027869584231746512 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_63 t22335R_41 (by norm_num)

theorem t22335R_39 : rows2 62 300 ≤ 1030103178113417281 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_62 t22335R_40 (by norm_num)

theorem t22335R_38 : rows2 61 300 ≤ 1032382286763897281 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_61 t22335R_39 (by norm_num)

theorem t22335R_37 : rows2 60 300 ≤ 1034700684559248470 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_60 t22335R_38 (by norm_num)

theorem t22335R_36 : rows2 59 300 ≤ 1037056251627916336 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_59 t22335R_37 (by norm_num)

theorem t22335R_35 : rows2 58 300 ≤ 1039442434729220171 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_58 t22335R_36 (by norm_num)

theorem t22335R_34 : rows2 57 300 ≤ 1041857212548012343 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_57 t22335R_35 (by norm_num)

theorem t22335R_33 : rows2 56 300 ≤ 1044293825643826167 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_56 t22335R_34 (by norm_num)

theorem t22335R_32 : rows2 55 300 ≤ 1046749986633581475 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_55 t22335R_33 (by norm_num)

theorem t22335R_31 : rows2 54 300 ≤ 1049219344172706384 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_54 t22335R_32 (by norm_num)

theorem t22335R_30 : rows2 53 300 ≤ 1051700009677185487 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_53 t22335R_31 (by norm_num)

theorem t22335R_29 : rows2 52 300 ≤ 1054186021997083160 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_52 t22335R_30 (by norm_num)

theorem t22335R_28 : rows2 51 300 ≤ 1056676217918606242 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_51 t22335R_29 (by norm_num)

theorem t22335R_27 : rows2 50 300 ≤ 1059165012692238508 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_50 t22335R_28 (by norm_num)

theorem t22335R_26 : rows2 49 300 ≤ 1061651520177915327 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_49 t22335R_27 (by norm_num)

theorem t22335R_25 : rows2 48 300 ≤ 1064130772123207398 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_48 t22335R_26 (by norm_num)

theorem t22335R_24 : rows2 47 300 ≤ 1066600688696217211 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_47 t22335R_25 (by norm_num)

theorem t22335R_23 : rows2 46 300 ≤ 1069072836087966499 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_46 t22335R_24 (by norm_num)

theorem t22335R_22 : rows2 45 300 ≤ 1071562684124583381 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_45 t22335R_23 (by norm_num)

theorem t22335R_21 : rows2 44 300 ≤ 1074082885040298330 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_44 t22335R_22 (by norm_num)

theorem t22335R_20 : rows2 43 300 ≤ 1076643124453317712 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_43 t22335R_21 (by norm_num)

theorem t22335R_19 : rows2 42 300 ≤ 1079250667867731407 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_42 t22335R_20 (by norm_num)

theorem t22335R_18 : rows2 41 300 ≤ 1081909166512877776 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_41 t22335R_19 (by norm_num)

theorem t22335R_17 : rows2 40 300 ≤ 1084619426502378473 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_40 t22335R_18 (by norm_num)

theorem t22335R_16 : rows2 39 300 ≤ 1087379199991912924 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_39 t22335R_17 (by norm_num)

theorem t22335R_15 : rows2 38 300 ≤ 1090183276739504639 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_38 t22335R_16 (by norm_num)

theorem t22335R_14 : rows2 37 300 ≤ 1093023376474336190 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_37 t22335R_15 (by norm_num)

theorem t22335R_13 : rows2 36 300 ≤ 1095888720080987237 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_36 t22335R_14 (by norm_num)

theorem t22335R_12 : rows2 35 300 ≤ 1098765205184509499 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22335R_35 t22335R_13 (by norm_num)

theorem t22335R_11 : rows2 34 300 ≤ 1101636081985293084 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_11 t22335R_12 (by norm_num)

theorem t22335R_10 : rows2 33 300 ≤ 1104481856184806219 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_10 t22335R_11 (by norm_num)

theorem t22335R_9 : rows2 32 300 ≤ 1107281264451905069 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_9 t22335R_10 (by norm_num)

theorem t22335R_8 : rows2 31 300 ≤ 1110011604937920750 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_8 t22335R_9 (by norm_num)

theorem t22335R_7 : rows2 30 300 ≤ 1112652829265009334 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_7 t22335R_8 (by norm_num)

theorem t22335R_6 : rows2 29 300 ≤ 1115188278735527890 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_6 t22335R_7 (by norm_num)

theorem t22335R_5 : rows2 28 300 ≤ 1117604711744475828 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_5 t22335R_6 (by norm_num)

theorem t22335R_4 : rows2 27 300 ≤ 1119892129098191493 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_4 t22335R_5 (by norm_num)

theorem t22335R_3 : rows2 25 300 ≤ 1124054402034235286 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_3 t22335R_4 (by norm_num)

theorem t22335R_2 : rows2 23 300 ≤ 1127653907063949740 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_2 t22335R_3 (by norm_num)

theorem t22335R_1 : rows2 19 300 ≤ 1133251580482043016 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_1 t22335R_2 (by norm_num)

theorem t22335R_0 : rows2 0 300 ≤ 1140404967899637341 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22335R_0 t22335R_1 (by norm_num)

/-- **The refined certificate on `grid22335R`**: the loss's bound is less than `K`, the 549 parts checked by the
kernel. -/
theorem total2_lt_22335R : total2 < K := by
  rw [total2_eq_rows2_full]
  exact lt_of_le_of_lt t22335R_0 (by decide +kernel)

end

end SieveCert

#print axioms SieveCert.total2_lt_22335R
