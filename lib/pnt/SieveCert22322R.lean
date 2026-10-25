/-
# The refined certificate of the sieve route's loss at `L = 11161/5000` with `n = 300`: `total2 < K`

On `SieveGrid22322R.grid22322R` (`U1 = ⌈(40981/100000)DEN⌉`, `U2 = ⌊(47725/100000)DEN⌋`, `n = 300`),
`SieveCert.total2` is less than `K` (it is below `0.99873K`, rounded up; the certificate of `SieveCertDefs.lean` on
the same grid totals `1.10833K`): `total2` is `rows2 0 n` (`SieveCert2.total2_eq_rows2_full`), and its bound is
assembled one step at a time from the 561 parts' bounds (`rows22322R_0` … `rows22322R_560`, each by `decide +kernel`
in one of the 143 part files): a heavy row's bound from its column pieces' (`rowsJ2_le_of_split`,
`rows2_le_of_rowsJ2`), then the 170 ranges of rows from the last to the first (`rows2_le_of_split`), every bound a
literal and every step a theorem of its own (`c22322R_…`, `hr22322R_…`, `t22322R_…`); the bounds, `⌈1.001 × part⌉`
computed exactly in integers, sum to `1152600486568670170`, less than `K` by `decide +kernel` (`total2_lt_22322R`).

The file imports `SieveCert2.lean` and `SieveCert22322RP1.lean` … `SieveCert22322RP143.lean`.
-/
import SieveCert2
import SieveCert22322RP1
import SieveCert22322RP2
import SieveCert22322RP3
import SieveCert22322RP4
import SieveCert22322RP5
import SieveCert22322RP6
import SieveCert22322RP7
import SieveCert22322RP8
import SieveCert22322RP9
import SieveCert22322RP10
import SieveCert22322RP11
import SieveCert22322RP12
import SieveCert22322RP13
import SieveCert22322RP14
import SieveCert22322RP15
import SieveCert22322RP16
import SieveCert22322RP17
import SieveCert22322RP18
import SieveCert22322RP19
import SieveCert22322RP20
import SieveCert22322RP21
import SieveCert22322RP22
import SieveCert22322RP23
import SieveCert22322RP24
import SieveCert22322RP25
import SieveCert22322RP26
import SieveCert22322RP27
import SieveCert22322RP28
import SieveCert22322RP29
import SieveCert22322RP30
import SieveCert22322RP31
import SieveCert22322RP32
import SieveCert22322RP33
import SieveCert22322RP34
import SieveCert22322RP35
import SieveCert22322RP36
import SieveCert22322RP37
import SieveCert22322RP38
import SieveCert22322RP39
import SieveCert22322RP40
import SieveCert22322RP41
import SieveCert22322RP42
import SieveCert22322RP43
import SieveCert22322RP44
import SieveCert22322RP45
import SieveCert22322RP46
import SieveCert22322RP47
import SieveCert22322RP48
import SieveCert22322RP49
import SieveCert22322RP50
import SieveCert22322RP51
import SieveCert22322RP52
import SieveCert22322RP53
import SieveCert22322RP54
import SieveCert22322RP55
import SieveCert22322RP56
import SieveCert22322RP57
import SieveCert22322RP58
import SieveCert22322RP59
import SieveCert22322RP60
import SieveCert22322RP61
import SieveCert22322RP62
import SieveCert22322RP63
import SieveCert22322RP64
import SieveCert22322RP65
import SieveCert22322RP66
import SieveCert22322RP67
import SieveCert22322RP68
import SieveCert22322RP69
import SieveCert22322RP70
import SieveCert22322RP71
import SieveCert22322RP72
import SieveCert22322RP73
import SieveCert22322RP74
import SieveCert22322RP75
import SieveCert22322RP76
import SieveCert22322RP77
import SieveCert22322RP78
import SieveCert22322RP79
import SieveCert22322RP80
import SieveCert22322RP81
import SieveCert22322RP82
import SieveCert22322RP83
import SieveCert22322RP84
import SieveCert22322RP85
import SieveCert22322RP86
import SieveCert22322RP87
import SieveCert22322RP88
import SieveCert22322RP89
import SieveCert22322RP90
import SieveCert22322RP91
import SieveCert22322RP92
import SieveCert22322RP93
import SieveCert22322RP94
import SieveCert22322RP95
import SieveCert22322RP96
import SieveCert22322RP97
import SieveCert22322RP98
import SieveCert22322RP99
import SieveCert22322RP100
import SieveCert22322RP101
import SieveCert22322RP102
import SieveCert22322RP103
import SieveCert22322RP104
import SieveCert22322RP105
import SieveCert22322RP106
import SieveCert22322RP107
import SieveCert22322RP108
import SieveCert22322RP109
import SieveCert22322RP110
import SieveCert22322RP111
import SieveCert22322RP112
import SieveCert22322RP113
import SieveCert22322RP114
import SieveCert22322RP115
import SieveCert22322RP116
import SieveCert22322RP117
import SieveCert22322RP118
import SieveCert22322RP119
import SieveCert22322RP120
import SieveCert22322RP121
import SieveCert22322RP122
import SieveCert22322RP123
import SieveCert22322RP124
import SieveCert22322RP125
import SieveCert22322RP126
import SieveCert22322RP127
import SieveCert22322RP128
import SieveCert22322RP129
import SieveCert22322RP130
import SieveCert22322RP131
import SieveCert22322RP132
import SieveCert22322RP133
import SieveCert22322RP134
import SieveCert22322RP135
import SieveCert22322RP136
import SieveCert22322RP137
import SieveCert22322RP138
import SieveCert22322RP139
import SieveCert22322RP140
import SieveCert22322RP141
import SieveCert22322RP142
import SieveCert22322RP143

namespace SieveCert

section

attribute [local instance] grid22322R

/-! The chain of bounds: `c22322R_{i}_{m}` for the heavy row `i` from its `m`-th column piece on, `hr22322R_{i}` for
the heavy row `i`, `t22322R_{m}` for the rows from the `m`-th range on; each a theorem of its own, its name distinct
from the other certificates' chains in the same namespace. -/

theorem c22322R_35_0 : rowsJ2 35 36 0 300 ≤ 2945081044147545 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22322R_12 rows22322R_13 (by norm_num)

theorem hr22322R_35 : rows2 35 36 ≤ 2945081044147545 := rows2_le_of_rowsJ2 35 36 c22322R_35_0

theorem c22322R_36_0 : rowsJ2 36 37 0 300 ≤ 2940042854376034 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22322R_14 rows22322R_15 (by norm_num)

theorem hr22322R_36 : rows2 36 37 ≤ 2940042854376034 := rows2_le_of_rowsJ2 36 37 c22322R_36_0

theorem c22322R_37_0 : rowsJ2 37 38 0 300 ≤ 2920598859919595 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22322R_16 rows22322R_17 (by norm_num)

theorem hr22322R_37 : rows2 37 38 ≤ 2920598859919595 := rows2_le_of_rowsJ2 37 38 c22322R_37_0

theorem c22322R_38_0 : rowsJ2 38 39 0 300 ≤ 2889379659035189 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22322R_18 rows22322R_19 (by norm_num)

theorem hr22322R_38 : rows2 38 39 ≤ 2889379659035189 := rows2_le_of_rowsJ2 38 39 c22322R_38_0

theorem c22322R_39_0 : rowsJ2 39 40 0 300 ≤ 2849578950247989 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22322R_20 rows22322R_21 (by norm_num)

theorem hr22322R_39 : rows2 39 40 ≤ 2849578950247989 := rows2_le_of_rowsJ2 39 40 c22322R_39_0

theorem c22322R_40_0 : rowsJ2 40 41 0 300 ≤ 2803840275641764 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22322R_22 rows22322R_23 (by norm_num)

theorem hr22322R_40 : rows2 40 41 ≤ 2803840275641764 := rows2_le_of_rowsJ2 40 41 c22322R_40_0

theorem c22322R_41_0 : rowsJ2 41 42 0 300 ≤ 2755270833460377 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22322R_24 rows22322R_25 (by norm_num)

theorem hr22322R_41 : rows2 41 42 ≤ 2755270833460377 := rows2_le_of_rowsJ2 41 42 c22322R_41_0

theorem c22322R_42_0 : rowsJ2 42 43 0 300 ≤ 2706765362303626 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22322R_26 rows22322R_27 (by norm_num)

theorem hr22322R_42 : rows2 42 43 ≤ 2706765362303626 := rows2_le_of_rowsJ2 42 43 c22322R_42_0

theorem c22322R_43_0 : rowsJ2 43 44 0 300 ≤ 2661589151059371 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22322R_28 rows22322R_29 (by norm_num)

theorem hr22322R_43 : rows2 43 44 ≤ 2661589151059371 := rows2_le_of_rowsJ2 43 44 c22322R_43_0

theorem c22322R_44_1 : rowsJ2 44 45 35 300 ≤ 496062221824402 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22322R_31 rows22322R_32 (by norm_num)

theorem c22322R_44_0 : rowsJ2 44 45 0 300 ≤ 2622628977502030 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22322R_30 c22322R_44_1 (by norm_num)

theorem hr22322R_44 : rows2 44 45 ≤ 2622628977502030 := rows2_le_of_rowsJ2 44 45 c22322R_44_0

theorem c22322R_45_1 : rowsJ2 45 46 35 300 ≤ 545550201991242 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22322R_34 rows22322R_35 (by norm_num)

theorem c22322R_45_0 : rowsJ2 45 46 0 300 ≤ 2593000171833594 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22322R_33 c22322R_45_1 (by norm_num)

theorem hr22322R_45 : rows2 45 46 ≤ 2593000171833594 := rows2_le_of_rowsJ2 45 46 c22322R_45_0

theorem c22322R_46_1 : rowsJ2 46 47 35 300 ≤ 606414593998050 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22322R_37 rows22322R_38 (by norm_num)

theorem c22322R_46_0 : rowsJ2 46 47 0 300 ≤ 2575217908255607 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22322R_36 c22322R_46_1 (by norm_num)

theorem hr22322R_46 : rows2 46 47 ≤ 2575217908255607 := rows2_le_of_rowsJ2 46 47 c22322R_46_0

theorem c22322R_47_1 : rowsJ2 47 48 35 300 ≤ 681209570391322 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22322R_40 rows22322R_41 (by norm_num)

theorem c22322R_47_0 : rowsJ2 47 48 0 300 ≤ 2572211962679050 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22322R_39 c22322R_47_1 (by norm_num)

theorem hr22322R_47 : rows2 47 48 ≤ 2572211962679050 := rows2_le_of_rowsJ2 47 48 c22322R_47_0

theorem c22322R_48_1 : rowsJ2 48 49 35 300 ≤ 765936849497098 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22322R_43 rows22322R_44 (by norm_num)

theorem c22322R_48_0 : rowsJ2 48 49 0 300 ≤ 2579871816101936 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22322R_42 c22322R_48_1 (by norm_num)

theorem hr22322R_48 : rows2 48 49 ≤ 2579871816101936 := rows2_le_of_rowsJ2 48 49 c22322R_48_0

theorem c22322R_49_1 : rowsJ2 49 50 35 300 ≤ 846884352813364 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22322R_46 rows22322R_47 (by norm_num)

theorem c22322R_49_0 : rowsJ2 49 50 0 300 ≤ 2584874508509118 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22322R_45 c22322R_49_1 (by norm_num)

theorem hr22322R_49 : rows2 49 50 ≤ 2584874508509118 := rows2_le_of_rowsJ2 49 50 c22322R_49_0

theorem c22322R_50_1 : rowsJ2 50 51 35 300 ≤ 921136121579731 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22322R_49 rows22322R_50 (by norm_num)

theorem c22322R_50_0 : rowsJ2 50 51 0 300 ≤ 2584032005666328 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22322R_48 c22322R_50_1 (by norm_num)

theorem hr22322R_50 : rows2 50 51 ≤ 2584032005666328 := rows2_le_of_rowsJ2 50 51 c22322R_50_0

theorem c22322R_51_2 : rowsJ2 51 52 44 300 ≤ 614929691492862 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22322R_53 rows22322R_54 (by norm_num)

theorem c22322R_51_1 : rowsJ2 51 52 35 300 ≤ 993453394913029 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22322R_52 c22322R_51_2 (by norm_num)

theorem c22322R_51_0 : rowsJ2 51 52 0 300 ≤ 2582674498087574 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22322R_51 c22322R_51_1 (by norm_num)

theorem hr22322R_51 : rows2 51 52 ≤ 2582674498087574 := rows2_le_of_rowsJ2 51 52 c22322R_51_0

theorem c22322R_52_2 : rowsJ2 52 53 44 300 ≤ 677545712234222 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22322R_57 rows22322R_58 (by norm_num)

theorem c22322R_52_1 : rowsJ2 52 53 35 300 ≤ 1058947572068873 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22322R_56 c22322R_52_2 (by norm_num)

theorem c22322R_52_0 : rowsJ2 52 53 0 300 ≤ 2575643722122114 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22322R_55 c22322R_52_1 (by norm_num)

theorem hr22322R_52 : rows2 52 53 ≤ 2575643722122114 := rows2_le_of_rowsJ2 52 53 c22322R_52_0

theorem c22322R_53_2 : rowsJ2 53 54 44 300 ≤ 734796093127683 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22322R_61 rows22322R_62 (by norm_num)

theorem c22322R_53_1 : rowsJ2 53 54 35 300 ≤ 1121771250299419 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22322R_60 c22322R_53_2 (by norm_num)

theorem c22322R_53_0 : rowsJ2 53 54 0 300 ≤ 2567509874913659 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22322R_59 c22322R_53_1 (by norm_num)

theorem hr22322R_53 : rows2 53 54 ≤ 2567509874913659 := rows2_le_of_rowsJ2 53 54 c22322R_53_0

theorem c22322R_54_2 : rowsJ2 54 55 44 300 ≤ 781394538576346 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22322R_65 rows22322R_66 (by norm_num)

theorem c22322R_54_1 : rowsJ2 54 55 35 300 ≤ 1177066543435739 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22322R_64 c22322R_54_2 (by norm_num)

theorem c22322R_54_0 : rowsJ2 54 55 0 300 ≤ 2553320171885327 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22322R_63 c22322R_54_1 (by norm_num)

theorem hr22322R_54 : rows2 54 55 ≤ 2553320171885327 := rows2_le_of_rowsJ2 54 55 c22322R_54_0

theorem c22322R_55_2 : rowsJ2 55 56 44 300 ≤ 822003341842278 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22322R_69 rows22322R_70 (by norm_num)

theorem c22322R_55_1 : rowsJ2 55 56 35 300 ≤ 1228937737698641 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22322R_68 c22322R_55_2 (by norm_num)

theorem c22322R_55_0 : rowsJ2 55 56 0 300 ≤ 2537615723966964 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22322R_67 c22322R_55_1 (by norm_num)

theorem hr22322R_55 : rows2 55 56 ≤ 2537615723966964 := rows2_le_of_rowsJ2 55 56 c22322R_55_0

theorem c22322R_56_2 : rowsJ2 56 57 44 300 ≤ 851259310241545 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22322R_73 rows22322R_74 (by norm_num)

theorem c22322R_56_1 : rowsJ2 56 57 35 300 ≤ 1272394518142265 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22322R_72 c22322R_56_2 (by norm_num)

theorem c22322R_56_0 : rowsJ2 56 57 0 300 ≤ 2515139244323421 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22322R_71 c22322R_56_1 (by norm_num)

theorem hr22322R_56 : rows2 56 57 ≤ 2515139244323421 := rows2_le_of_rowsJ2 56 57 c22322R_56_0

theorem c22322R_57_2 : rowsJ2 57 58 44 300 ≤ 873872473503943 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22322R_77 rows22322R_78 (by norm_num)

theorem c22322R_57_1 : rowsJ2 57 58 35 300 ≤ 1311655666575656 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22322R_76 c22322R_57_2 (by norm_num)

theorem c22322R_57_0 : rowsJ2 57 58 0 300 ≤ 2490747210742910 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22322R_75 c22322R_57_1 (by norm_num)

theorem hr22322R_57 : rows2 57 58 ≤ 2490747210742910 := rows2_le_of_rowsJ2 57 58 c22322R_57_0

theorem c22322R_58_2 : rowsJ2 58 59 44 300 ≤ 890031916013562 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22322R_81 rows22322R_82 (by norm_num)

theorem c22322R_58_1 : rowsJ2 58 59 35 300 ≤ 1342041056575978 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22322R_80 c22322R_58_2 (by norm_num)

theorem c22322R_58_0 : rowsJ2 58 59 0 300 ≤ 2459497441064453 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22322R_79 c22322R_58_1 (by norm_num)

theorem hr22322R_58 : rows2 58 59 ≤ 2459497441064453 := rows2_le_of_rowsJ2 58 59 c22322R_58_0

theorem c22322R_59_2 : rowsJ2 59 60 44 300 ≤ 899847742463665 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22322R_85 rows22322R_86 (by norm_num)

theorem c22322R_59_1 : rowsJ2 59 60 35 300 ≤ 1367950876687636 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22322R_84 c22322R_59_2 (by norm_num)

theorem c22322R_59_0 : rowsJ2 59 60 0 300 ≤ 2426267603977192 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22322R_83 c22322R_59_1 (by norm_num)

theorem hr22322R_59 : rows2 59 60 ≤ 2426267603977192 := rows2_le_of_rowsJ2 59 60 c22322R_59_0

theorem c22322R_60_2 : rowsJ2 60 61 44 300 ≤ 903525711898943 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22322R_89 rows22322R_90 (by norm_num)

theorem c22322R_60_1 : rowsJ2 60 61 35 300 ≤ 1384777749942289 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22322R_88 c22322R_60_2 (by norm_num)

theorem c22322R_60_0 : rowsJ2 60 61 0 300 ≤ 2386382102877910 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22322R_87 c22322R_60_1 (by norm_num)

theorem hr22322R_60 : rows2 60 61 ≤ 2386382102877910 := rows2_le_of_rowsJ2 60 61 c22322R_60_0

theorem c22322R_61_2 : rowsJ2 61 62 45 300 ≤ 833188818046181 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22322R_93 rows22322R_94 (by norm_num)

theorem c22322R_61_1 : rowsJ2 61 62 35 300 ≤ 1396935820441303 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22322R_92 c22322R_61_2 (by norm_num)

theorem c22322R_61_0 : rowsJ2 61 62 0 300 ≤ 2344759459316238 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22322R_91 c22322R_61_1 (by norm_num)

theorem hr22322R_61 : rows2 61 62 ≤ 2344759459316238 := rows2_le_of_rowsJ2 61 62 c22322R_61_0

theorem c22322R_62_1 : rowsJ2 62 63 35 300 ≤ 1399740149496973 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22322R_96 rows22322R_97 (by norm_num)

theorem c22322R_62_0 : rowsJ2 62 63 0 300 ≤ 2296460555585028 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22322R_95 c22322R_62_1 (by norm_num)

theorem hr22322R_62 : rows2 62 63 ≤ 2296460555585028 := rows2_le_of_rowsJ2 62 63 c22322R_62_0

theorem c22322R_63_1 : rowsJ2 63 64 35 300 ≤ 1397771710379284 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22322R_99 rows22322R_100 (by norm_num)

theorem c22322R_63_0 : rowsJ2 63 64 0 300 ≤ 2246797878872372 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22322R_98 c22322R_63_1 (by norm_num)

theorem hr22322R_63 : rows2 63 64 ≤ 2246797878872372 := rows2_le_of_rowsJ2 63 64 c22322R_63_0

theorem c22322R_64_1 : rowsJ2 64 65 35 300 ≤ 1386500720825599 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22322R_102 rows22322R_103 (by norm_num)

theorem c22322R_64_0 : rowsJ2 64 65 0 300 ≤ 2190996325612096 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22322R_101 c22322R_64_1 (by norm_num)

theorem hr22322R_64 : rows2 64 65 ≤ 2190996325612096 := rows2_le_of_rowsJ2 64 65 c22322R_64_0

theorem c22322R_65_1 : rowsJ2 65 66 35 300 ≤ 1370524700153802 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22322R_105 rows22322R_106 (by norm_num)

theorem c22322R_65_0 : rowsJ2 65 66 0 300 ≤ 2134215455466528 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22322R_104 c22322R_65_1 (by norm_num)

theorem hr22322R_65 : rows2 65 66 ≤ 2134215455466528 := rows2_le_of_rowsJ2 65 66 c22322R_65_0

theorem c22322R_66_1 : rowsJ2 66 67 35 300 ≤ 1345420957130905 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22322R_108 rows22322R_109 (by norm_num)

theorem c22322R_66_0 : rowsJ2 66 67 0 300 ≤ 2072005085579459 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22322R_107 c22322R_66_1 (by norm_num)

theorem hr22322R_66 : rows2 66 67 ≤ 2072005085579459 := rows2_le_of_rowsJ2 66 67 c22322R_66_0

theorem c22322R_67_2 : rowsJ2 67 68 47 300 ≤ 616450465073683 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22322R_112 rows22322R_113 (by norm_num)

theorem c22322R_67_1 : rowsJ2 67 68 35 300 ≤ 1316384510420531 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22322R_111 c22322R_67_2 (by norm_num)

theorem c22322R_67_0 : rowsJ2 67 68 0 300 ≤ 2009633385899037 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22322R_110 c22322R_67_1 (by norm_num)

theorem hr22322R_67 : rows2 67 68 ≤ 2009633385899037 := rows2_le_of_rowsJ2 67 68 c22322R_67_0

theorem c22322R_68_2 : rowsJ2 68 69 48 300 ≤ 540538899100214 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22322R_116 rows22322R_117 (by norm_num)

theorem c22322R_68_1 : rowsJ2 68 69 35 300 ≤ 1278975151567668 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22322R_115 c22322R_68_2 (by norm_num)

theorem c22322R_68_0 : rowsJ2 68 69 0 300 ≤ 1942426802298272 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22322R_114 c22322R_68_1 (by norm_num)

theorem hr22322R_68 : rows2 68 69 ≤ 1942426802298272 := rows2_le_of_rowsJ2 68 69 c22322R_68_0

theorem c22322R_69_2 : rowsJ2 69 70 49 300 ≤ 468142875967344 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22322R_120 rows22322R_121 (by norm_num)

theorem c22322R_69_1 : rowsJ2 69 70 35 300 ≤ 1238620480560626 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22322R_119 c22322R_69_2 (by norm_num)

theorem c22322R_69_0 : rowsJ2 69 70 0 300 ≤ 1876114686659752 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22322R_118 c22322R_69_1 (by norm_num)

theorem hr22322R_69 : rows2 69 70 ≤ 1876114686659752 := rows2_le_of_rowsJ2 69 70 c22322R_69_0

theorem c22322R_70_2 : rowsJ2 70 71 50 300 ≤ 399796072704560 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22322R_124 rows22322R_125 (by norm_num)

theorem c22322R_70_1 : rowsJ2 70 71 35 300 ≤ 1190997576534213 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22322R_123 c22322R_70_2 (by norm_num)

theorem c22322R_70_0 : rowsJ2 70 71 0 300 ≤ 1806149181709505 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22322R_122 c22322R_70_1 (by norm_num)

theorem hr22322R_70 : rows2 70 71 ≤ 1806149181709505 := rows2_le_of_rowsJ2 70 71 c22322R_70_0

theorem c22322R_71_2 : rowsJ2 71 72 51 300 ≤ 336105058463984 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22322R_128 rows22322R_129 (by norm_num)

theorem c22322R_71_1 : rowsJ2 71 72 35 300 ≤ 1141672581296991 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22322R_127 c22322R_71_2 (by norm_num)

theorem c22322R_71_0 : rowsJ2 71 72 0 300 ≤ 1738183384519222 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22322R_126 c22322R_71_1 (by norm_num)

theorem hr22322R_71 : rows2 71 72 ≤ 1738183384519222 := rows2_le_of_rowsJ2 71 72 c22322R_71_0

theorem c22322R_72_2 : rowsJ2 72 73 54 300 ≤ 223158334189357 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22322R_132 rows22322R_133 (by norm_num)

theorem c22322R_72_1 : rowsJ2 72 73 35 300 ≤ 1087665289977172 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22322R_131 c22322R_72_2 (by norm_num)

theorem c22322R_72_0 : rowsJ2 72 73 0 300 ≤ 1669251438374475 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22322R_130 c22322R_72_1 (by norm_num)

theorem hr22322R_72 : rows2 72 73 ≤ 1669251438374475 := rows2_le_of_rowsJ2 72 73 c22322R_72_0

theorem c22322R_73_3 : rowsJ2 73 74 68 300 ≤ 29090776181051 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22322R_137 rows22322R_138 (by norm_num)

theorem c22322R_73_2 : rowsJ2 73 74 58 300 ≤ 123388728886587 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22322R_136 c22322R_73_3 (by norm_num)

theorem c22322R_73_1 : rowsJ2 73 74 35 300 ≤ 1036286833803962 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22322R_135 c22322R_73_2 (by norm_num)

theorem c22322R_73_0 : rowsJ2 73 74 0 300 ≤ 1606485890418231 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22322R_134 c22322R_73_1 (by norm_num)

theorem hr22322R_73 : rows2 73 74 ≤ 1606485890418231 := rows2_le_of_rowsJ2 73 74 c22322R_73_0

theorem c22322R_74_3 : rowsJ2 74 75 68 300 ≤ 35242397715490 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22322R_142 rows22322R_143 (by norm_num)

theorem c22322R_74_2 : rowsJ2 74 75 59 300 ≤ 101054573580160 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22322R_141 c22322R_74_3 (by norm_num)

theorem c22322R_74_1 : rowsJ2 74 75 35 300 ≤ 982964193500317 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22322R_140 c22322R_74_2 (by norm_num)

theorem c22322R_74_0 : rowsJ2 74 75 0 300 ≤ 1545001707850540 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22322R_139 c22322R_74_1 (by norm_num)

theorem hr22322R_74 : rows2 74 75 ≤ 1545001707850540 := rows2_le_of_rowsJ2 74 75 c22322R_74_0

theorem c22322R_75_3 : rowsJ2 75 76 68 300 ≤ 40085994641323 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22322R_147 rows22322R_148 (by norm_num)

theorem c22322R_75_2 : rowsJ2 75 76 60 300 ≤ 82995051020669 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22322R_146 c22322R_75_3 (by norm_num)

theorem c22322R_75_1 : rowsJ2 75 76 35 300 ≤ 929438845910245 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22322R_145 c22322R_75_2 (by norm_num)

theorem c22322R_75_0 : rowsJ2 75 76 0 300 ≤ 1486693681973551 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22322R_144 c22322R_75_1 (by norm_num)

theorem hr22322R_75 : rows2 75 76 ≤ 1486693681973551 := rows2_le_of_rowsJ2 75 76 c22322R_75_0

theorem c22322R_76_4 : rowsJ2 76 77 72 300 ≤ 30650435544725 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22322R_153 rows22322R_154 (by norm_num)

theorem c22322R_76_3 : rowsJ2 76 77 68 300 ≤ 43607015607172 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22322R_152 c22322R_76_4 (by norm_num)

theorem c22322R_76_2 : rowsJ2 76 77 61 300 ≤ 69074016735565 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22322R_151 c22322R_76_3 (by norm_num)

theorem c22322R_76_1 : rowsJ2 76 77 35 300 ≤ 875948723626611 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22322R_150 c22322R_76_2 (by norm_num)

theorem c22322R_76_0 : rowsJ2 76 77 0 300 ≤ 1426478303905105 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22322R_149 c22322R_76_1 (by norm_num)

theorem hr22322R_76 : rows2 76 77 ≤ 1426478303905105 := rows2_le_of_rowsJ2 76 77 c22322R_76_0

theorem c22322R_77_4 : rowsJ2 77 78 72 300 ≤ 32125798454389 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22322R_159 rows22322R_160 (by norm_num)

theorem c22322R_77_3 : rowsJ2 77 78 68 300 ≤ 44971066942023 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22322R_158 c22322R_77_4 (by norm_num)

theorem c22322R_77_2 : rowsJ2 77 78 61 300 ≤ 63725586886133 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22322R_157 c22322R_77_3 (by norm_num)

theorem c22322R_77_1 : rowsJ2 77 78 35 300 ≤ 822035147061459 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22322R_156 c22322R_77_2 (by norm_num)

theorem c22322R_77_0 : rowsJ2 77 78 0 300 ≤ 1368827043863074 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22322R_155 c22322R_77_1 (by norm_num)

theorem hr22322R_77 : rows2 77 78 ≤ 1368827043863074 := rows2_le_of_rowsJ2 77 78 c22322R_77_0

theorem c22322R_78_4 : rowsJ2 78 79 72 300 ≤ 32321702099257 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22322R_165 rows22322R_166 (by norm_num)

theorem c22322R_78_3 : rowsJ2 78 79 68 300 ≤ 45057868846404 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22322R_164 c22322R_78_4 (by norm_num)

theorem c22322R_78_2 : rowsJ2 78 79 61 300 ≤ 58347853918130 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22322R_163 c22322R_78_3 (by norm_num)

theorem c22322R_78_1 : rowsJ2 78 79 35 300 ≤ 768867005803510 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22322R_162 c22322R_78_2 (by norm_num)

theorem c22322R_78_0 : rowsJ2 78 79 0 300 ≤ 1309887332700993 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22322R_161 c22322R_78_1 (by norm_num)

theorem hr22322R_78 : rows2 78 79 ≤ 1309887332700993 := rows2_le_of_rowsJ2 78 79 c22322R_78_0

theorem c22322R_79_4 : rowsJ2 79 80 72 300 ≤ 31201546138875 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22322R_171 rows22322R_172 (by norm_num)

theorem c22322R_79_3 : rowsJ2 79 80 68 300 ≤ 43828745579158 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22322R_170 c22322R_79_4 (by norm_num)

theorem c22322R_79_2 : rowsJ2 79 80 61 300 ≤ 52990820396528 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22322R_169 c22322R_79_3 (by norm_num)

theorem c22322R_79_1 : rowsJ2 79 80 35 300 ≤ 716494717534870 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22322R_168 c22322R_79_2 (by norm_num)

theorem c22322R_79_0 : rowsJ2 79 80 0 300 ≤ 1254680690473313 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22322R_167 c22322R_79_1 (by norm_num)

theorem hr22322R_79 : rows2 79 80 ≤ 1254680690473313 := rows2_le_of_rowsJ2 79 80 c22322R_79_0

theorem c22322R_80_5 : rowsJ2 80 81 76 300 ≤ 14960103733062 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22322R_178 rows22322R_179 (by norm_num)

theorem c22322R_80_4 : rowsJ2 80 81 72 300 ≤ 29784772500504 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22322R_177 c22322R_80_5 (by norm_num)

theorem c22322R_80_3 : rowsJ2 80 81 68 300 ≤ 42305208660494 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22322R_176 c22322R_80_4 (by norm_num)

theorem c22322R_80_2 : rowsJ2 80 81 62 300 ≤ 46588068178571 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22322R_175 c22322R_80_3 (by norm_num)

theorem c22322R_80_1 : rowsJ2 80 81 36 300 ≤ 616892423717170 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22322R_174 c22322R_80_2 (by norm_num)

theorem c22322R_80_0 : rowsJ2 80 81 0 300 ≤ 1198770580981874 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22322R_173 c22322R_80_1 (by norm_num)

theorem hr22322R_80 : rows2 80 81 ≤ 1198770580981874 := rows2_le_of_rowsJ2 80 81 c22322R_80_0

theorem c22322R_81_5 : rowsJ2 81 82 76 300 ≤ 16279389444753 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22322R_185 rows22322R_186 (by norm_num)

theorem c22322R_81_4 : rowsJ2 81 82 72 300 ≤ 28753646576395 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22322R_184 c22322R_81_5 (by norm_num)

theorem c22322R_81_3 : rowsJ2 81 82 68 300 ≤ 40565832266715 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22322R_183 c22322R_81_4 (by norm_num)

theorem c22322R_81_2 : rowsJ2 81 82 62 300 ≤ 43884744396300 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22322R_182 c22322R_81_3 (by norm_num)

theorem c22322R_81_1 : rowsJ2 81 82 36 300 ≤ 570137142655851 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22322R_181 c22322R_81_2 (by norm_num)

theorem c22322R_81_0 : rowsJ2 81 82 0 300 ≤ 1147707951007772 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22322R_180 c22322R_81_1 (by norm_num)

theorem hr22322R_81 : rows2 81 82 ≤ 1147707951007772 := rows2_le_of_rowsJ2 81 82 c22322R_81_0

theorem c22322R_82_5 : rowsJ2 82 83 76 300 ≤ 17917707643466 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22322R_192 rows22322R_193 (by norm_num)

theorem c22322R_82_4 : rowsJ2 82 83 72 300 ≤ 28253449201052 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22322R_191 c22322R_82_5 (by norm_num)

theorem c22322R_82_3 : rowsJ2 82 83 68 300 ≤ 39411393707681 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22322R_190 c22322R_82_4 (by norm_num)

theorem c22322R_82_2 : rowsJ2 82 83 62 300 ≤ 42385917207620 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22322R_189 c22322R_82_3 (by norm_num)

theorem c22322R_82_1 : rowsJ2 82 83 37 300 ≤ 483522649261963 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22322R_188 c22322R_82_2 (by norm_num)

theorem c22322R_82_0 : rowsJ2 82 83 0 300 ≤ 1096786948282577 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22322R_187 c22322R_82_1 (by norm_num)

theorem hr22322R_82 : rows2 82 83 ≤ 1096786948282577 := rows2_le_of_rowsJ2 82 83 c22322R_82_0

theorem c22322R_83_5 : rowsJ2 83 84 75 300 ≤ 22589625048566 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22322R_199 rows22322R_200 (by norm_num)

theorem c22322R_83_4 : rowsJ2 83 84 71 300 ≤ 31835730543397 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22322R_198 c22322R_83_5 (by norm_num)

theorem c22322R_83_3 : rowsJ2 83 84 67 300 ≤ 40568475122886 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22322R_197 c22322R_83_4 (by norm_num)

theorem c22322R_83_2 : rowsJ2 83 84 62 300 ≤ 42181323270087 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22322R_196 c22322R_83_3 (by norm_num)

theorem c22322R_83_1 : rowsJ2 83 84 37 300 ≤ 444434220173572 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22322R_195 c22322R_83_2 (by norm_num)

theorem c22322R_83_0 : rowsJ2 83 84 0 300 ≤ 1051547648252509 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22322R_194 c22322R_83_1 (by norm_num)

theorem hr22322R_83 : rows2 83 84 ≤ 1051547648252509 := rows2_le_of_rowsJ2 83 84 c22322R_83_0

theorem c22322R_84_5 : rowsJ2 84 85 75 300 ≤ 26386051191725 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22322R_206 rows22322R_207 (by norm_num)

theorem c22322R_84_4 : rowsJ2 84 85 71 300 ≤ 33823865510246 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22322R_205 c22322R_84_5 (by norm_num)

theorem c22322R_84_3 : rowsJ2 84 85 67 300 ≤ 42003330106809 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22322R_204 c22322R_84_4 (by norm_num)

theorem c22322R_84_2 : rowsJ2 84 85 62 300 ≤ 43603933224817 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22322R_203 c22322R_84_3 (by norm_num)

theorem c22322R_84_1 : rowsJ2 84 85 38 300 ≤ 372739017941453 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22322R_202 c22322R_84_2 (by norm_num)

theorem c22322R_84_0 : rowsJ2 84 85 0 300 ≤ 1007462902135633 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22322R_201 c22322R_84_1 (by norm_num)

theorem hr22322R_84 : rows2 84 85 ≤ 1007462902135633 := rows2_le_of_rowsJ2 84 85 c22322R_84_0

theorem c22322R_85_6 : rowsJ2 85 86 80 300 ≤ 25952511426572 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22322R_214 rows22322R_215 (by norm_num)

theorem c22322R_85_5 : rowsJ2 85 86 75 300 ≤ 32665212167896 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22322R_213 c22322R_85_6 (by norm_num)

theorem c22322R_85_4 : rowsJ2 85 86 71 300 ≤ 38495956489432 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22322R_212 c22322R_85_5 (by norm_num)

theorem c22322R_85_3 : rowsJ2 85 86 67 300 ≤ 45720351081664 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22322R_211 c22322R_85_4 (by norm_num)

theorem c22322R_85_2 : rowsJ2 85 86 62 300 ≤ 47308895818857 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22322R_210 c22322R_85_3 (by norm_num)

theorem c22322R_85_1 : rowsJ2 85 86 39 300 ≤ 311422486075872 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22322R_209 c22322R_85_2 (by norm_num)

theorem c22322R_85_0 : rowsJ2 85 86 0 300 ≤ 970298827056392 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22322R_208 c22322R_85_1 (by norm_num)

theorem hr22322R_85 : rows2 85 86 ≤ 970298827056392 := rows2_le_of_rowsJ2 85 86 c22322R_85_0

theorem c22322R_86_6 : rowsJ2 86 87 80 300 ≤ 35679005961284 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22322R_222 rows22322R_223 (by norm_num)

theorem c22322R_86_5 : rowsJ2 86 87 75 300 ≤ 41446957121652 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22322R_221 c22322R_86_6 (by norm_num)

theorem c22322R_86_4 : rowsJ2 86 87 71 300 ≤ 45868686300629 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22322R_220 c22322R_86_5 (by norm_num)

theorem c22322R_86_3 : rowsJ2 86 87 67 300 ≤ 52238734046580 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22322R_219 c22322R_86_4 (by norm_num)

theorem c22322R_86_2 : rowsJ2 86 87 62 300 ≤ 53813379668206 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22322R_218 c22322R_86_3 (by norm_num)

theorem c22322R_86_1 : rowsJ2 86 87 40 300 ≤ 260814976770155 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22322R_217 c22322R_86_2 (by norm_num)

theorem c22322R_86_0 : rowsJ2 86 87 0 300 ≤ 935126335959753 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22322R_216 c22322R_86_1 (by norm_num)

theorem hr22322R_86 : rows2 86 87 ≤ 935126335959753 := rows2_le_of_rowsJ2 86 87 c22322R_86_0

theorem c22322R_87_6 : rowsJ2 87 88 80 300 ≤ 48758390094370 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22322R_230 rows22322R_231 (by norm_num)

theorem c22322R_87_5 : rowsJ2 87 88 75 300 ≤ 53977879843545 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22322R_229 c22322R_87_6 (by norm_num)

theorem c22322R_87_4 : rowsJ2 87 88 71 300 ≤ 57187789684762 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22322R_228 c22322R_87_5 (by norm_num)

theorem c22322R_87_3 : rowsJ2 87 88 67 300 ≤ 62420113079071 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22322R_227 c22322R_87_4 (by norm_num)

theorem c22322R_87_2 : rowsJ2 87 88 62 300 ≤ 63981138813986 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22322R_226 c22322R_87_3 (by norm_num)

theorem c22322R_87_1 : rowsJ2 87 88 43 300 ≤ 179236778543316 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22322R_225 c22322R_87_2 (by norm_num)

theorem c22322R_87_0 : rowsJ2 87 88 0 300 ≤ 908190427699711 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22322R_224 c22322R_87_1 (by norm_num)

theorem hr22322R_87 : rows2 87 88 ≤ 908190427699711 := rows2_le_of_rowsJ2 87 88 c22322R_87_0

theorem c22322R_88_6 : rowsJ2 88 89 81 300 ≤ 62482691127587 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22322R_238 rows22322R_239 (by norm_num)

theorem c22322R_88_5 : rowsJ2 88 89 76 300 ≤ 69578812948014 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22322R_237 c22322R_88_6 (by norm_num)

theorem c22322R_88_4 : rowsJ2 88 89 71 300 ≤ 72067948157613 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22322R_236 c22322R_88_5 (by norm_num)

theorem c22322R_88_3 : rowsJ2 88 89 67 300 ≤ 76307435150593 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22322R_235 c22322R_88_4 (by norm_num)

theorem c22322R_88_2 : rowsJ2 88 89 62 300 ≤ 77855115459040 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22322R_234 c22322R_88_3 (by norm_num)

theorem c22322R_88_1 : rowsJ2 88 89 48 300 ≤ 109118398368020 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22322R_233 c22322R_88_2 (by norm_num)

theorem c22322R_88_0 : rowsJ2 88 89 0 300 ≤ 884125608326381 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22322R_232 c22322R_88_1 (by norm_num)

theorem hr22322R_88 : rows2 88 89 ≤ 884125608326381 := rows2_le_of_rowsJ2 88 89 c22322R_88_0

theorem c22322R_89_6 : rowsJ2 89 90 81 300 ≤ 248098790234496 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22322R_246 rows22322R_247 (by norm_num)

theorem c22322R_89_5 : rowsJ2 89 90 76 300 ≤ 255567982726497 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22322R_245 c22322R_89_6 (by norm_num)

theorem c22322R_89_4 : rowsJ2 89 90 71 300 ≤ 257086518552686 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22322R_244 c22322R_89_5 (by norm_num)

theorem c22322R_89_3 : rowsJ2 89 90 67 300 ≤ 260165831955171 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22322R_243 c22322R_89_4 (by norm_num)

theorem c22322R_89_2 : rowsJ2 89 90 62 300 ≤ 261700459211411 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22322R_242 c22322R_89_3 (by norm_num)

theorem c22322R_89_1 : rowsJ2 89 90 51 300 ≤ 267937757023284 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22322R_241 c22322R_89_2 (by norm_num)

theorem c22322R_89_0 : rowsJ2 89 90 0 300 ≤ 1034210235556753 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22322R_240 c22322R_89_1 (by norm_num)

theorem hr22322R_89 : rows2 89 90 ≤ 1034210235556753 := rows2_le_of_rowsJ2 89 90 c22322R_89_0

theorem c22322R_90_6 : rowsJ2 90 91 80 300 ≤ 385647910380324 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22322R_254 rows22322R_255 (by norm_num)

theorem c22322R_90_5 : rowsJ2 90 91 75 300 ≤ 390575160660634 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22322R_253 c22322R_90_6 (by norm_num)

theorem c22322R_90_4 : rowsJ2 90 91 70 300 ≤ 391695859693375 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22322R_252 c22322R_90_5 (by norm_num)

theorem c22322R_90_3 : rowsJ2 90 91 66 300 ≤ 394237610911737 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22322R_251 c22322R_90_4 (by norm_num)

theorem c22322R_90_2 : rowsJ2 90 91 61 300 ≤ 394946603291384 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22322R_250 c22322R_90_3 (by norm_num)

theorem c22322R_90_1 : rowsJ2 90 91 52 300 ≤ 396229926486122 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22322R_249 c22322R_90_2 (by norm_num)

theorem c22322R_90_0 : rowsJ2 90 91 0 300 ≤ 1132836251097057 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22322R_248 c22322R_90_1 (by norm_num)

theorem hr22322R_90 : rows2 90 91 ≤ 1132836251097057 := rows2_le_of_rowsJ2 90 91 c22322R_90_0

theorem c22322R_91_5 : rowsJ2 91 92 75 300 ≤ 638540069316010 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22322R_261 rows22322R_262 (by norm_num)

theorem c22322R_91_4 : rowsJ2 91 92 70 300 ≤ 639062771637203 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22322R_260 c22322R_91_5 (by norm_num)

theorem c22322R_91_3 : rowsJ2 91 92 66 300 ≤ 640733941126555 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22322R_259 c22322R_91_4 (by norm_num)

theorem c22322R_91_2 : rowsJ2 91 92 61 300 ≤ 641435860628534 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22322R_258 c22322R_91_3 (by norm_num)

theorem c22322R_91_1 : rowsJ2 91 92 53 300 ≤ 641435860628534 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22322R_257 c22322R_91_2 (by norm_num)

theorem c22322R_91_0 : rowsJ2 91 92 0 300 ≤ 1348814282880672 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22322R_256 c22322R_91_1 (by norm_num)

theorem hr22322R_91 : rows2 91 92 ≤ 1348814282880672 := rows2_le_of_rowsJ2 91 92 c22322R_91_0

theorem c22322R_92_5 : rowsJ2 92 93 75 300 ≤ 759576256854712 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22322R_268 rows22322R_269 (by norm_num)

theorem c22322R_92_4 : rowsJ2 92 93 70 300 ≤ 759741647351106 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22322R_267 c22322R_92_5 (by norm_num)

theorem c22322R_92_3 : rowsJ2 92 93 66 300 ≤ 760726372361246 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22322R_266 c22322R_92_4 (by norm_num)

theorem c22322R_92_2 : rowsJ2 92 93 61 300 ≤ 761421393018790 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22322R_265 c22322R_92_3 (by norm_num)

theorem c22322R_92_1 : rowsJ2 92 93 53 300 ≤ 761421393018790 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22322R_264 c22322R_92_2 (by norm_num)

theorem c22322R_92_0 : rowsJ2 92 93 0 300 ≤ 1437050751127638 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22322R_263 c22322R_92_1 (by norm_num)

theorem hr22322R_92 : rows2 92 93 ≤ 1437050751127638 := rows2_le_of_rowsJ2 92 93 c22322R_92_0

theorem c22322R_93_5 : rowsJ2 93 94 76 300 ≤ 991483612211286 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22322R_275 rows22322R_276 (by norm_num)

theorem c22322R_93_4 : rowsJ2 93 94 71 300 ≤ 991483612211286 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22322R_274 c22322R_93_5 (by norm_num)

theorem c22322R_93_3 : rowsJ2 93 94 66 300 ≤ 991987733679920 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22322R_273 c22322R_93_4 (by norm_num)

theorem c22322R_93_2 : rowsJ2 93 94 61 300 ≤ 992501694056374 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22322R_272 c22322R_93_3 (by norm_num)

theorem c22322R_93_1 : rowsJ2 93 94 53 300 ≤ 992501694056374 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22322R_271 c22322R_93_2 (by norm_num)

theorem c22322R_93_0 : rowsJ2 93 94 0 300 ≤ 1640462498250852 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22322R_270 c22322R_93_1 (by norm_num)

theorem hr22322R_93 : rows2 93 94 ≤ 1640462498250852 := rows2_le_of_rowsJ2 93 94 c22322R_93_0

theorem c22322R_94_5 : rowsJ2 94 95 76 300 ≤ 1099066952487992 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22322R_282 rows22322R_283 (by norm_num)

theorem c22322R_94_4 : rowsJ2 94 95 71 300 ≤ 1099066952487992 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22322R_281 c22322R_94_5 (by norm_num)

theorem c22322R_94_3 : rowsJ2 94 95 66 300 ≤ 1099226514033927 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22322R_280 c22322R_94_4 (by norm_num)

theorem c22322R_94_2 : rowsJ2 94 95 61 300 ≤ 1099605402819444 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22322R_279 c22322R_94_3 (by norm_num)

theorem c22322R_94_1 : rowsJ2 94 95 53 300 ≤ 1099605402819444 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22322R_278 c22322R_94_2 (by norm_num)

theorem c22322R_94_0 : rowsJ2 94 95 0 300 ≤ 1718837328646270 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22322R_277 c22322R_94_1 (by norm_num)

theorem hr22322R_94 : rows2 94 95 ≤ 1718837328646270 := rows2_le_of_rowsJ2 94 95 c22322R_94_0

theorem c22322R_95_5 : rowsJ2 95 96 77 300 ≤ 1314979687764643 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22322R_289 rows22322R_290 (by norm_num)

theorem c22322R_95_4 : rowsJ2 95 96 71 300 ≤ 1315601912912756 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22322R_288 c22322R_95_5 (by norm_num)

theorem c22322R_95_3 : rowsJ2 95 96 66 300 ≤ 1315624597037149 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22322R_287 c22322R_95_4 (by norm_num)

theorem c22322R_95_2 : rowsJ2 95 96 61 300 ≤ 1315803297175859 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22322R_286 c22322R_95_3 (by norm_num)

theorem c22322R_95_1 : rowsJ2 95 96 53 300 ≤ 1315803297175859 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22322R_285 c22322R_95_2 (by norm_num)

theorem c22322R_95_0 : rowsJ2 95 96 0 300 ≤ 1910060898092567 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22322R_284 c22322R_95_1 (by norm_num)

theorem hr22322R_95 : rows2 95 96 ≤ 1910060898092567 := rows2_le_of_rowsJ2 95 96 c22322R_95_0

theorem c22322R_96_5 : rowsJ2 96 97 76 300 ≤ 1140757289035941 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22322R_296 rows22322R_297 (by norm_num)

theorem c22322R_96_4 : rowsJ2 96 97 70 300 ≤ 1140757289035941 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22322R_295 c22322R_96_5 (by norm_num)

theorem c22322R_96_3 : rowsJ2 96 97 65 300 ≤ 1140757289035941 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22322R_294 c22322R_96_4 (by norm_num)

theorem c22322R_96_2 : rowsJ2 96 97 60 300 ≤ 1140823796603663 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22322R_293 c22322R_96_3 (by norm_num)

theorem c22322R_96_1 : rowsJ2 96 97 53 300 ≤ 1140823796603663 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22322R_292 c22322R_96_2 (by norm_num)

theorem c22322R_96_0 : rowsJ2 96 97 0 300 ≤ 1709274599065389 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22322R_291 c22322R_96_1 (by norm_num)

theorem hr22322R_96 : rows2 96 97 ≤ 1709274599065389 := rows2_le_of_rowsJ2 96 97 c22322R_96_0

theorem c22322R_97_5 : rowsJ2 97 98 76 300 ≤ 1124554180430540 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22322R_303 rows22322R_304 (by norm_num)

theorem c22322R_97_4 : rowsJ2 97 98 70 300 ≤ 1124554180430540 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22322R_302 c22322R_97_5 (by norm_num)

theorem c22322R_97_3 : rowsJ2 97 98 65 300 ≤ 1124554180430540 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22322R_301 c22322R_97_4 (by norm_num)

theorem c22322R_97_2 : rowsJ2 97 98 60 300 ≤ 1124554180430540 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22322R_300 c22322R_97_3 (by norm_num)

theorem c22322R_97_1 : rowsJ2 97 98 53 300 ≤ 1124554180430540 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22322R_299 c22322R_97_2 (by norm_num)

theorem c22322R_97_0 : rowsJ2 97 98 0 300 ≤ 1671004555963155 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22322R_298 c22322R_97_1 (by norm_num)

theorem hr22322R_97 : rows2 97 98 ≤ 1671004555963155 := rows2_le_of_rowsJ2 97 98 c22322R_97_0

theorem c22322R_98_5 : rowsJ2 98 99 76 300 ≤ 996675621770465 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22322R_310 rows22322R_311 (by norm_num)

theorem c22322R_98_4 : rowsJ2 98 99 70 300 ≤ 996675621770465 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22322R_309 c22322R_98_5 (by norm_num)

theorem c22322R_98_3 : rowsJ2 98 99 65 300 ≤ 996675621770465 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22322R_308 c22322R_98_4 (by norm_num)

theorem c22322R_98_2 : rowsJ2 98 99 60 300 ≤ 996675621770465 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22322R_307 c22322R_98_3 (by norm_num)

theorem c22322R_98_1 : rowsJ2 98 99 53 300 ≤ 997059668166287 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22322R_306 c22322R_98_2 (by norm_num)

theorem c22322R_98_0 : rowsJ2 98 99 0 300 ≤ 1520120508837383 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22322R_305 c22322R_98_1 (by norm_num)

theorem hr22322R_98 : rows2 98 99 ≤ 1520120508837383 := rows2_le_of_rowsJ2 98 99 c22322R_98_0

theorem c22322R_99_5 : rowsJ2 99 100 76 300 ≤ 981737929691870 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22322R_317 rows22322R_318 (by norm_num)

theorem c22322R_99_4 : rowsJ2 99 100 70 300 ≤ 981737929691870 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22322R_316 c22322R_99_5 (by norm_num)

theorem c22322R_99_3 : rowsJ2 99 100 65 300 ≤ 981737929691870 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22322R_315 c22322R_99_4 (by norm_num)

theorem c22322R_99_2 : rowsJ2 99 100 60 300 ≤ 981737929691870 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22322R_314 c22322R_99_3 (by norm_num)

theorem c22322R_99_1 : rowsJ2 99 100 53 300 ≤ 982941872056726 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22322R_313 c22322R_99_2 (by norm_num)

theorem c22322R_99_0 : rowsJ2 99 100 0 300 ≤ 1486040374018360 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22322R_312 c22322R_99_1 (by norm_num)

theorem hr22322R_99 : rows2 99 100 ≤ 1486040374018360 := rows2_le_of_rowsJ2 99 100 c22322R_99_0

theorem c22322R_100_4 : rowsJ2 100 101 70 300 ≤ 857076120945029 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22322R_323 rows22322R_324 (by norm_num)

theorem c22322R_100_3 : rowsJ2 100 101 65 300 ≤ 857076120945029 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22322R_322 c22322R_100_4 (by norm_num)

theorem c22322R_100_2 : rowsJ2 100 101 60 300 ≤ 857076120945029 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22322R_321 c22322R_100_3 (by norm_num)

theorem c22322R_100_1 : rowsJ2 100 101 53 300 ≤ 859713248675870 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22322R_320 c22322R_100_2 (by norm_num)

theorem c22322R_100_0 : rowsJ2 100 101 0 300 ≤ 1341471893262261 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22322R_319 c22322R_100_1 (by norm_num)

theorem hr22322R_100 : rows2 100 101 ≤ 1341471893262261 := rows2_le_of_rowsJ2 100 101 c22322R_100_0

theorem c22322R_101_4 : rowsJ2 101 102 69 300 ≤ 843432764752341 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22322R_329 rows22322R_330 (by norm_num)

theorem c22322R_101_3 : rowsJ2 101 102 64 300 ≤ 843432764752341 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22322R_328 c22322R_101_4 (by norm_num)

theorem c22322R_101_2 : rowsJ2 101 102 59 300 ≤ 843432764752341 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22322R_327 c22322R_101_3 (by norm_num)

theorem c22322R_101_1 : rowsJ2 101 102 53 300 ≤ 848092300608640 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22322R_326 c22322R_101_2 (by norm_num)

theorem c22322R_101_0 : rowsJ2 101 102 0 300 ≤ 1311403616223379 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22322R_325 c22322R_101_1 (by norm_num)

theorem hr22322R_101 : rows2 101 102 ≤ 1311403616223379 := rows2_le_of_rowsJ2 101 102 c22322R_101_0

theorem c22322R_102_4 : rowsJ2 102 103 70 300 ≤ 721837089519722 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22322R_335 rows22322R_336 (by norm_num)

theorem c22322R_102_3 : rowsJ2 102 103 64 300 ≤ 721837089519722 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22322R_334 c22322R_102_4 (by norm_num)

theorem c22322R_102_2 : rowsJ2 102 103 59 300 ≤ 721837089519722 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22322R_333 c22322R_102_3 (by norm_num)

theorem c22322R_102_1 : rowsJ2 102 103 53 300 ≤ 729376446150802 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22322R_332 c22322R_102_2 (by norm_num)

theorem c22322R_102_0 : rowsJ2 102 103 0 300 ≤ 1172872971835455 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22322R_331 c22322R_102_1 (by norm_num)

theorem hr22322R_102 : rows2 102 103 ≤ 1172872971835455 := rows2_le_of_rowsJ2 102 103 c22322R_102_0

theorem c22322R_103_4 : rowsJ2 103 104 70 300 ≤ 709534091210865 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22322R_341 rows22322R_342 (by norm_num)

theorem c22322R_103_3 : rowsJ2 103 104 64 300 ≤ 709534091210865 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22322R_340 c22322R_103_4 (by norm_num)

theorem c22322R_103_2 : rowsJ2 103 104 59 300 ≤ 709534091210865 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22322R_339 c22322R_103_3 (by norm_num)

theorem c22322R_103_1 : rowsJ2 103 104 52 300 ≤ 723358296360639 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22322R_338 c22322R_103_2 (by norm_num)

theorem c22322R_103_0 : rowsJ2 103 104 0 300 ≤ 1147174220238683 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22322R_337 c22322R_103_1 (by norm_num)

theorem hr22322R_103 : rows2 103 104 ≤ 1147174220238683 := rows2_le_of_rowsJ2 103 104 c22322R_103_0

theorem c22322R_104_4 : rowsJ2 104 105 69 300 ≤ 590953627427305 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22322R_347 rows22322R_348 (by norm_num)

theorem c22322R_104_3 : rowsJ2 104 105 63 300 ≤ 590953627427305 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22322R_346 c22322R_104_4 (by norm_num)

theorem c22322R_104_2 : rowsJ2 104 105 58 300 ≤ 593278184416555 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22322R_345 c22322R_104_3 (by norm_num)

theorem c22322R_104_1 : rowsJ2 104 105 52 300 ≤ 610028414276142 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22322R_344 c22322R_104_2 (by norm_num)

theorem c22322R_104_0 : rowsJ2 104 105 0 300 ≤ 1015211232825491 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22322R_343 c22322R_104_1 (by norm_num)

theorem hr22322R_104 : rows2 104 105 ≤ 1015211232825491 := rows2_le_of_rowsJ2 104 105 c22322R_104_0

theorem c22322R_105_4 : rowsJ2 105 106 69 300 ≤ 580056020214095 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22322R_353 rows22322R_354 (by norm_num)

theorem c22322R_105_3 : rowsJ2 105 106 63 300 ≤ 580056020214095 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22322R_352 c22322R_105_4 (by norm_num)

theorem c22322R_105_2 : rowsJ2 105 106 58 300 ≤ 584621713841917 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22322R_351 c22322R_105_3 (by norm_num)

theorem c22322R_105_1 : rowsJ2 105 106 52 300 ≤ 605067311088857 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22322R_350 c22322R_105_2 (by norm_num)

theorem c22322R_105_0 : rowsJ2 105 106 0 300 ≤ 994278140691535 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22322R_349 c22322R_105_1 (by norm_num)

theorem hr22322R_105 : rows2 105 106 ≤ 994278140691535 := rows2_le_of_rowsJ2 105 106 c22322R_105_0

theorem c22322R_106_4 : rowsJ2 106 107 69 300 ≤ 464360489302848 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22322R_359 rows22322R_360 (by norm_num)

theorem c22322R_106_3 : rowsJ2 106 107 63 300 ≤ 464360489302848 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22322R_358 c22322R_106_4 (by norm_num)

theorem c22322R_106_2 : rowsJ2 106 107 58 300 ≤ 471787029721968 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22322R_357 c22322R_106_3 (by norm_num)

theorem c22322R_106_1 : rowsJ2 106 107 52 300 ≤ 496235186239520 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22322R_356 c22322R_106_2 (by norm_num)

theorem c22322R_106_0 : rowsJ2 106 107 0 300 ≤ 868338354415827 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22322R_355 c22322R_106_1 (by norm_num)

theorem hr22322R_106 : rows2 106 107 ≤ 868338354415827 := rows2_le_of_rowsJ2 106 107 c22322R_106_0

theorem c22322R_107_4 : rowsJ2 107 108 69 300 ≤ 454954431026837 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22322R_365 rows22322R_366 (by norm_num)

theorem c22322R_107_3 : rowsJ2 107 108 63 300 ≤ 454954431026837 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22322R_364 c22322R_107_4 (by norm_num)

theorem c22322R_107_2 : rowsJ2 107 108 58 300 ≤ 465293676069380 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22322R_363 c22322R_107_3 (by norm_num)

theorem c22322R_107_1 : rowsJ2 107 108 52 300 ≤ 493796467519161 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22322R_362 c22322R_107_2 (by norm_num)

theorem c22322R_107_0 : rowsJ2 107 108 0 300 ≤ 851592134155037 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22322R_361 c22322R_107_1 (by norm_num)

theorem hr22322R_107 : rows2 107 108 ≤ 851592134155037 := rows2_le_of_rowsJ2 107 108 c22322R_107_0

theorem c22322R_108_4 : rowsJ2 108 109 68 300 ≤ 342118393159482 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22322R_371 rows22322R_372 (by norm_num)

theorem c22322R_108_3 : rowsJ2 108 109 62 300 ≤ 343755310558453 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22322R_370 c22322R_108_4 (by norm_num)

theorem c22322R_108_2 : rowsJ2 108 109 57 300 ≤ 360891959615427 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22322R_369 c22322R_108_3 (by norm_num)

theorem c22322R_108_1 : rowsJ2 108 109 51 300 ≤ 393605108403188 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22322R_368 c22322R_108_2 (by norm_num)

theorem c22322R_108_0 : rowsJ2 108 109 0 300 ≤ 730906093617506 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22322R_367 c22322R_108_1 (by norm_num)

theorem hr22322R_108 : rows2 108 109 ≤ 730906093617506 := rows2_le_of_rowsJ2 108 109 c22322R_108_0

theorem c22322R_109_3 : rowsJ2 109 110 63 300 ≤ 335718070969694 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22322R_376 rows22322R_377 (by norm_num)

theorem c22322R_109_2 : rowsJ2 109 110 57 300 ≤ 356624877032195 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22322R_375 c22322R_109_3 (by norm_num)

theorem c22322R_109_1 : rowsJ2 109 110 51 300 ≤ 393482776678168 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22322R_374 c22322R_109_2 (by norm_num)

theorem c22322R_109_0 : rowsJ2 109 110 0 300 ≤ 717472561169593 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22322R_373 c22322R_109_1 (by norm_num)

theorem hr22322R_109 : rows2 109 110 ≤ 717472561169593 := rows2_le_of_rowsJ2 109 110 c22322R_109_0

theorem c22322R_110_3 : rowsJ2 110 111 63 300 ≤ 226807153896054 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22322R_381 rows22322R_382 (by norm_num)

theorem c22322R_110_2 : rowsJ2 110 111 57 300 ≤ 250095519152964 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22322R_380 c22322R_110_3 (by norm_num)

theorem c22322R_110_1 : rowsJ2 110 111 51 300 ≤ 291432489501552 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22322R_379 c22322R_110_2 (by norm_num)

theorem c22322R_110_0 : rowsJ2 110 111 0 300 ≤ 601245861456422 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22322R_378 c22322R_110_1 (by norm_num)

theorem hr22322R_110 : rows2 110 111 ≤ 601245861456422 := rows2_le_of_rowsJ2 110 111 c22322R_110_0

theorem c22322R_111_3 : rowsJ2 111 112 63 300 ≤ 222895898096230 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22322R_386 rows22322R_387 (by norm_num)

theorem c22322R_111_2 : rowsJ2 111 112 57 300 ≤ 248033127388700 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22322R_385 c22322R_111_3 (by norm_num)

theorem c22322R_111_1 : rowsJ2 111 112 51 300 ≤ 293346016958498 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22322R_384 c22322R_111_2 (by norm_num)

theorem c22322R_111_0 : rowsJ2 111 112 0 300 ≤ 591527044467077 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22322R_383 c22322R_111_1 (by norm_num)

theorem hr22322R_111 : rows2 111 112 ≤ 591527044467077 := rows2_le_of_rowsJ2 111 112 c22322R_111_0

theorem c22322R_112_3 : rowsJ2 112 113 62 300 ≤ 119084396231878 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22322R_391 rows22322R_392 (by norm_num)

theorem c22322R_112_2 : rowsJ2 112 113 56 300 ≤ 151039197026427 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22322R_390 c22322R_112_3 (by norm_num)

theorem c22322R_112_1 : rowsJ2 112 113 50 300 ≤ 199846259677994 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22322R_389 c22322R_112_2 (by norm_num)

theorem c22322R_112_0 : rowsJ2 112 113 0 300 ≤ 478554440342262 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22322R_388 c22322R_112_1 (by norm_num)

theorem hr22322R_112 : rows2 112 113 ≤ 478554440342262 := rows2_le_of_rowsJ2 112 113 c22322R_112_0

theorem c22322R_113_3 : rowsJ2 113 114 62 300 ≤ 117211727408563 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22322R_396 rows22322R_397 (by norm_num)

theorem c22322R_113_2 : rowsJ2 113 114 56 300 ≤ 150233332034721 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22322R_395 c22322R_113_3 (by norm_num)

theorem c22322R_113_1 : rowsJ2 113 114 50 300 ≤ 202988255253662 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22322R_394 c22322R_113_2 (by norm_num)

theorem c22322R_113_0 : rowsJ2 113 114 0 300 ≤ 471278186518082 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22322R_393 c22322R_113_1 (by norm_num)

theorem hr22322R_113 : rows2 113 114 ≤ 471278186518082 := rows2_le_of_rowsJ2 113 114 c22322R_113_0

theorem c22322R_114_3 : rowsJ2 114 115 62 300 ≤ 11565110181868 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22322R_401 rows22322R_402 (by norm_num)

theorem c22322R_114_2 : rowsJ2 114 115 56 300 ≤ 45402837705844 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22322R_400 c22322R_114_3 (by norm_num)

theorem c22322R_114_1 : rowsJ2 114 115 50 300 ≤ 102367602707215 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22322R_399 c22322R_114_2 (by norm_num)

theorem c22322R_114_0 : rowsJ2 114 115 0 300 ≤ 359393030678076 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22322R_398 c22322R_114_1 (by norm_num)

theorem hr22322R_114 : rows2 114 115 ≤ 359393030678076 := rows2_le_of_rowsJ2 114 115 c22322R_114_0

theorem c22322R_115_3 : rowsJ2 115 116 61 300 ≤ 13739340072821 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22322R_406 rows22322R_407 (by norm_num)

theorem c22322R_115_2 : rowsJ2 115 116 55 300 ≤ 53629439242996 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22322R_405 c22322R_115_3 (by norm_num)

theorem c22322R_115_1 : rowsJ2 115 116 49 300 ≤ 112901658126699 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22322R_404 c22322R_115_2 (by norm_num)

theorem c22322R_115_0 : rowsJ2 115 116 0 300 ≤ 352921374304392 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22322R_403 c22322R_115_1 (by norm_num)

theorem hr22322R_115 : rows2 115 116 ≤ 352921374304392 := rows2_le_of_rowsJ2 115 116 c22322R_115_0

theorem c22322R_116_3 : rowsJ2 116 117 62 300 ≤ 10218270292572 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22322R_411 rows22322R_412 (by norm_num)

theorem c22322R_116_2 : rowsJ2 116 117 55 300 ≤ 53721999809395 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22322R_410 c22322R_116_3 (by norm_num)

theorem c22322R_116_1 : rowsJ2 116 117 49 300 ≤ 117207553422486 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22322R_409 c22322R_116_2 (by norm_num)

theorem c22322R_116_0 : rowsJ2 116 117 0 300 ≤ 347277780495382 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22322R_408 c22322R_116_1 (by norm_num)

theorem hr22322R_116 : rows2 116 117 ≤ 347277780495382 := rows2_le_of_rowsJ2 116 117 c22322R_116_0

theorem c22322R_117_3 : rowsJ2 117 118 62 300 ≤ 9523335534066 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22322R_416 rows22322R_417 (by norm_num)

theorem c22322R_117_2 : rowsJ2 117 118 55 300 ≤ 52495809021689 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22322R_415 c22322R_117_3 (by norm_num)

theorem c22322R_117_1 : rowsJ2 117 118 49 300 ≤ 119150337312892 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22322R_414 c22322R_117_2 (by norm_num)

theorem c22322R_117_0 : rowsJ2 117 118 0 300 ≤ 341666540106828 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22322R_413 c22322R_117_1 (by norm_num)

theorem hr22322R_117 : rows2 117 118 ≤ 341666540106828 := rows2_le_of_rowsJ2 117 118 c22322R_117_0

theorem c22322R_118_3 : rowsJ2 118 119 62 300 ≤ 110158411337305 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22322R_421 rows22322R_422 (by norm_num)

theorem c22322R_118_2 : rowsJ2 118 119 55 300 ≤ 152333460599555 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22322R_420 c22322R_118_3 (by norm_num)

theorem c22322R_118_1 : rowsJ2 118 119 49 300 ≤ 222347470131196 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22322R_419 c22322R_118_2 (by norm_num)

theorem c22322R_118_0 : rowsJ2 118 119 0 300 ≤ 436805196817221 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22322R_418 c22322R_118_1 (by norm_num)

theorem hr22322R_118 : rows2 118 119 ≤ 436805196817221 := rows2_le_of_rowsJ2 118 119 c22322R_118_0

theorem c22322R_119_2 : rowsJ2 119 120 55 300 ≤ 349966250176093 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22322R_425 rows22322R_426 (by norm_num)

theorem c22322R_119_1 : rowsJ2 119 120 48 300 ≤ 432346800303277 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22322R_424 c22322R_119_2 (by norm_num)

theorem c22322R_119_0 : rowsJ2 119 120 0 300 ≤ 631007326862704 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22322R_423 c22322R_119_1 (by norm_num)

theorem hr22322R_119 : rows2 119 120 ≤ 631007326862704 := rows2_le_of_rowsJ2 119 120 c22322R_119_0

theorem c22322R_120_2 : rowsJ2 120 121 55 300 ≤ 543365993315369 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22322R_429 rows22322R_430 (by norm_num)

theorem c22322R_120_1 : rowsJ2 120 121 48 300 ≤ 628761132140582 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22322R_428 c22322R_120_2 (by norm_num)

theorem c22322R_120_0 : rowsJ2 120 121 0 300 ≤ 820637069092302 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22322R_427 c22322R_120_1 (by norm_num)

theorem hr22322R_120 : rows2 120 121 ≤ 820637069092302 := rows2_le_of_rowsJ2 120 121 c22322R_120_0

theorem c22322R_121_2 : rowsJ2 121 122 55 300 ≤ 732065194980355 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22322R_433 rows22322R_434 (by norm_num)

theorem c22322R_121_1 : rowsJ2 121 122 48 300 ≤ 818943377874343 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22322R_432 c22322R_121_2 (by norm_num)

theorem c22322R_121_0 : rowsJ2 121 122 0 300 ≤ 1006425045949707 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22322R_431 c22322R_121_1 (by norm_num)

theorem hr22322R_121 : rows2 121 122 ≤ 1006425045949707 := rows2_le_of_rowsJ2 121 122 c22322R_121_0

theorem c22322R_122_2 : rowsJ2 122 123 54 300 ≤ 926278950327963 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22322R_437 rows22322R_438 (by norm_num)

theorem c22322R_122_1 : rowsJ2 122 123 47 300 ≤ 1017004789121568 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22322R_436 c22322R_122_2 (by norm_num)

theorem c22322R_122_0 : rowsJ2 122 123 0 300 ≤ 1188408045505625 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22322R_435 c22322R_122_1 (by norm_num)

theorem hr22322R_122 : rows2 122 123 ≤ 1188408045505625 := rows2_le_of_rowsJ2 122 123 c22322R_122_0

theorem c22322R_123_2 : rowsJ2 123 124 54 300 ≤ 1106520876180652 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22322R_441 rows22322R_442 (by norm_num)

theorem c22322R_123_1 : rowsJ2 123 124 47 300 ≤ 1198357010934634 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22322R_440 c22322R_123_2 (by norm_num)

theorem c22322R_123_0 : rowsJ2 123 124 0 300 ≤ 1366589701048778 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22322R_439 c22322R_123_1 (by norm_num)

theorem hr22322R_123 : rows2 123 124 ≤ 1366589701048778 := rows2_le_of_rowsJ2 123 124 c22322R_123_0

theorem c22322R_124_2 : rowsJ2 124 125 54 300 ≤ 1283371905093157 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22322R_445 rows22322R_446 (by norm_num)

theorem c22322R_124_1 : rowsJ2 124 125 47 300 ≤ 1376415546387616 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22322R_444 c22322R_124_2 (by norm_num)

theorem c22322R_124_0 : rowsJ2 124 125 0 300 ≤ 1541383959349535 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22322R_443 c22322R_124_1 (by norm_num)

theorem hr22322R_124 : rows2 124 125 ≤ 1541383959349535 := rows2_le_of_rowsJ2 124 125 c22322R_124_0

theorem c22322R_125_2 : rowsJ2 125 126 53 300 ≤ 1465562015406183 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22322R_449 rows22322R_450 (by norm_num)

theorem c22322R_125_1 : rowsJ2 125 126 46 300 ≤ 1561586757139885 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22322R_448 c22322R_125_2 (by norm_num)

theorem c22322R_125_0 : rowsJ2 125 126 0 300 ≤ 1712737431210256 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22322R_447 c22322R_125_1 (by norm_num)

theorem hr22322R_125 : rows2 125 126 ≤ 1712737431210256 := rows2_le_of_rowsJ2 125 126 c22322R_125_0

theorem c22322R_126_2 : rowsJ2 126 127 53 300 ≤ 1634878930772182 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22322R_453 rows22322R_454 (by norm_num)

theorem c22322R_126_1 : rowsJ2 126 127 46 300 ≤ 1731799733960719 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22322R_452 c22322R_126_2 (by norm_num)

theorem c22322R_126_0 : rowsJ2 126 127 0 300 ≤ 1881056018342284 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22322R_451 c22322R_126_1 (by norm_num)

theorem hr22322R_126 : rows2 126 127 ≤ 1881056018342284 := rows2_le_of_rowsJ2 126 127 c22322R_126_0

theorem c22322R_127_2 : rowsJ2 127 128 53 300 ≤ 1791469769844069 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22322R_457 rows22322R_458 (by norm_num)

theorem c22322R_127_1 : rowsJ2 127 128 46 300 ≤ 1887342934917080 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22322R_456 c22322R_127_2 (by norm_num)

theorem c22322R_127_0 : rowsJ2 127 128 0 300 ≤ 2036882956279276 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22322R_455 c22322R_127_1 (by norm_num)

theorem hr22322R_127 : rows2 127 128 ≤ 2036882956279276 := rows2_le_of_rowsJ2 127 128 c22322R_127_0

theorem c22322R_128_1 : rowsJ2 128 129 45 300 ≤ 2055960674493049 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22322R_460 rows22322R_461 (by norm_num)

theorem c22322R_128_0 : rowsJ2 128 129 0 300 ≤ 2191628929742197 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22322R_459 c22322R_128_1 (by norm_num)

theorem hr22322R_128 : rows2 128 129 ≤ 2191628929742197 := rows2_le_of_rowsJ2 128 129 c22322R_128_0

theorem c22322R_129_1 : rowsJ2 129 130 45 300 ≤ 2197668709417761 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22322R_463 rows22322R_464 (by norm_num)

theorem c22322R_129_0 : rowsJ2 129 130 0 300 ≤ 2334917875684346 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22322R_462 c22322R_129_1 (by norm_num)

theorem hr22322R_129 : rows2 129 130 ≤ 2334917875684346 := rows2_le_of_rowsJ2 129 130 c22322R_129_0

theorem c22322R_130_1 : rowsJ2 130 131 45 300 ≤ 2347565118422476 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22322R_466 rows22322R_467 (by norm_num)

theorem c22322R_130_0 : rowsJ2 130 131 0 300 ≤ 2486667785227482 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22322R_465 c22322R_130_1 (by norm_num)

theorem hr22322R_130 : rows2 130 131 ≤ 2486667785227482 := rows2_le_of_rowsJ2 130 131 c22322R_130_0

theorem c22322R_131_1 : rowsJ2 131 132 44 300 ≤ 2509331040765169 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22322R_469 rows22322R_470 (by norm_num)

theorem c22322R_131_0 : rowsJ2 131 132 0 300 ≤ 2636343017410999 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22322R_468 c22322R_131_1 (by norm_num)

theorem hr22322R_131 : rows2 131 132 ≤ 2636343017410999 := rows2_le_of_rowsJ2 131 132 c22322R_131_0

theorem c22322R_132_1 : rowsJ2 132 133 44 300 ≤ 2645574550400782 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22322R_472 rows22322R_473 (by norm_num)

theorem c22322R_132_0 : rowsJ2 132 133 0 300 ≤ 2775831829970022 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22322R_471 c22322R_132_1 (by norm_num)

theorem hr22322R_132 : rows2 132 133 ≤ 2775831829970022 := rows2_le_of_rowsJ2 132 133 c22322R_132_0

theorem c22322R_133_1 : rowsJ2 133 134 44 300 ≤ 2786957024147816 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22322R_475 rows22322R_476 (by norm_num)

theorem c22322R_133_0 : rowsJ2 133 134 0 300 ≤ 2922422151410698 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22322R_474 c22322R_133_1 (by norm_num)

theorem hr22322R_133 : rows2 133 134 ≤ 2922422151410698 := rows2_le_of_rowsJ2 133 134 c22322R_133_0

theorem c22322R_134_1 : rowsJ2 134 135 43 300 ≤ 2945035055903930 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22322R_478 rows22322R_479 (by norm_num)

theorem c22322R_134_0 : rowsJ2 134 135 0 300 ≤ 3068412238002186 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22322R_477 c22322R_134_1 (by norm_num)

theorem hr22322R_134 : rows2 134 135 ≤ 3068412238002186 := rows2_le_of_rowsJ2 134 135 c22322R_134_0

theorem c22322R_135_1 : rowsJ2 135 136 43 300 ≤ 3000312012032774 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22322R_481 rows22322R_482 (by norm_num)

theorem c22322R_135_0 : rowsJ2 135 136 0 300 ≤ 3130169335307764 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22322R_480 c22322R_135_1 (by norm_num)

theorem hr22322R_135 : rows2 135 136 ≤ 3130169335307764 := rows2_le_of_rowsJ2 135 136 c22322R_135_0

theorem c22322R_136_1 : rowsJ2 136 137 43 300 ≤ 2991676235710142 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22322R_484 rows22322R_485 (by norm_num)

theorem c22322R_136_0 : rowsJ2 136 137 0 300 ≤ 3128749637987079 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22322R_483 c22322R_136_1 (by norm_num)

theorem hr22322R_136 : rows2 136 137 ≤ 3128749637987079 := rows2_le_of_rowsJ2 136 137 c22322R_136_0

theorem c22322R_137_1 : rowsJ2 137 138 42 300 ≤ 3001213213816008 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22322R_487 rows22322R_488 (by norm_num)

theorem c22322R_137_0 : rowsJ2 137 138 0 300 ≤ 3127290578582270 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22322R_486 c22322R_137_1 (by norm_num)

theorem hr22322R_137 : rows2 137 138 ≤ 3127290578582270 := rows2_le_of_rowsJ2 137 138 c22322R_137_0

theorem c22322R_138_1 : rowsJ2 138 139 42 300 ≤ 2983922193576310 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22322R_490 rows22322R_491 (by norm_num)

theorem c22322R_138_0 : rowsJ2 138 139 0 300 ≤ 3118592724350856 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22322R_489 c22322R_138_1 (by norm_num)

theorem hr22322R_138 : rows2 138 139 ≤ 3118592724350856 := rows2_le_of_rowsJ2 138 139 c22322R_138_0

theorem c22322R_139_0 : rowsJ2 139 140 0 300 ≤ 3118776630690840 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22322R_492 rows22322R_493 (by norm_num)

theorem hr22322R_139 : rows2 139 140 ≤ 3118776630690840 := rows2_le_of_rowsJ2 139 140 c22322R_139_0

theorem c22322R_140_0 : rowsJ2 140 141 0 300 ≤ 3121197696350101 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22322R_494 rows22322R_495 (by norm_num)

theorem hr22322R_140 : rows2 140 141 ≤ 3121197696350101 := rows2_le_of_rowsJ2 140 141 c22322R_140_0

theorem c22322R_141_0 : rowsJ2 141 142 0 300 ≤ 3113697640803303 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22322R_496 rows22322R_497 (by norm_num)

theorem hr22322R_141 : rows2 141 142 ≤ 3113697640803303 := rows2_le_of_rowsJ2 141 142 c22322R_141_0

theorem c22322R_142_0 : rowsJ2 142 143 0 300 ≤ 3119520398799027 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22322R_498 rows22322R_499 (by norm_num)

theorem hr22322R_142 : rows2 142 143 ≤ 3119520398799027 := rows2_le_of_rowsJ2 142 143 c22322R_142_0

theorem c22322R_143_0 : rowsJ2 143 144 0 300 ≤ 3126332862047020 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22322R_500 rows22322R_501 (by norm_num)

theorem hr22322R_143 : rows2 143 144 ≤ 3126332862047020 := rows2_le_of_rowsJ2 143 144 c22322R_143_0

theorem c22322R_144_0 : rowsJ2 144 145 0 300 ≤ 3128136188541957 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22322R_502 rows22322R_503 (by norm_num)

theorem hr22322R_144 : rows2 144 145 ≤ 3128136188541957 := rows2_le_of_rowsJ2 144 145 c22322R_144_0

theorem c22322R_145_0 : rowsJ2 145 146 0 300 ≤ 3139633451404459 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22322R_504 rows22322R_505 (by norm_num)

theorem hr22322R_145 : rows2 145 146 ≤ 3139633451404459 := rows2_le_of_rowsJ2 145 146 c22322R_145_0

theorem c22322R_146_0 : rowsJ2 146 147 0 300 ≤ 3154995558814945 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22322R_506 rows22322R_507 (by norm_num)

theorem hr22322R_146 : rows2 146 147 ≤ 3154995558814945 := rows2_le_of_rowsJ2 146 147 c22322R_146_0

theorem c22322R_147_0 : rowsJ2 147 148 0 300 ≤ 3161269598890456 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22322R_508 rows22322R_509 (by norm_num)

theorem hr22322R_147 : rows2 147 148 ≤ 3161269598890456 := rows2_le_of_rowsJ2 147 148 c22322R_147_0

theorem c22322R_148_0 : rowsJ2 148 149 0 300 ≤ 3180492167129559 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22322R_510 rows22322R_511 (by norm_num)

theorem hr22322R_148 : rows2 148 149 ≤ 3180492167129559 := rows2_le_of_rowsJ2 148 149 c22322R_148_0

theorem c22322R_149_0 : rowsJ2 149 150 0 300 ≤ 3199429428980630 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22322R_512 rows22322R_513 (by norm_num)

theorem hr22322R_149 : rows2 149 150 ≤ 3199429428980630 := rows2_le_of_rowsJ2 149 150 c22322R_149_0

theorem c22322R_150_0 : rowsJ2 150 151 0 300 ≤ 3213077196141746 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22322R_514 rows22322R_515 (by norm_num)

theorem hr22322R_150 : rows2 150 151 ≤ 3213077196141746 := rows2_le_of_rowsJ2 150 151 c22322R_150_0

theorem c22322R_151_0 : rowsJ2 151 152 0 300 ≤ 3234577176295569 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22322R_516 rows22322R_517 (by norm_num)

theorem hr22322R_151 : rows2 151 152 ≤ 3234577176295569 := rows2_le_of_rowsJ2 151 152 c22322R_151_0

theorem c22322R_152_0 : rowsJ2 152 153 0 300 ≤ 3249458423683783 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22322R_518 rows22322R_519 (by norm_num)

theorem hr22322R_152 : rows2 152 153 ≤ 3249458423683783 := rows2_le_of_rowsJ2 152 153 c22322R_152_0

theorem c22322R_153_0 : rowsJ2 153 154 0 300 ≤ 3263519032088276 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22322R_520 rows22322R_521 (by norm_num)

theorem hr22322R_153 : rows2 153 154 ≤ 3263519032088276 := rows2_le_of_rowsJ2 153 154 c22322R_153_0

theorem t22322R_168 : rows2 293 300 ≤ 98005768773284498 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_559 rows22322R_560 (by norm_num)

theorem t22322R_167 : rows2 289 300 ≤ 148664933009239619 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_558 t22322R_168 (by norm_num)

theorem t22322R_166 : rows2 284 300 ≤ 207323868373592234 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_557 t22322R_167 (by norm_num)

theorem t22322R_165 : rows2 234 300 ≤ 249800870869766010 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_556 t22322R_166 (by norm_num)

theorem t22322R_164 : rows2 230 300 ≤ 291888873695834886 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_555 t22322R_165 (by norm_num)

theorem t22322R_163 : rows2 227 300 ≤ 323262773848521775 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_554 t22322R_164 (by norm_num)

theorem t22322R_162 : rows2 224 300 ≤ 354198182046861284 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_553 t22322R_163 (by norm_num)

theorem t22322R_161 : rows2 221 300 ≤ 385050947666763082 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_552 t22322R_162 (by norm_num)

theorem t22322R_160 : rows2 218 300 ≤ 415462324189333898 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_551 t22322R_161 (by norm_num)

theorem t22322R_159 : rows2 215 300 ≤ 445790480251112742 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_550 t22322R_160 (by norm_num)

theorem t22322R_158 : rows2 212 300 ≤ 475726255283038526 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_549 t22322R_159 (by norm_num)

theorem t22322R_157 : rows2 209 300 ≤ 505587079029247411 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_548 t22322R_158 (by norm_num)

theorem t22322R_156 : rows2 206 300 ≤ 535045485179419205 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_547 t22322R_157 (by norm_num)

theorem t22322R_155 : rows2 203 300 ≤ 564170967733756724 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_546 t22322R_156 (by norm_num)

theorem t22322R_154 : rows2 200 300 ≤ 591990085325166402 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_545 t22322R_155 (by norm_num)

theorem t22322R_153 : rows2 197 300 ≤ 618656684281426965 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_544 t22322R_154 (by norm_num)

theorem t22322R_152 : rows2 194 300 ≤ 644198409696797889 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_543 t22322R_153 (by norm_num)

theorem t22322R_151 : rows2 191 300 ≤ 668797490996438900 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_542 t22322R_152 (by norm_num)

theorem t22322R_150 : rows2 188 300 ≤ 692503009999152743 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_541 t22322R_151 (by norm_num)

theorem t22322R_149 : rows2 184 300 ≤ 722974921515474130 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_540 t22322R_150 (by norm_num)

theorem t22322R_148 : rows2 180 300 ≤ 751290998339923805 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_539 t22322R_149 (by norm_num)

theorem t22322R_147 : rows2 177 300 ≤ 770882638444173186 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_538 t22322R_148 (by norm_num)

theorem t22322R_146 : rows2 174 300 ≤ 789107867584162160 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_537 t22322R_147 (by norm_num)

theorem t22322R_145 : rows2 171 300 ≤ 805990152781408296 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_536 t22322R_146 (by norm_num)

theorem t22322R_144 : rows2 169 300 ≤ 816498579716496010 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_535 t22322R_145 (by norm_num)

theorem t22322R_143 : rows2 167 300 ≤ 826409906801342574 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_534 t22322R_144 (by norm_num)

theorem t22322R_142 : rows2 165 300 ≤ 835725433300542036 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_533 t22322R_143 (by norm_num)

theorem t22322R_141 : rows2 164 300 ≤ 840160417007093227 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_532 t22322R_142 (by norm_num)

theorem t22322R_140 : rows2 163 300 ≤ 844447372389016896 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_531 t22322R_141 (by norm_num)

theorem t22322R_139 : rows2 162 300 ≤ 848586708716606347 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_530 t22322R_140 (by norm_num)

theorem t22322R_138 : rows2 161 300 ≤ 852578842260550985 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_529 t22322R_139 (by norm_num)

theorem t22322R_137 : rows2 160 300 ≤ 856424131963206109 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_528 t22322R_138 (by norm_num)

theorem t22322R_136 : rows2 159 300 ≤ 860122940968467214 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_527 t22322R_137 (by norm_num)

theorem t22322R_135 : rows2 158 300 ≤ 863673310068269902 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_526 t22322R_136 (by norm_num)

theorem t22322R_134 : rows2 157 300 ≤ 867070035187716332 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_525 t22322R_135 (by norm_num)

theorem t22322R_133 : rows2 156 300 ≤ 870382311180611488 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_524 t22322R_134 (by norm_num)

theorem t22322R_132 : rows2 155 300 ≤ 873676977944884240 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_523 t22322R_133 (by norm_num)

theorem t22322R_131 : rows2 154 300 ≤ 876956606965609558 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_522 t22322R_132 (by norm_num)

theorem t22322R_130 : rows2 153 300 ≤ 880220125997697834 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_153 t22322R_131 (by norm_num)

theorem t22322R_129 : rows2 152 300 ≤ 883469584421381617 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_152 t22322R_130 (by norm_num)

theorem t22322R_128 : rows2 151 300 ≤ 886704161597677186 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_151 t22322R_129 (by norm_num)

theorem t22322R_127 : rows2 150 300 ≤ 889917238793818932 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_150 t22322R_128 (by norm_num)

theorem t22322R_126 : rows2 149 300 ≤ 893116668222799562 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_149 t22322R_127 (by norm_num)

theorem t22322R_125 : rows2 148 300 ≤ 896297160389929121 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_148 t22322R_126 (by norm_num)

theorem t22322R_124 : rows2 147 300 ≤ 899458429988819577 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_147 t22322R_125 (by norm_num)

theorem t22322R_123 : rows2 146 300 ≤ 902613425547634522 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_146 t22322R_124 (by norm_num)

theorem t22322R_122 : rows2 145 300 ≤ 905753058999038981 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_145 t22322R_123 (by norm_num)

theorem t22322R_121 : rows2 144 300 ≤ 908881195187580938 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_144 t22322R_122 (by norm_num)

theorem t22322R_120 : rows2 143 300 ≤ 912007528049627958 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_143 t22322R_121 (by norm_num)

theorem t22322R_119 : rows2 142 300 ≤ 915127048448426985 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_142 t22322R_120 (by norm_num)

theorem t22322R_118 : rows2 141 300 ≤ 918240746089230288 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_141 t22322R_119 (by norm_num)

theorem t22322R_117 : rows2 140 300 ≤ 921361943785580389 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_140 t22322R_118 (by norm_num)

theorem t22322R_116 : rows2 139 300 ≤ 924480720416271229 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_139 t22322R_117 (by norm_num)

theorem t22322R_115 : rows2 138 300 ≤ 927599313140622085 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_138 t22322R_116 (by norm_num)

theorem t22322R_114 : rows2 137 300 ≤ 930726603719204355 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_137 t22322R_115 (by norm_num)

theorem t22322R_113 : rows2 136 300 ≤ 933855353357191434 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_136 t22322R_114 (by norm_num)

theorem t22322R_112 : rows2 135 300 ≤ 936985522692499198 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_135 t22322R_113 (by norm_num)

theorem t22322R_111 : rows2 134 300 ≤ 940053934930501384 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_134 t22322R_112 (by norm_num)

theorem t22322R_110 : rows2 133 300 ≤ 942976357081912082 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_133 t22322R_111 (by norm_num)

theorem t22322R_109 : rows2 132 300 ≤ 945752188911882104 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_132 t22322R_110 (by norm_num)

theorem t22322R_108 : rows2 131 300 ≤ 948388531929293103 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_131 t22322R_109 (by norm_num)

theorem t22322R_107 : rows2 130 300 ≤ 950875199714520585 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_130 t22322R_108 (by norm_num)

theorem t22322R_106 : rows2 129 300 ≤ 953210117590204931 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_129 t22322R_107 (by norm_num)

theorem t22322R_105 : rows2 128 300 ≤ 955401746519947128 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_128 t22322R_106 (by norm_num)

theorem t22322R_104 : rows2 127 300 ≤ 957438629476226404 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_127 t22322R_105 (by norm_num)

theorem t22322R_103 : rows2 126 300 ≤ 959319685494568688 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_126 t22322R_104 (by norm_num)

theorem t22322R_102 : rows2 125 300 ≤ 961032422925778944 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_125 t22322R_103 (by norm_num)

theorem t22322R_101 : rows2 124 300 ≤ 962573806885128479 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_124 t22322R_102 (by norm_num)

theorem t22322R_100 : rows2 123 300 ≤ 963940396586177257 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_123 t22322R_101 (by norm_num)

theorem t22322R_99 : rows2 122 300 ≤ 965128804631682882 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_122 t22322R_100 (by norm_num)

theorem t22322R_98 : rows2 121 300 ≤ 966135229677632589 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_121 t22322R_99 (by norm_num)

theorem t22322R_97 : rows2 120 300 ≤ 966955866746724891 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_120 t22322R_98 (by norm_num)

theorem t22322R_96 : rows2 119 300 ≤ 967586874073587595 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_119 t22322R_97 (by norm_num)

theorem t22322R_95 : rows2 118 300 ≤ 968023679270404816 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_118 t22322R_96 (by norm_num)

theorem t22322R_94 : rows2 117 300 ≤ 968365345810511644 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_117 t22322R_95 (by norm_num)

theorem t22322R_93 : rows2 116 300 ≤ 968712623591007026 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_116 t22322R_94 (by norm_num)

theorem t22322R_92 : rows2 115 300 ≤ 969065544965311418 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_115 t22322R_93 (by norm_num)

theorem t22322R_91 : rows2 114 300 ≤ 969424937995989494 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_114 t22322R_92 (by norm_num)

theorem t22322R_90 : rows2 113 300 ≤ 969896216182507576 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_113 t22322R_91 (by norm_num)

theorem t22322R_89 : rows2 112 300 ≤ 970374770622849838 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_112 t22322R_90 (by norm_num)

theorem t22322R_88 : rows2 111 300 ≤ 970966297667316915 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_111 t22322R_89 (by norm_num)

theorem t22322R_87 : rows2 110 300 ≤ 971567543528773337 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_110 t22322R_88 (by norm_num)

theorem t22322R_86 : rows2 109 300 ≤ 972285016089942930 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_109 t22322R_87 (by norm_num)

theorem t22322R_85 : rows2 108 300 ≤ 973015922183560436 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_108 t22322R_86 (by norm_num)

theorem t22322R_84 : rows2 107 300 ≤ 973867514317715473 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_107 t22322R_85 (by norm_num)

theorem t22322R_83 : rows2 106 300 ≤ 974735852672131300 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_106 t22322R_84 (by norm_num)

theorem t22322R_82 : rows2 105 300 ≤ 975730130812822835 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_105 t22322R_83 (by norm_num)

theorem t22322R_81 : rows2 104 300 ≤ 976745342045648326 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_104 t22322R_82 (by norm_num)

theorem t22322R_80 : rows2 103 300 ≤ 977892516265887009 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_103 t22322R_81 (by norm_num)

theorem t22322R_79 : rows2 102 300 ≤ 979065389237722464 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_102 t22322R_80 (by norm_num)

theorem t22322R_78 : rows2 101 300 ≤ 980376792853945843 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_101 t22322R_79 (by norm_num)

theorem t22322R_77 : rows2 100 300 ≤ 981718264747208104 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_100 t22322R_78 (by norm_num)

theorem t22322R_76 : rows2 99 300 ≤ 983204305121226464 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_99 t22322R_77 (by norm_num)

theorem t22322R_75 : rows2 98 300 ≤ 984724425630063847 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_98 t22322R_76 (by norm_num)

theorem t22322R_74 : rows2 97 300 ≤ 986395430186027002 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_97 t22322R_75 (by norm_num)

theorem t22322R_73 : rows2 96 300 ≤ 988104704785092391 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_96 t22322R_74 (by norm_num)

theorem t22322R_72 : rows2 95 300 ≤ 990014765683184958 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_95 t22322R_73 (by norm_num)

theorem t22322R_71 : rows2 94 300 ≤ 991733603011831228 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_94 t22322R_72 (by norm_num)

theorem t22322R_70 : rows2 93 300 ≤ 993374065510082080 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_93 t22322R_71 (by norm_num)

theorem t22322R_69 : rows2 92 300 ≤ 994811116261209718 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_92 t22322R_70 (by norm_num)

theorem t22322R_68 : rows2 91 300 ≤ 996159930544090390 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_91 t22322R_69 (by norm_num)

theorem t22322R_67 : rows2 90 300 ≤ 997292766795187447 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_90 t22322R_68 (by norm_num)

theorem t22322R_66 : rows2 89 300 ≤ 998326977030744200 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_89 t22322R_67 (by norm_num)

theorem t22322R_65 : rows2 88 300 ≤ 999211102639070581 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_88 t22322R_66 (by norm_num)

theorem t22322R_64 : rows2 87 300 ≤ 1000119293066770292 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_87 t22322R_65 (by norm_num)

theorem t22322R_63 : rows2 86 300 ≤ 1001054419402730045 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_86 t22322R_64 (by norm_num)

theorem t22322R_62 : rows2 85 300 ≤ 1002024718229786437 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_85 t22322R_63 (by norm_num)

theorem t22322R_61 : rows2 84 300 ≤ 1003032181131922070 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_84 t22322R_62 (by norm_num)

theorem t22322R_60 : rows2 83 300 ≤ 1004083728780174579 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_83 t22322R_61 (by norm_num)

theorem t22322R_59 : rows2 82 300 ≤ 1005180515728457156 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_82 t22322R_60 (by norm_num)

theorem t22322R_58 : rows2 81 300 ≤ 1006328223679464928 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_81 t22322R_59 (by norm_num)

theorem t22322R_57 : rows2 80 300 ≤ 1007526994260446802 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_80 t22322R_58 (by norm_num)

theorem t22322R_56 : rows2 79 300 ≤ 1008781674950920115 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_79 t22322R_57 (by norm_num)

theorem t22322R_55 : rows2 78 300 ≤ 1010091562283621108 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_78 t22322R_56 (by norm_num)

theorem t22322R_54 : rows2 77 300 ≤ 1011460389327484182 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_77 t22322R_55 (by norm_num)

theorem t22322R_53 : rows2 76 300 ≤ 1012886867631389287 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_76 t22322R_54 (by norm_num)

theorem t22322R_52 : rows2 75 300 ≤ 1014373561313362838 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_75 t22322R_53 (by norm_num)

theorem t22322R_51 : rows2 74 300 ≤ 1015918563021213378 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_74 t22322R_52 (by norm_num)

theorem t22322R_50 : rows2 73 300 ≤ 1017525048911631609 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_73 t22322R_51 (by norm_num)

theorem t22322R_49 : rows2 72 300 ≤ 1019194300350006084 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_72 t22322R_50 (by norm_num)

theorem t22322R_48 : rows2 71 300 ≤ 1020932483734525306 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_71 t22322R_49 (by norm_num)

theorem t22322R_47 : rows2 70 300 ≤ 1022738632916234811 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_70 t22322R_48 (by norm_num)

theorem t22322R_46 : rows2 69 300 ≤ 1024614747602894563 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_69 t22322R_47 (by norm_num)

theorem t22322R_45 : rows2 68 300 ≤ 1026557174405192835 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_68 t22322R_46 (by norm_num)

theorem t22322R_44 : rows2 67 300 ≤ 1028566807791091872 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_67 t22322R_45 (by norm_num)

theorem t22322R_43 : rows2 66 300 ≤ 1030638812876671331 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_66 t22322R_44 (by norm_num)

theorem t22322R_42 : rows2 65 300 ≤ 1032773028332137859 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_65 t22322R_43 (by norm_num)

theorem t22322R_41 : rows2 64 300 ≤ 1034964024657749955 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_64 t22322R_42 (by norm_num)

theorem t22322R_40 : rows2 63 300 ≤ 1037210822536622327 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_63 t22322R_41 (by norm_num)

theorem t22322R_39 : rows2 62 300 ≤ 1039507283092207355 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_62 t22322R_40 (by norm_num)

theorem t22322R_38 : rows2 61 300 ≤ 1041852042551523593 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_61 t22322R_39 (by norm_num)

theorem t22322R_37 : rows2 60 300 ≤ 1044238424654401503 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_60 t22322R_38 (by norm_num)

theorem t22322R_36 : rows2 59 300 ≤ 1046664692258378695 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_59 t22322R_37 (by norm_num)

theorem t22322R_35 : rows2 58 300 ≤ 1049124189699443148 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_58 t22322R_36 (by norm_num)

theorem t22322R_34 : rows2 57 300 ≤ 1051614936910186058 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_57 t22322R_35 (by norm_num)

theorem t22322R_33 : rows2 56 300 ≤ 1054130076154509479 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_56 t22322R_34 (by norm_num)

theorem t22322R_32 : rows2 55 300 ≤ 1056667691878476443 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_55 t22322R_33 (by norm_num)

theorem t22322R_31 : rows2 54 300 ≤ 1059221012050361770 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_54 t22322R_32 (by norm_num)

theorem t22322R_30 : rows2 53 300 ≤ 1061788521925275429 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_53 t22322R_31 (by norm_num)

theorem t22322R_29 : rows2 52 300 ≤ 1064364165647397543 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_52 t22322R_30 (by norm_num)

theorem t22322R_28 : rows2 51 300 ≤ 1066946840145485117 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_51 t22322R_29 (by norm_num)

theorem t22322R_27 : rows2 50 300 ≤ 1069530872151151445 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_50 t22322R_28 (by norm_num)

theorem t22322R_26 : rows2 49 300 ≤ 1072115746659660563 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_49 t22322R_27 (by norm_num)

theorem t22322R_25 : rows2 48 300 ≤ 1074695618475762499 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_48 t22322R_26 (by norm_num)

theorem t22322R_24 : rows2 47 300 ≤ 1077267830438441549 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_47 t22322R_25 (by norm_num)

theorem t22322R_23 : rows2 46 300 ≤ 1079843048346697156 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_46 t22322R_24 (by norm_num)

theorem t22322R_22 : rows2 45 300 ≤ 1082436048518530750 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_45 t22322R_23 (by norm_num)

theorem t22322R_21 : rows2 44 300 ≤ 1085058677496032780 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_44 t22322R_22 (by norm_num)

theorem t22322R_20 : rows2 43 300 ≤ 1087720266647092151 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_43 t22322R_21 (by norm_num)

theorem t22322R_19 : rows2 42 300 ≤ 1090427032009395777 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_42 t22322R_20 (by norm_num)

theorem t22322R_18 : rows2 41 300 ≤ 1093182302842856154 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_41 t22322R_19 (by norm_num)

theorem t22322R_17 : rows2 40 300 ≤ 1095986143118497918 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_40 t22322R_18 (by norm_num)

theorem t22322R_16 : rows2 39 300 ≤ 1098835722068745907 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_39 t22322R_17 (by norm_num)

theorem t22322R_15 : rows2 38 300 ≤ 1101725101727781096 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_38 t22322R_16 (by norm_num)

theorem t22322R_14 : rows2 37 300 ≤ 1104645700587700691 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_37 t22322R_15 (by norm_num)

theorem t22322R_13 : rows2 36 300 ≤ 1107585743442076725 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_36 t22322R_14 (by norm_num)

theorem t22322R_12 : rows2 35 300 ≤ 1110530824486224270 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22322R_35 t22322R_13 (by norm_num)

theorem t22322R_11 : rows2 34 300 ≤ 1113463458822247252 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_11 t22322R_12 (by norm_num)

theorem t22322R_10 : rows2 33 300 ≤ 1116363572086977763 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_10 t22322R_11 (by norm_num)

theorem t22322R_9 : rows2 32 300 ≤ 1119209155782451900 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_9 t22322R_10 (by norm_num)

theorem t22322R_8 : rows2 31 300 ≤ 1121978007909828484 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_8 t22322R_9 (by norm_num)

theorem t22322R_7 : rows2 30 300 ≤ 1124651056685905309 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_7 t22322R_8 (by norm_num)

theorem t22322R_6 : rows2 29 300 ≤ 1127212767239507802 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_6 t22322R_7 (by norm_num)

theorem t22322R_5 : rows2 28 300 ≤ 1129650928888046448 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_5 t22322R_6 (by norm_num)

theorem t22322R_4 : rows2 27 300 ≤ 1131956244469719501 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_4 t22322R_5 (by norm_num)

theorem t22322R_3 : rows2 25 300 ≤ 1136146347073143835 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_3 t22322R_4 (by norm_num)

theorem t22322R_2 : rows2 23 300 ≤ 1139767730779905094 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_2 t22322R_3 (by norm_num)

theorem t22322R_1 : rows2 19 300 ≤ 1145400153497687514 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_1 t22322R_2 (by norm_num)

theorem t22322R_0 : rows2 0 300 ≤ 1152600486568670170 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22322R_0 t22322R_1 (by norm_num)

/-- **The refined certificate on `grid22322R`**: the loss's bound is less than `K`, the 561 parts checked by the
kernel. -/
theorem total2_lt_22322R : total2 < K := by
  rw [total2_eq_rows2_full]
  exact lt_of_le_of_lt t22322R_0 (by decide +kernel)

end

end SieveCert

#print axioms SieveCert.total2_lt_22322R
