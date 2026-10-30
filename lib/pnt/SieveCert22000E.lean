/-
# The certificate to depth 8 of the sieve route's loss at `L = 11/5` with `n = 272`: `totalD < K`

On `SieveGrid22000E.grid22000E` (`U1 = ⌈(43457/100000)DEN⌉`, `U2 = ⌊(46959/100000)DEN⌋`, `n = 272`) under `ibRule`
(`ibPar22000E`, `L = 11/5`), `SieveDeep.totalD` is less than `K` (it is below `0.93214K`, rounded up): `totalD` is
`rowsJD 0 n 0 n` (`SieveDeep.totalD_eq_rowsJD`), and its bound is assembled one step at a time from the 1136 parts'
bounds (`rows22000E_0` … `rows22000E_1135`, each by `decide +kernel` in one of the 114 part files): a heavy row's
bound from its column pieces' (`rowsJD_le_of_splitJ`), then the 229 ranges of rows from the last to the first
(`rowsJD_le_of_splitI`), every bound a literal and every step a theorem of its own (`c22000E_…`, `t22000E_…`); the
bounds, `⌈1.001 × part⌉` computed exactly in integers, sum to `1075756859466551505`, less than `K` by `decide
+kernel` (`totalD_lt_22000E`).

The file imports `SieveDeepCert.lean` and `SieveCert22000EP1.lean` … `SieveCert22000EP114.lean`.
-/
import SieveDeepCert
import SieveCert22000EP1
import SieveCert22000EP2
import SieveCert22000EP3
import SieveCert22000EP4
import SieveCert22000EP5
import SieveCert22000EP6
import SieveCert22000EP7
import SieveCert22000EP8
import SieveCert22000EP9
import SieveCert22000EP10
import SieveCert22000EP11
import SieveCert22000EP12
import SieveCert22000EP13
import SieveCert22000EP14
import SieveCert22000EP15
import SieveCert22000EP16
import SieveCert22000EP17
import SieveCert22000EP18
import SieveCert22000EP19
import SieveCert22000EP20
import SieveCert22000EP21
import SieveCert22000EP22
import SieveCert22000EP23
import SieveCert22000EP24
import SieveCert22000EP25
import SieveCert22000EP26
import SieveCert22000EP27
import SieveCert22000EP28
import SieveCert22000EP29
import SieveCert22000EP30
import SieveCert22000EP31
import SieveCert22000EP32
import SieveCert22000EP33
import SieveCert22000EP34
import SieveCert22000EP35
import SieveCert22000EP36
import SieveCert22000EP37
import SieveCert22000EP38
import SieveCert22000EP39
import SieveCert22000EP40
import SieveCert22000EP41
import SieveCert22000EP42
import SieveCert22000EP43
import SieveCert22000EP44
import SieveCert22000EP45
import SieveCert22000EP46
import SieveCert22000EP47
import SieveCert22000EP48
import SieveCert22000EP49
import SieveCert22000EP50
import SieveCert22000EP51
import SieveCert22000EP52
import SieveCert22000EP53
import SieveCert22000EP54
import SieveCert22000EP55
import SieveCert22000EP56
import SieveCert22000EP57
import SieveCert22000EP58
import SieveCert22000EP59
import SieveCert22000EP60
import SieveCert22000EP61
import SieveCert22000EP62
import SieveCert22000EP63
import SieveCert22000EP64
import SieveCert22000EP65
import SieveCert22000EP66
import SieveCert22000EP67
import SieveCert22000EP68
import SieveCert22000EP69
import SieveCert22000EP70
import SieveCert22000EP71
import SieveCert22000EP72
import SieveCert22000EP73
import SieveCert22000EP74
import SieveCert22000EP75
import SieveCert22000EP76
import SieveCert22000EP77
import SieveCert22000EP78
import SieveCert22000EP79
import SieveCert22000EP80
import SieveCert22000EP81
import SieveCert22000EP82
import SieveCert22000EP83
import SieveCert22000EP84
import SieveCert22000EP85
import SieveCert22000EP86
import SieveCert22000EP87
import SieveCert22000EP88
import SieveCert22000EP89
import SieveCert22000EP90
import SieveCert22000EP91
import SieveCert22000EP92
import SieveCert22000EP93
import SieveCert22000EP94
import SieveCert22000EP95
import SieveCert22000EP96
import SieveCert22000EP97
import SieveCert22000EP98
import SieveCert22000EP99
import SieveCert22000EP100
import SieveCert22000EP101
import SieveCert22000EP102
import SieveCert22000EP103
import SieveCert22000EP104
import SieveCert22000EP105
import SieveCert22000EP106
import SieveCert22000EP107
import SieveCert22000EP108
import SieveCert22000EP109
import SieveCert22000EP110
import SieveCert22000EP111
import SieveCert22000EP112
import SieveCert22000EP113
import SieveCert22000EP114

namespace SieveDeep

open SieveCert

section

attribute [local instance] grid22000E ibPar22000E

/-! The chain of bounds: `c22000E_{i}_{m}` for the heavy row `i` from its `m`-th column piece on, `t22000E_{m}` for
the rows from the `m`-th range on; each a theorem of its own. -/

theorem c22000E_37_0 : rowsJD 37 38 0 272 ≤ 412382366589089 :=
  rowsJD_le_of_splitJ 37 38 (by norm_num) (by norm_num) rows22000E_14 rows22000E_15 (by norm_num)

theorem c22000E_38_0 : rowsJD 38 39 0 272 ≤ 432262178919162 :=
  rowsJD_le_of_splitJ 38 39 (by norm_num) (by norm_num) rows22000E_16 rows22000E_17 (by norm_num)

theorem c22000E_39_0 : rowsJD 39 40 0 272 ≤ 453593082921484 :=
  rowsJD_le_of_splitJ 39 40 (by norm_num) (by norm_num) rows22000E_18 rows22000E_19 (by norm_num)

theorem c22000E_40_0 : rowsJD 40 41 0 272 ≤ 479477470597759 :=
  rowsJD_le_of_splitJ 40 41 (by norm_num) (by norm_num) rows22000E_20 rows22000E_21 (by norm_num)

theorem c22000E_41_0 : rowsJD 41 42 0 272 ≤ 509572461686344 :=
  rowsJD_le_of_splitJ 41 42 (by norm_num) (by norm_num) rows22000E_22 rows22000E_23 (by norm_num)

theorem c22000E_42_0 : rowsJD 42 43 0 272 ≤ 539555538520694 :=
  rowsJD_le_of_splitJ 42 43 (by norm_num) (by norm_num) rows22000E_24 rows22000E_25 (by norm_num)

theorem c22000E_43_0 : rowsJD 43 44 0 272 ≤ 569034115310948 :=
  rowsJD_le_of_splitJ 43 44 (by norm_num) (by norm_num) rows22000E_26 rows22000E_27 (by norm_num)

theorem c22000E_44_0 : rowsJD 44 45 0 272 ≤ 601030573183807 :=
  rowsJD_le_of_splitJ 44 45 (by norm_num) (by norm_num) rows22000E_28 rows22000E_29 (by norm_num)

theorem c22000E_45_0 : rowsJD 45 46 0 272 ≤ 634523398130514 :=
  rowsJD_le_of_splitJ 45 46 (by norm_num) (by norm_num) rows22000E_30 rows22000E_31 (by norm_num)

theorem c22000E_46_0 : rowsJD 46 47 0 272 ≤ 666017030591415 :=
  rowsJD_le_of_splitJ 46 47 (by norm_num) (by norm_num) rows22000E_32 rows22000E_33 (by norm_num)

theorem c22000E_47_1 : rowsJD 47 48 37 272 ≤ 369835387934595 :=
  rowsJD_le_of_splitJ 47 48 (by norm_num) (by norm_num) rows22000E_35 rows22000E_36 (by norm_num)

theorem c22000E_47_0 : rowsJD 47 48 0 272 ≤ 694127098374065 :=
  rowsJD_le_of_splitJ 47 48 (by norm_num) (by norm_num) rows22000E_34 c22000E_47_1 (by norm_num)

theorem c22000E_48_1 : rowsJD 48 49 37 272 ≤ 399806639564773 :=
  rowsJD_le_of_splitJ 48 49 (by norm_num) (by norm_num) rows22000E_38 rows22000E_39 (by norm_num)

theorem c22000E_48_0 : rowsJD 48 49 0 272 ≤ 719808207013383 :=
  rowsJD_le_of_splitJ 48 49 (by norm_num) (by norm_num) rows22000E_37 c22000E_48_1 (by norm_num)

theorem c22000E_49_1 : rowsJD 49 50 37 272 ≤ 427630559476146 :=
  rowsJD_le_of_splitJ 49 50 (by norm_num) (by norm_num) rows22000E_41 rows22000E_42 (by norm_num)

theorem c22000E_49_0 : rowsJD 49 50 0 272 ≤ 743233678684326 :=
  rowsJD_le_of_splitJ 49 50 (by norm_num) (by norm_num) rows22000E_40 c22000E_49_1 (by norm_num)

theorem c22000E_50_1 : rowsJD 50 51 37 272 ≤ 452775504037379 :=
  rowsJD_le_of_splitJ 50 51 (by norm_num) (by norm_num) rows22000E_44 rows22000E_45 (by norm_num)

theorem c22000E_50_0 : rowsJD 50 51 0 272 ≤ 763993715598017 :=
  rowsJD_le_of_splitJ 50 51 (by norm_num) (by norm_num) rows22000E_43 c22000E_50_1 (by norm_num)

theorem c22000E_51_1 : rowsJD 51 52 37 272 ≤ 474247022574437 :=
  rowsJD_le_of_splitJ 51 52 (by norm_num) (by norm_num) rows22000E_47 rows22000E_48 (by norm_num)

theorem c22000E_51_0 : rowsJD 51 52 0 272 ≤ 781638399083445 :=
  rowsJD_le_of_splitJ 51 52 (by norm_num) (by norm_num) rows22000E_46 c22000E_51_1 (by norm_num)

theorem c22000E_52_1 : rowsJD 52 53 37 272 ≤ 492442011502993 :=
  rowsJD_le_of_splitJ 52 53 (by norm_num) (by norm_num) rows22000E_50 rows22000E_51 (by norm_num)

theorem c22000E_52_0 : rowsJD 52 53 0 272 ≤ 796466983914125 :=
  rowsJD_le_of_splitJ 52 53 (by norm_num) (by norm_num) rows22000E_49 c22000E_52_1 (by norm_num)

theorem c22000E_53_1 : rowsJD 53 54 37 272 ≤ 506973826855862 :=
  rowsJD_le_of_splitJ 53 54 (by norm_num) (by norm_num) rows22000E_53 rows22000E_54 (by norm_num)

theorem c22000E_53_0 : rowsJD 53 54 0 272 ≤ 807984669913279 :=
  rowsJD_le_of_splitJ 53 54 (by norm_num) (by norm_num) rows22000E_52 c22000E_53_1 (by norm_num)

theorem c22000E_54_1 : rowsJD 54 55 37 272 ≤ 517971368626657 :=
  rowsJD_le_of_splitJ 54 55 (by norm_num) (by norm_num) rows22000E_56 rows22000E_57 (by norm_num)

theorem c22000E_54_0 : rowsJD 54 55 0 272 ≤ 816222278234371 :=
  rowsJD_le_of_splitJ 54 55 (by norm_num) (by norm_num) rows22000E_55 c22000E_54_1 (by norm_num)

theorem c22000E_55_2 : rowsJD 55 56 47 272 ≤ 238594262701513 :=
  rowsJD_le_of_splitJ 55 56 (by norm_num) (by norm_num) rows22000E_60 rows22000E_61 (by norm_num)

theorem c22000E_55_1 : rowsJD 55 56 37 272 ≤ 523985349389722 :=
  rowsJD_le_of_splitJ 55 56 (by norm_num) (by norm_num) rows22000E_59 c22000E_55_2 (by norm_num)

theorem c22000E_55_0 : rowsJD 55 56 0 272 ≤ 818327154943002 :=
  rowsJD_le_of_splitJ 55 56 (by norm_num) (by norm_num) rows22000E_58 c22000E_55_1 (by norm_num)

theorem c22000E_56_2 : rowsJD 56 57 48 272 ≤ 221694574274519 :=
  rowsJD_le_of_splitJ 56 57 (by norm_num) (by norm_num) rows22000E_64 rows22000E_65 (by norm_num)

theorem c22000E_56_1 : rowsJD 56 57 37 272 ≤ 527574576929308 :=
  rowsJD_le_of_splitJ 56 57 (by norm_num) (by norm_num) rows22000E_63 c22000E_56_2 (by norm_num)

theorem c22000E_56_0 : rowsJD 56 57 0 272 ≤ 817902155852321 :=
  rowsJD_le_of_splitJ 56 57 (by norm_num) (by norm_num) rows22000E_62 c22000E_56_1 (by norm_num)

theorem c22000E_57_2 : rowsJD 57 58 48 272 ≤ 231115879885166 :=
  rowsJD_le_of_splitJ 57 58 (by norm_num) (by norm_num) rows22000E_68 rows22000E_69 (by norm_num)

theorem c22000E_57_1 : rowsJD 57 58 37 272 ≤ 528771301348742 :=
  rowsJD_le_of_splitJ 57 58 (by norm_num) (by norm_num) rows22000E_67 c22000E_57_2 (by norm_num)

theorem c22000E_57_0 : rowsJD 57 58 0 272 ≤ 815553165374945 :=
  rowsJD_le_of_splitJ 57 58 (by norm_num) (by norm_num) rows22000E_66 c22000E_57_1 (by norm_num)

theorem c22000E_58_2 : rowsJD 58 59 48 272 ≤ 238721257552015 :=
  rowsJD_le_of_splitJ 58 59 (by norm_num) (by norm_num) rows22000E_72 rows22000E_73 (by norm_num)

theorem c22000E_58_1 : rowsJD 58 59 37 272 ≤ 528124363642124 :=
  rowsJD_le_of_splitJ 58 59 (by norm_num) (by norm_num) rows22000E_71 c22000E_58_2 (by norm_num)

theorem c22000E_58_0 : rowsJD 58 59 0 272 ≤ 811333436775144 :=
  rowsJD_le_of_splitJ 58 59 (by norm_num) (by norm_num) rows22000E_70 c22000E_58_1 (by norm_num)

theorem c22000E_59_3 : rowsJD 59 60 55 272 ≤ 91421082603534 :=
  rowsJD_le_of_splitJ 59 60 (by norm_num) (by norm_num) rows22000E_77 rows22000E_78 (by norm_num)

theorem c22000E_59_2 : rowsJD 59 60 48 272 ≤ 244308748969523 :=
  rowsJD_le_of_splitJ 59 60 (by norm_num) (by norm_num) rows22000E_76 c22000E_59_3 (by norm_num)

theorem c22000E_59_1 : rowsJD 59 60 37 272 ≤ 525585558502376 :=
  rowsJD_le_of_splitJ 59 60 (by norm_num) (by norm_num) rows22000E_75 c22000E_59_2 (by norm_num)

theorem c22000E_59_0 : rowsJD 59 60 0 272 ≤ 805723101074398 :=
  rowsJD_le_of_splitJ 59 60 (by norm_num) (by norm_num) rows22000E_74 c22000E_59_1 (by norm_num)

theorem c22000E_60_3 : rowsJD 60 61 55 272 ≤ 104423034594672 :=
  rowsJD_le_of_splitJ 60 61 (by norm_num) (by norm_num) rows22000E_82 rows22000E_83 (by norm_num)

theorem c22000E_60_2 : rowsJD 60 61 48 272 ≤ 250266809117990 :=
  rowsJD_le_of_splitJ 60 61 (by norm_num) (by norm_num) rows22000E_81 c22000E_60_3 (by norm_num)

theorem c22000E_60_1 : rowsJD 60 61 37 272 ≤ 524028452130679 :=
  rowsJD_le_of_splitJ 60 61 (by norm_num) (by norm_num) rows22000E_80 c22000E_60_2 (by norm_num)

theorem c22000E_60_0 : rowsJD 60 61 0 272 ≤ 801181801315350 :=
  rowsJD_le_of_splitJ 60 61 (by norm_num) (by norm_num) rows22000E_79 c22000E_60_1 (by norm_num)

theorem c22000E_61_3 : rowsJD 61 62 55 272 ≤ 116446279450615 :=
  rowsJD_le_of_splitJ 61 62 (by norm_num) (by norm_num) rows22000E_87 rows22000E_88 (by norm_num)

theorem c22000E_61_2 : rowsJD 61 62 48 272 ≤ 255369034953017 :=
  rowsJD_le_of_splitJ 61 62 (by norm_num) (by norm_num) rows22000E_86 c22000E_61_3 (by norm_num)

theorem c22000E_61_1 : rowsJD 61 62 37 272 ≤ 521764690857913 :=
  rowsJD_le_of_splitJ 61 62 (by norm_num) (by norm_num) rows22000E_85 c22000E_61_2 (by norm_num)

theorem c22000E_61_0 : rowsJD 61 62 0 272 ≤ 796350208443290 :=
  rowsJD_le_of_splitJ 61 62 (by norm_num) (by norm_num) rows22000E_84 c22000E_61_1 (by norm_num)

theorem c22000E_62_3 : rowsJD 62 63 55 272 ≤ 129291113504369 :=
  rowsJD_le_of_splitJ 62 63 (by norm_num) (by norm_num) rows22000E_92 rows22000E_93 (by norm_num)

theorem c22000E_62_2 : rowsJD 62 63 48 272 ≤ 261797403043536 :=
  rowsJD_le_of_splitJ 62 63 (by norm_num) (by norm_num) rows22000E_91 c22000E_62_3 (by norm_num)

theorem c22000E_62_1 : rowsJD 62 63 37 272 ≤ 520845027448579 :=
  rowsJD_le_of_splitJ 62 63 (by norm_num) (by norm_num) rows22000E_90 c22000E_62_2 (by norm_num)

theorem c22000E_62_0 : rowsJD 62 63 0 272 ≤ 792926649471295 :=
  rowsJD_le_of_splitJ 62 63 (by norm_num) (by norm_num) rows22000E_89 c22000E_62_1 (by norm_num)

theorem c22000E_63_4 : rowsJD 63 64 59 272 ≤ 81821268721686 :=
  rowsJD_le_of_splitJ 63 64 (by norm_num) (by norm_num) rows22000E_98 rows22000E_99 (by norm_num)

theorem c22000E_63_3 : rowsJD 63 64 55 272 ≤ 143491592143474 :=
  rowsJD_le_of_splitJ 63 64 (by norm_num) (by norm_num) rows22000E_97 c22000E_63_4 (by norm_num)

theorem c22000E_63_2 : rowsJD 63 64 48 272 ≤ 269987600717381 :=
  rowsJD_le_of_splitJ 63 64 (by norm_num) (by norm_num) rows22000E_96 c22000E_63_3 (by norm_num)

theorem c22000E_63_1 : rowsJD 63 64 37 272 ≤ 521789714603225 :=
  rowsJD_le_of_splitJ 63 64 (by norm_num) (by norm_num) rows22000E_95 c22000E_63_2 (by norm_num)

theorem c22000E_63_0 : rowsJD 63 64 0 272 ≤ 791748867236782 :=
  rowsJD_le_of_splitJ 63 64 (by norm_num) (by norm_num) rows22000E_94 c22000E_63_1 (by norm_num)

theorem c22000E_64_4 : rowsJD 64 65 60 272 ≤ 85279856237772 :=
  rowsJD_le_of_splitJ 64 65 (by norm_num) (by norm_num) rows22000E_104 rows22000E_105 (by norm_num)

theorem c22000E_64_3 : rowsJD 64 65 55 272 ≤ 159448340309784 :=
  rowsJD_le_of_splitJ 64 65 (by norm_num) (by norm_num) rows22000E_103 c22000E_64_4 (by norm_num)

theorem c22000E_64_2 : rowsJD 64 65 48 272 ≤ 280277599617074 :=
  rowsJD_le_of_splitJ 64 65 (by norm_num) (by norm_num) rows22000E_102 c22000E_64_3 (by norm_num)

theorem c22000E_64_1 : rowsJD 64 65 37 272 ≤ 524484924185946 :=
  rowsJD_le_of_splitJ 64 65 (by norm_num) (by norm_num) rows22000E_101 c22000E_64_2 (by norm_num)

theorem c22000E_64_0 : rowsJD 64 65 0 272 ≤ 791034325789927 :=
  rowsJD_le_of_splitJ 64 65 (by norm_num) (by norm_num) rows22000E_100 c22000E_64_1 (by norm_num)

theorem c22000E_65_4 : rowsJD 65 66 60 272 ≤ 98595484248825 :=
  rowsJD_le_of_splitJ 65 66 (by norm_num) (by norm_num) rows22000E_110 rows22000E_111 (by norm_num)

theorem c22000E_65_3 : rowsJD 65 66 55 272 ≤ 170275162291380 :=
  rowsJD_le_of_splitJ 65 66 (by norm_num) (by norm_num) rows22000E_109 c22000E_65_4 (by norm_num)

theorem c22000E_65_2 : rowsJD 65 66 48 272 ≤ 285626975568395 :=
  rowsJD_le_of_splitJ 65 66 (by norm_num) (by norm_num) rows22000E_108 c22000E_65_3 (by norm_num)

theorem c22000E_65_1 : rowsJD 65 66 37 272 ≤ 522156403099667 :=
  rowsJD_le_of_splitJ 65 66 (by norm_num) (by norm_num) rows22000E_107 c22000E_65_2 (by norm_num)

theorem c22000E_65_0 : rowsJD 65 66 0 272 ≤ 785506463931314 :=
  rowsJD_le_of_splitJ 65 66 (by norm_num) (by norm_num) rows22000E_106 c22000E_65_1 (by norm_num)

theorem c22000E_66_4 : rowsJD 66 67 60 272 ≤ 109125466206384 :=
  rowsJD_le_of_splitJ 66 67 (by norm_num) (by norm_num) rows22000E_116 rows22000E_117 (by norm_num)

theorem c22000E_66_3 : rowsJD 66 67 55 272 ≤ 178656940737762 :=
  rowsJD_le_of_splitJ 66 67 (by norm_num) (by norm_num) rows22000E_115 c22000E_66_4 (by norm_num)

theorem c22000E_66_2 : rowsJD 66 67 48 272 ≤ 289098147578805 :=
  rowsJD_le_of_splitJ 66 67 (by norm_num) (by norm_num) rows22000E_114 c22000E_66_3 (by norm_num)

theorem c22000E_66_1 : rowsJD 66 67 37 272 ≤ 517926208085718 :=
  rowsJD_le_of_splitJ 66 67 (by norm_num) (by norm_num) rows22000E_113 c22000E_66_2 (by norm_num)

theorem c22000E_66_0 : rowsJD 66 67 0 272 ≤ 778055037368961 :=
  rowsJD_le_of_splitJ 66 67 (by norm_num) (by norm_num) rows22000E_112 c22000E_66_1 (by norm_num)

theorem c22000E_67_4 : rowsJD 67 68 60 272 ≤ 116091922433683 :=
  rowsJD_le_of_splitJ 67 68 (by norm_num) (by norm_num) rows22000E_122 rows22000E_123 (by norm_num)

theorem c22000E_67_3 : rowsJD 67 68 55 272 ≤ 183686432400844 :=
  rowsJD_le_of_splitJ 67 68 (by norm_num) (by norm_num) rows22000E_121 c22000E_67_4 (by norm_num)

theorem c22000E_67_2 : rowsJD 67 68 48 272 ≤ 289480064376649 :=
  rowsJD_le_of_splitJ 67 68 (by norm_num) (by norm_num) rows22000E_120 c22000E_67_3 (by norm_num)

theorem c22000E_67_1 : rowsJD 67 68 37 272 ≤ 510541509063158 :=
  rowsJD_le_of_splitJ 67 68 (by norm_num) (by norm_num) rows22000E_119 c22000E_67_2 (by norm_num)

theorem c22000E_67_0 : rowsJD 67 68 0 272 ≤ 767683354086628 :=
  rowsJD_le_of_splitJ 67 68 (by norm_num) (by norm_num) rows22000E_118 c22000E_67_1 (by norm_num)

theorem c22000E_68_4 : rowsJD 68 69 60 272 ≤ 123068426531202 :=
  rowsJD_le_of_splitJ 68 69 (by norm_num) (by norm_num) rows22000E_128 rows22000E_129 (by norm_num)

theorem c22000E_68_3 : rowsJD 68 69 55 272 ≤ 189187058527484 :=
  rowsJD_le_of_splitJ 68 69 (by norm_num) (by norm_num) rows22000E_127 c22000E_68_4 (by norm_num)

theorem c22000E_68_2 : rowsJD 68 69 48 272 ≤ 291003941296476 :=
  rowsJD_le_of_splitJ 68 69 (by norm_num) (by norm_num) rows22000E_126 c22000E_68_3 (by norm_num)

theorem c22000E_68_1 : rowsJD 68 69 37 272 ≤ 504603230050152 :=
  rowsJD_le_of_splitJ 68 69 (by norm_num) (by norm_num) rows22000E_125 c22000E_68_2 (by norm_num)

theorem c22000E_68_0 : rowsJD 68 69 0 272 ≤ 758702711826794 :=
  rowsJD_le_of_splitJ 68 69 (by norm_num) (by norm_num) rows22000E_124 c22000E_68_1 (by norm_num)

theorem c22000E_69_5 : rowsJD 69 70 64 272 ≤ 73864034304997 :=
  rowsJD_le_of_splitJ 69 70 (by norm_num) (by norm_num) rows22000E_135 rows22000E_136 (by norm_num)

theorem c22000E_69_4 : rowsJD 69 70 60 272 ≤ 129434706768396 :=
  rowsJD_le_of_splitJ 69 70 (by norm_num) (by norm_num) rows22000E_134 c22000E_69_5 (by norm_num)

theorem c22000E_69_3 : rowsJD 69 70 55 272 ≤ 194188507799460 :=
  rowsJD_le_of_splitJ 69 70 (by norm_num) (by norm_num) rows22000E_133 c22000E_69_4 (by norm_num)

theorem c22000E_69_2 : rowsJD 69 70 48 272 ≤ 292152469903548 :=
  rowsJD_le_of_splitJ 69 70 (by norm_num) (by norm_num) rows22000E_132 c22000E_69_3 (by norm_num)

theorem c22000E_69_1 : rowsJD 69 70 37 272 ≤ 498317299466657 :=
  rowsJD_le_of_splitJ 69 70 (by norm_num) (by norm_num) rows22000E_131 c22000E_69_2 (by norm_num)

theorem c22000E_69_0 : rowsJD 69 70 0 272 ≤ 749701521020371 :=
  rowsJD_le_of_splitJ 69 70 (by norm_num) (by norm_num) rows22000E_130 c22000E_69_1 (by norm_num)

theorem c22000E_70_4 : rowsJD 70 71 60 272 ≤ 137617229303540 :=
  rowsJD_le_of_splitJ 70 71 (by norm_num) (by norm_num) rows22000E_141 rows22000E_142 (by norm_num)

theorem c22000E_70_3 : rowsJD 70 71 55 272 ≤ 201366401070580 :=
  rowsJD_le_of_splitJ 70 71 (by norm_num) (by norm_num) rows22000E_140 c22000E_70_4 (by norm_num)

theorem c22000E_70_2 : rowsJD 70 71 48 272 ≤ 295978026301126 :=
  rowsJD_le_of_splitJ 70 71 (by norm_num) (by norm_num) rows22000E_139 c22000E_70_3 (by norm_num)

theorem c22000E_70_1 : rowsJD 70 71 37 272 ≤ 494406018643842 :=
  rowsJD_le_of_splitJ 70 71 (by norm_num) (by norm_num) rows22000E_138 c22000E_70_2 (by norm_num)

theorem c22000E_70_0 : rowsJD 70 71 0 272 ≤ 742961359739226 :=
  rowsJD_le_of_splitJ 70 71 (by norm_num) (by norm_num) rows22000E_137 c22000E_70_1 (by norm_num)

theorem c22000E_71_5 : rowsJD 71 72 65 272 ≤ 87373016665826 :=
  rowsJD_le_of_splitJ 71 72 (by norm_num) (by norm_num) rows22000E_148 rows22000E_149 (by norm_num)

theorem c22000E_71_4 : rowsJD 71 72 60 272 ≤ 149331635179544 :=
  rowsJD_le_of_splitJ 71 72 (by norm_num) (by norm_num) rows22000E_147 c22000E_71_5 (by norm_num)

theorem c22000E_71_3 : rowsJD 71 72 55 272 ≤ 212231907690642 :=
  rowsJD_le_of_splitJ 71 72 (by norm_num) (by norm_num) rows22000E_146 c22000E_71_4 (by norm_num)

theorem c22000E_71_2 : rowsJD 71 72 48 272 ≤ 303578584047407 :=
  rowsJD_le_of_splitJ 71 72 (by norm_num) (by norm_num) rows22000E_145 c22000E_71_3 (by norm_num)

theorem c22000E_71_1 : rowsJD 71 72 37 272 ≤ 494325783856275 :=
  rowsJD_le_of_splitJ 71 72 (by norm_num) (by norm_num) rows22000E_144 c22000E_71_2 (by norm_num)

theorem c22000E_71_0 : rowsJD 71 72 0 272 ≤ 740353110731588 :=
  rowsJD_le_of_splitJ 71 72 (by norm_num) (by norm_num) rows22000E_143 c22000E_71_1 (by norm_num)

theorem c22000E_72_5 : rowsJD 72 73 65 272 ≤ 105926089396936 :=
  rowsJD_le_of_splitJ 72 73 (by norm_num) (by norm_num) rows22000E_155 rows22000E_156 (by norm_num)

theorem c22000E_72_4 : rowsJD 72 73 60 272 ≤ 166794015076152 :=
  rowsJD_le_of_splitJ 72 73 (by norm_num) (by norm_num) rows22000E_154 c22000E_72_5 (by norm_num)

theorem c22000E_72_3 : rowsJD 72 73 55 272 ≤ 229715406537420 :=
  rowsJD_le_of_splitJ 72 73 (by norm_num) (by norm_num) rows22000E_153 c22000E_72_4 (by norm_num)

theorem c22000E_72_2 : rowsJD 72 73 48 272 ≤ 319408062166162 :=
  rowsJD_le_of_splitJ 72 73 (by norm_num) (by norm_num) rows22000E_152 c22000E_72_3 (by norm_num)

theorem c22000E_72_1 : rowsJD 72 73 37 272 ≤ 502961540226858 :=
  rowsJD_le_of_splitJ 72 73 (by norm_num) (by norm_num) rows22000E_151 c22000E_72_2 (by norm_num)

theorem c22000E_72_0 : rowsJD 72 73 0 272 ≤ 746438926729316 :=
  rowsJD_le_of_splitJ 72 73 (by norm_num) (by norm_num) rows22000E_150 c22000E_72_1 (by norm_num)

theorem c22000E_73_5 : rowsJD 73 74 66 272 ≤ 112523400058967 :=
  rowsJD_le_of_splitJ 73 74 (by norm_num) (by norm_num) rows22000E_162 rows22000E_163 (by norm_num)

theorem c22000E_73_4 : rowsJD 73 74 60 272 ≤ 184107670756677 :=
  rowsJD_le_of_splitJ 73 74 (by norm_num) (by norm_num) rows22000E_161 c22000E_73_5 (by norm_num)

theorem c22000E_73_3 : rowsJD 73 74 55 272 ≤ 246898847937504 :=
  rowsJD_le_of_splitJ 73 74 (by norm_num) (by norm_num) rows22000E_160 c22000E_73_4 (by norm_num)

theorem c22000E_73_2 : rowsJD 73 74 48 272 ≤ 334856423745388 :=
  rowsJD_le_of_splitJ 73 74 (by norm_num) (by norm_num) rows22000E_159 c22000E_73_3 (by norm_num)

theorem c22000E_73_1 : rowsJD 73 74 37 272 ≤ 511237911744212 :=
  rowsJD_le_of_splitJ 73 74 (by norm_num) (by norm_num) rows22000E_158 c22000E_73_2 (by norm_num)

theorem c22000E_73_0 : rowsJD 73 74 0 272 ≤ 751981702647469 :=
  rowsJD_le_of_splitJ 73 74 (by norm_num) (by norm_num) rows22000E_157 c22000E_73_1 (by norm_num)

theorem c22000E_74_5 : rowsJD 74 75 66 272 ≤ 130050098066606 :=
  rowsJD_le_of_splitJ 74 75 (by norm_num) (by norm_num) rows22000E_169 rows22000E_170 (by norm_num)

theorem c22000E_74_4 : rowsJD 74 75 60 272 ≤ 201556555608831 :=
  rowsJD_le_of_splitJ 74 75 (by norm_num) (by norm_num) rows22000E_168 c22000E_74_5 (by norm_num)

theorem c22000E_74_3 : rowsJD 74 75 55 272 ≤ 264643652503335 :=
  rowsJD_le_of_splitJ 74 75 (by norm_num) (by norm_num) rows22000E_167 c22000E_74_4 (by norm_num)

theorem c22000E_74_2 : rowsJD 74 75 48 272 ≤ 351451291865721 :=
  rowsJD_le_of_splitJ 74 75 (by norm_num) (by norm_num) rows22000E_166 c22000E_74_3 (by norm_num)

theorem c22000E_74_1 : rowsJD 74 75 37 272 ≤ 520915600759350 :=
  rowsJD_le_of_splitJ 74 75 (by norm_num) (by norm_num) rows22000E_165 c22000E_74_2 (by norm_num)

theorem c22000E_74_0 : rowsJD 74 75 0 272 ≤ 758781122165844 :=
  rowsJD_le_of_splitJ 74 75 (by norm_num) (by norm_num) rows22000E_164 c22000E_74_1 (by norm_num)

theorem c22000E_75_5 : rowsJD 75 76 68 272 ≤ 121966058186349 :=
  rowsJD_le_of_splitJ 75 76 (by norm_num) (by norm_num) rows22000E_176 rows22000E_177 (by norm_num)

theorem c22000E_75_4 : rowsJD 75 76 61 272 ≤ 204965239714800 :=
  rowsJD_le_of_splitJ 75 76 (by norm_num) (by norm_num) rows22000E_175 c22000E_75_5 (by norm_num)

theorem c22000E_75_3 : rowsJD 75 76 55 272 ≤ 280399451669709 :=
  rowsJD_le_of_splitJ 75 76 (by norm_num) (by norm_num) rows22000E_174 c22000E_75_4 (by norm_num)

theorem c22000E_75_2 : rowsJD 75 76 48 272 ≤ 366008977283895 :=
  rowsJD_le_of_splitJ 75 76 (by norm_num) (by norm_num) rows22000E_173 c22000E_75_3 (by norm_num)

theorem c22000E_75_1 : rowsJD 75 76 37 272 ≤ 528714468790199 :=
  rowsJD_le_of_splitJ 75 76 (by norm_num) (by norm_num) rows22000E_172 c22000E_75_2 (by norm_num)

theorem c22000E_75_0 : rowsJD 75 76 0 272 ≤ 763534497099087 :=
  rowsJD_le_of_splitJ 75 76 (by norm_num) (by norm_num) rows22000E_171 c22000E_75_1 (by norm_num)

theorem c22000E_76_5 : rowsJD 76 77 70 272 ≤ 111984180208804 :=
  rowsJD_le_of_splitJ 76 77 (by norm_num) (by norm_num) rows22000E_183 rows22000E_184 (by norm_num)

theorem c22000E_76_4 : rowsJD 76 77 62 272 ≤ 209172937336225 :=
  rowsJD_le_of_splitJ 76 77 (by norm_num) (by norm_num) rows22000E_182 c22000E_76_5 (by norm_num)

theorem c22000E_76_3 : rowsJD 76 77 56 272 ≤ 284594756011815 :=
  rowsJD_le_of_splitJ 76 77 (by norm_num) (by norm_num) rows22000E_181 c22000E_76_4 (by norm_num)

theorem c22000E_76_2 : rowsJD 76 77 49 272 ≤ 369878085605701 :=
  rowsJD_le_of_splitJ 76 77 (by norm_num) (by norm_num) rows22000E_180 c22000E_76_3 (by norm_num)

theorem c22000E_76_1 : rowsJD 76 77 37 272 ≤ 538324543922282 :=
  rowsJD_le_of_splitJ 76 77 (by norm_num) (by norm_num) rows22000E_179 c22000E_76_2 (by norm_num)

theorem c22000E_76_0 : rowsJD 76 77 0 272 ≤ 770029090373547 :=
  rowsJD_le_of_splitJ 76 77 (by norm_num) (by norm_num) rows22000E_178 c22000E_76_1 (by norm_num)

theorem c22000E_77_5 : rowsJD 77 78 70 272 ≤ 126652258585239 :=
  rowsJD_le_of_splitJ 77 78 (by norm_num) (by norm_num) rows22000E_190 rows22000E_191 (by norm_num)

theorem c22000E_77_4 : rowsJD 77 78 62 272 ≤ 223989087308576 :=
  rowsJD_le_of_splitJ 77 78 (by norm_num) (by norm_num) rows22000E_189 c22000E_77_5 (by norm_num)

theorem c22000E_77_3 : rowsJD 77 78 56 272 ≤ 299133959885216 :=
  rowsJD_le_of_splitJ 77 78 (by norm_num) (by norm_num) rows22000E_188 c22000E_77_4 (by norm_num)

theorem c22000E_77_2 : rowsJD 77 78 49 272 ≤ 384048953015318 :=
  rowsJD_le_of_splitJ 77 78 (by norm_num) (by norm_num) rows22000E_187 c22000E_77_3 (by norm_num)

theorem c22000E_77_1 : rowsJD 77 78 37 272 ≤ 545880097069518 :=
  rowsJD_le_of_splitJ 77 78 (by norm_num) (by norm_num) rows22000E_186 c22000E_77_2 (by norm_num)

theorem c22000E_77_0 : rowsJD 77 78 0 272 ≤ 774239154203553 :=
  rowsJD_le_of_splitJ 77 78 (by norm_num) (by norm_num) rows22000E_185 c22000E_77_1 (by norm_num)

theorem c22000E_78_5 : rowsJD 78 79 70 272 ≤ 142885961031488 :=
  rowsJD_le_of_splitJ 78 79 (by norm_num) (by norm_num) rows22000E_197 rows22000E_198 (by norm_num)

theorem c22000E_78_4 : rowsJD 78 79 62 272 ≤ 240277426054649 :=
  rowsJD_le_of_splitJ 78 79 (by norm_num) (by norm_num) rows22000E_196 c22000E_78_5 (by norm_num)

theorem c22000E_78_3 : rowsJD 78 79 56 272 ≤ 315722166877838 :=
  rowsJD_le_of_splitJ 78 79 (by norm_num) (by norm_num) rows22000E_195 c22000E_78_4 (by norm_num)

theorem c22000E_78_2 : rowsJD 78 79 49 272 ≤ 400876757498934 :=
  rowsJD_le_of_splitJ 78 79 (by norm_num) (by norm_num) rows22000E_194 c22000E_78_3 (by norm_num)

theorem c22000E_78_1 : rowsJD 78 79 37 272 ≤ 556666035718623 :=
  rowsJD_le_of_splitJ 78 79 (by norm_num) (by norm_num) rows22000E_193 c22000E_78_2 (by norm_num)

theorem c22000E_78_0 : rowsJD 78 79 0 272 ≤ 781619129672491 :=
  rowsJD_le_of_splitJ 78 79 (by norm_num) (by norm_num) rows22000E_192 c22000E_78_1 (by norm_num)

theorem c22000E_79_5 : rowsJD 79 80 71 272 ≤ 147283641294984 :=
  rowsJD_le_of_splitJ 79 80 (by norm_num) (by norm_num) rows22000E_204 rows22000E_205 (by norm_num)

theorem c22000E_79_4 : rowsJD 79 80 63 272 ≤ 244376359311296 :=
  rowsJD_le_of_splitJ 79 80 (by norm_num) (by norm_num) rows22000E_203 c22000E_79_5 (by norm_num)

theorem c22000E_79_3 : rowsJD 79 80 56 272 ≤ 331616891834416 :=
  rowsJD_le_of_splitJ 79 80 (by norm_num) (by norm_num) rows22000E_202 c22000E_79_4 (by norm_num)

theorem c22000E_79_2 : rowsJD 79 80 49 272 ≤ 416885014273827 :=
  rowsJD_le_of_splitJ 79 80 (by norm_num) (by norm_num) rows22000E_201 c22000E_79_3 (by norm_num)

theorem c22000E_79_1 : rowsJD 79 80 37 272 ≤ 566691870069263 :=
  rowsJD_le_of_splitJ 79 80 (by norm_num) (by norm_num) rows22000E_200 c22000E_79_2 (by norm_num)

theorem c22000E_79_0 : rowsJD 79 80 0 272 ≤ 788034093678682 :=
  rowsJD_le_of_splitJ 79 80 (by norm_num) (by norm_num) rows22000E_199 c22000E_79_1 (by norm_num)

theorem c22000E_80_6 : rowsJD 80 81 76 272 ≤ 98996136458616 :=
  rowsJD_le_of_splitJ 80 81 (by norm_num) (by norm_num) rows22000E_212 rows22000E_213 (by norm_num)

theorem c22000E_80_5 : rowsJD 80 81 71 272 ≤ 164715338356935 :=
  rowsJD_le_of_splitJ 80 81 (by norm_num) (by norm_num) rows22000E_211 c22000E_80_6 (by norm_num)

theorem c22000E_80_4 : rowsJD 80 81 63 272 ≤ 260956049038561 :=
  rowsJD_le_of_splitJ 80 81 (by norm_num) (by norm_num) rows22000E_210 c22000E_80_5 (by norm_num)

theorem c22000E_80_3 : rowsJD 80 81 56 272 ≤ 348650131123911 :=
  rowsJD_le_of_splitJ 80 81 (by norm_num) (by norm_num) rows22000E_209 c22000E_80_4 (by norm_num)

theorem c22000E_80_2 : rowsJD 80 81 49 272 ≤ 435588914949813 :=
  rowsJD_le_of_splitJ 80 81 (by norm_num) (by norm_num) rows22000E_208 c22000E_80_3 (by norm_num)

theorem c22000E_80_1 : rowsJD 80 81 37 272 ≤ 580984231051601 :=
  rowsJD_le_of_splitJ 80 81 (by norm_num) (by norm_num) rows22000E_207 c22000E_80_2 (by norm_num)

theorem c22000E_80_0 : rowsJD 80 81 0 272 ≤ 798640700724417 :=
  rowsJD_le_of_splitJ 80 81 (by norm_num) (by norm_num) rows22000E_206 c22000E_80_1 (by norm_num)

theorem c22000E_81_5 : rowsJD 81 82 71 272 ≤ 175403439999325 :=
  rowsJD_le_of_splitJ 81 82 (by norm_num) (by norm_num) rows22000E_219 rows22000E_220 (by norm_num)

theorem c22000E_81_4 : rowsJD 81 82 63 272 ≤ 270378508776436 :=
  rowsJD_le_of_splitJ 81 82 (by norm_num) (by norm_num) rows22000E_218 c22000E_81_5 (by norm_num)

theorem c22000E_81_3 : rowsJD 81 82 56 272 ≤ 357777355349628 :=
  rowsJD_le_of_splitJ 81 82 (by norm_num) (by norm_num) rows22000E_217 c22000E_81_4 (by norm_num)

theorem c22000E_81_2 : rowsJD 81 82 49 272 ≤ 446455165050145 :=
  rowsJD_le_of_splitJ 81 82 (by norm_num) (by norm_num) rows22000E_216 c22000E_81_3 (by norm_num)

theorem c22000E_81_1 : rowsJD 81 82 37 272 ≤ 587817073019709 :=
  rowsJD_le_of_splitJ 81 82 (by norm_num) (by norm_num) rows22000E_215 c22000E_81_2 (by norm_num)

theorem c22000E_81_0 : rowsJD 81 82 0 272 ≤ 801652493195566 :=
  rowsJD_le_of_splitJ 81 82 (by norm_num) (by norm_num) rows22000E_214 c22000E_81_1 (by norm_num)

theorem c22000E_82_6 : rowsJD 82 83 76 272 ≤ 129993890384826 :=
  rowsJD_le_of_splitJ 82 83 (by norm_num) (by norm_num) rows22000E_227 rows22000E_228 (by norm_num)

theorem c22000E_82_5 : rowsJD 82 83 70 272 ≤ 200523104900753 :=
  rowsJD_le_of_splitJ 82 83 (by norm_num) (by norm_num) rows22000E_226 c22000E_82_6 (by norm_num)

theorem c22000E_82_4 : rowsJD 82 83 62 272 ≤ 295519058369650 :=
  rowsJD_le_of_splitJ 82 83 (by norm_num) (by norm_num) rows22000E_225 c22000E_82_5 (by norm_num)

theorem c22000E_82_3 : rowsJD 82 83 55 272 ≤ 384284645318081 :=
  rowsJD_le_of_splitJ 82 83 (by norm_num) (by norm_num) rows22000E_224 c22000E_82_4 (by norm_num)

theorem c22000E_82_2 : rowsJD 82 83 48 272 ≤ 472989764932653 :=
  rowsJD_le_of_splitJ 82 83 (by norm_num) (by norm_num) rows22000E_223 c22000E_82_3 (by norm_num)

theorem c22000E_82_1 : rowsJD 82 83 37 272 ≤ 599030017400961 :=
  rowsJD_le_of_splitJ 82 83 (by norm_num) (by norm_num) rows22000E_222 c22000E_82_2 (by norm_num)

theorem c22000E_82_0 : rowsJD 82 83 0 272 ≤ 808970329861590 :=
  rowsJD_le_of_splitJ 82 83 (by norm_num) (by norm_num) rows22000E_221 c22000E_82_1 (by norm_num)

theorem c22000E_83_6 : rowsJD 83 84 77 272 ≤ 126454613784602 :=
  rowsJD_le_of_splitJ 83 84 (by norm_num) (by norm_num) rows22000E_235 rows22000E_236 (by norm_num)

theorem c22000E_83_5 : rowsJD 83 84 71 272 ≤ 196051095737644 :=
  rowsJD_le_of_splitJ 83 84 (by norm_num) (by norm_num) rows22000E_234 c22000E_83_6 (by norm_num)

theorem c22000E_83_4 : rowsJD 83 84 63 272 ≤ 288863231498482 :=
  rowsJD_le_of_splitJ 83 84 (by norm_num) (by norm_num) rows22000E_233 c22000E_83_5 (by norm_num)

theorem c22000E_83_3 : rowsJD 83 84 55 272 ≤ 388868684354079 :=
  rowsJD_le_of_splitJ 83 84 (by norm_num) (by norm_num) rows22000E_232 c22000E_83_4 (by norm_num)

theorem c22000E_83_2 : rowsJD 83 84 48 272 ≤ 479416735631999 :=
  rowsJD_le_of_splitJ 83 84 (by norm_num) (by norm_num) rows22000E_231 c22000E_83_3 (by norm_num)

theorem c22000E_83_1 : rowsJD 83 84 37 272 ≤ 602230572997880 :=
  rowsJD_le_of_splitJ 83 84 (by norm_num) (by norm_num) rows22000E_230 c22000E_83_2 (by norm_num)

theorem c22000E_83_0 : rowsJD 83 84 0 272 ≤ 807837671482127 :=
  rowsJD_le_of_splitJ 83 84 (by norm_num) (by norm_num) rows22000E_229 c22000E_83_1 (by norm_num)

theorem c22000E_84_6 : rowsJD 84 85 79 272 ≤ 105694514094543 :=
  rowsJD_le_of_splitJ 84 85 (by norm_num) (by norm_num) rows22000E_243 rows22000E_244 (by norm_num)

theorem c22000E_84_5 : rowsJD 84 85 73 272 ≤ 175444800616725 :=
  rowsJD_le_of_splitJ 84 85 (by norm_num) (by norm_num) rows22000E_242 c22000E_84_6 (by norm_num)

theorem c22000E_84_4 : rowsJD 84 85 65 272 ≤ 263572118727619 :=
  rowsJD_le_of_splitJ 84 85 (by norm_num) (by norm_num) rows22000E_241 c22000E_84_5 (by norm_num)

theorem c22000E_84_3 : rowsJD 84 85 56 272 ≤ 372766913328910 :=
  rowsJD_le_of_splitJ 84 85 (by norm_num) (by norm_num) rows22000E_240 c22000E_84_4 (by norm_num)

theorem c22000E_84_2 : rowsJD 84 85 49 272 ≤ 466427712958674 :=
  rowsJD_le_of_splitJ 84 85 (by norm_num) (by norm_num) rows22000E_239 c22000E_84_3 (by norm_num)

theorem c22000E_84_1 : rowsJD 84 85 38 272 ≤ 587141310287317 :=
  rowsJD_le_of_splitJ 84 85 (by norm_num) (by norm_num) rows22000E_238 c22000E_84_2 (by norm_num)

theorem c22000E_84_0 : rowsJD 84 85 0 272 ≤ 799828794413894 :=
  rowsJD_le_of_splitJ 84 85 (by norm_num) (by norm_num) rows22000E_237 c22000E_84_1 (by norm_num)

theorem c22000E_85_6 : rowsJD 85 86 79 272 ≤ 100361689454000 :=
  rowsJD_le_of_splitJ 85 86 (by norm_num) (by norm_num) rows22000E_251 rows22000E_252 (by norm_num)

theorem c22000E_85_5 : rowsJD 85 86 73 272 ≤ 163915251342735 :=
  rowsJD_le_of_splitJ 85 86 (by norm_num) (by norm_num) rows22000E_250 c22000E_85_6 (by norm_num)

theorem c22000E_85_4 : rowsJD 85 86 65 272 ≤ 250401027459668 :=
  rowsJD_le_of_splitJ 85 86 (by norm_num) (by norm_num) rows22000E_249 c22000E_85_5 (by norm_num)

theorem c22000E_85_3 : rowsJD 85 86 56 272 ≤ 358237998293757 :=
  rowsJD_le_of_splitJ 85 86 (by norm_num) (by norm_num) rows22000E_248 c22000E_85_4 (by norm_num)

theorem c22000E_85_2 : rowsJD 85 86 49 272 ≤ 452911222936339 :=
  rowsJD_le_of_splitJ 85 86 (by norm_num) (by norm_num) rows22000E_247 c22000E_85_3 (by norm_num)

theorem c22000E_85_1 : rowsJD 85 86 38 272 ≤ 571824851254228 :=
  rowsJD_le_of_splitJ 85 86 (by norm_num) (by norm_num) rows22000E_246 c22000E_85_2 (by norm_num)

theorem c22000E_85_0 : rowsJD 85 86 0 272 ≤ 779615678566609 :=
  rowsJD_le_of_splitJ 85 86 (by norm_num) (by norm_num) rows22000E_245 c22000E_85_1 (by norm_num)

theorem c22000E_86_6 : rowsJD 86 87 80 272 ≤ 82066677847439 :=
  rowsJD_le_of_splitJ 86 87 (by norm_num) (by norm_num) rows22000E_259 rows22000E_260 (by norm_num)

theorem c22000E_86_5 : rowsJD 86 87 73 272 ≤ 150844937659282 :=
  rowsJD_le_of_splitJ 86 87 (by norm_num) (by norm_num) rows22000E_258 c22000E_86_6 (by norm_num)

theorem c22000E_86_4 : rowsJD 86 87 65 272 ≤ 236172197915251 :=
  rowsJD_le_of_splitJ 86 87 (by norm_num) (by norm_num) rows22000E_257 c22000E_86_5 (by norm_num)

theorem c22000E_86_3 : rowsJD 86 87 56 272 ≤ 342965142611682 :=
  rowsJD_le_of_splitJ 86 87 (by norm_num) (by norm_num) rows22000E_256 c22000E_86_4 (by norm_num)

theorem c22000E_86_2 : rowsJD 86 87 49 272 ≤ 439019039139666 :=
  rowsJD_le_of_splitJ 86 87 (by norm_num) (by norm_num) rows22000E_255 c22000E_86_3 (by norm_num)

theorem c22000E_86_1 : rowsJD 86 87 38 272 ≤ 556611873483514 :=
  rowsJD_le_of_splitJ 86 87 (by norm_num) (by norm_num) rows22000E_254 c22000E_86_2 (by norm_num)

theorem c22000E_86_0 : rowsJD 86 87 0 272 ≤ 759489225152242 :=
  rowsJD_le_of_splitJ 86 87 (by norm_num) (by norm_num) rows22000E_253 c22000E_86_1 (by norm_num)

theorem c22000E_87_6 : rowsJD 87 88 81 272 ≤ 64187158138173 :=
  rowsJD_le_of_splitJ 87 88 (by norm_num) (by norm_num) rows22000E_267 rows22000E_268 (by norm_num)

theorem c22000E_87_5 : rowsJD 87 88 74 272 ≤ 126794018507994 :=
  rowsJD_le_of_splitJ 87 88 (by norm_num) (by norm_num) rows22000E_266 c22000E_87_6 (by norm_num)

theorem c22000E_87_4 : rowsJD 87 88 66 272 ≤ 206148753439719 :=
  rowsJD_le_of_splitJ 87 88 (by norm_num) (by norm_num) rows22000E_265 c22000E_87_5 (by norm_num)

theorem c22000E_87_3 : rowsJD 87 88 56 272 ≤ 325345075833154 :=
  rowsJD_le_of_splitJ 87 88 (by norm_num) (by norm_num) rows22000E_264 c22000E_87_4 (by norm_num)

theorem c22000E_87_2 : rowsJD 87 88 49 272 ≤ 422192443317568 :=
  rowsJD_le_of_splitJ 87 88 (by norm_num) (by norm_num) rows22000E_263 c22000E_87_3 (by norm_num)

theorem c22000E_87_1 : rowsJD 87 88 38 272 ≤ 538906526845124 :=
  rowsJD_le_of_splitJ 87 88 (by norm_num) (by norm_num) rows22000E_262 c22000E_87_2 (by norm_num)

theorem c22000E_87_0 : rowsJD 87 88 0 272 ≤ 736797379507916 :=
  rowsJD_le_of_splitJ 87 88 (by norm_num) (by norm_num) rows22000E_261 c22000E_87_1 (by norm_num)

theorem c22000E_88_6 : rowsJD 88 89 82 272 ≤ 55536048393147 :=
  rowsJD_le_of_splitJ 88 89 (by norm_num) (by norm_num) rows22000E_275 rows22000E_276 (by norm_num)

theorem c22000E_88_5 : rowsJD 88 89 75 272 ≤ 111809865682255 :=
  rowsJD_le_of_splitJ 88 89 (by norm_num) (by norm_num) rows22000E_274 c22000E_88_6 (by norm_num)

theorem c22000E_88_4 : rowsJD 88 89 67 272 ≤ 182579484486167 :=
  rowsJD_le_of_splitJ 88 89 (by norm_num) (by norm_num) rows22000E_273 c22000E_88_5 (by norm_num)

theorem c22000E_88_3 : rowsJD 88 89 57 272 ≤ 301794493451642 :=
  rowsJD_le_of_splitJ 88 89 (by norm_num) (by norm_num) rows22000E_272 c22000E_88_4 (by norm_num)

theorem c22000E_88_2 : rowsJD 88 89 49 272 ≤ 411421859462374 :=
  rowsJD_le_of_splitJ 88 89 (by norm_num) (by norm_num) rows22000E_271 c22000E_88_3 (by norm_num)

theorem c22000E_88_1 : rowsJD 88 89 38 272 ≤ 527435796653364 :=
  rowsJD_le_of_splitJ 88 89 (by norm_num) (by norm_num) rows22000E_270 c22000E_88_2 (by norm_num)

theorem c22000E_88_0 : rowsJD 88 89 0 272 ≤ 720489170019921 :=
  rowsJD_le_of_splitJ 88 89 (by norm_num) (by norm_num) rows22000E_269 c22000E_88_1 (by norm_num)

theorem c22000E_89_6 : rowsJD 89 90 83 272 ≤ 57790373586994 :=
  rowsJD_le_of_splitJ 89 90 (by norm_num) (by norm_num) rows22000E_283 rows22000E_284 (by norm_num)

theorem c22000E_89_5 : rowsJD 89 90 76 272 ≤ 103281285473074 :=
  rowsJD_le_of_splitJ 89 90 (by norm_num) (by norm_num) rows22000E_282 c22000E_89_6 (by norm_num)

theorem c22000E_89_4 : rowsJD 89 90 67 272 ≤ 176820479914336 :=
  rowsJD_le_of_splitJ 89 90 (by norm_num) (by norm_num) rows22000E_281 c22000E_89_5 (by norm_num)

theorem c22000E_89_3 : rowsJD 89 90 57 272 ≤ 295791212894140 :=
  rowsJD_le_of_splitJ 89 90 (by norm_num) (by norm_num) rows22000E_280 c22000E_89_4 (by norm_num)

theorem c22000E_89_2 : rowsJD 89 90 49 272 ≤ 404735972176869 :=
  rowsJD_le_of_splitJ 89 90 (by norm_num) (by norm_num) rows22000E_279 c22000E_89_3 (by norm_num)

theorem c22000E_89_1 : rowsJD 89 90 38 272 ≤ 520319127644025 :=
  rowsJD_le_of_splitJ 89 90 (by norm_num) (by norm_num) rows22000E_278 c22000E_89_2 (by norm_num)

theorem c22000E_89_0 : rowsJD 89 90 0 272 ≤ 708491078950820 :=
  rowsJD_le_of_splitJ 89 90 (by norm_num) (by norm_num) rows22000E_277 c22000E_89_1 (by norm_num)

theorem c22000E_90_6 : rowsJD 90 91 83 272 ≤ 81480410404232 :=
  rowsJD_le_of_splitJ 90 91 (by norm_num) (by norm_num) rows22000E_291 rows22000E_292 (by norm_num)

theorem c22000E_90_5 : rowsJD 90 91 76 272 ≤ 122784350083636 :=
  rowsJD_le_of_splitJ 90 91 (by norm_num) (by norm_num) rows22000E_290 c22000E_90_6 (by norm_num)

theorem c22000E_90_4 : rowsJD 90 91 67 272 ≤ 190885262062930 :=
  rowsJD_le_of_splitJ 90 91 (by norm_num) (by norm_num) rows22000E_289 c22000E_90_5 (by norm_num)

theorem c22000E_90_3 : rowsJD 90 91 57 272 ≤ 309348154511938 :=
  rowsJD_le_of_splitJ 90 91 (by norm_num) (by norm_num) rows22000E_288 c22000E_90_4 (by norm_num)

theorem c22000E_90_2 : rowsJD 90 91 49 272 ≤ 418284880612787 :=
  rowsJD_le_of_splitJ 90 91 (by norm_num) (by norm_num) rows22000E_287 c22000E_90_3 (by norm_num)

theorem c22000E_90_1 : rowsJD 90 91 38 272 ≤ 534298135005107 :=
  rowsJD_le_of_splitJ 90 91 (by norm_num) (by norm_num) rows22000E_286 c22000E_90_2 (by norm_num)

theorem c22000E_90_0 : rowsJD 90 91 0 272 ≤ 717743126016696 :=
  rowsJD_le_of_splitJ 90 91 (by norm_num) (by norm_num) rows22000E_285 c22000E_90_1 (by norm_num)

theorem c22000E_91_6 : rowsJD 91 92 84 272 ≤ 107267715232736 :=
  rowsJD_le_of_splitJ 91 92 (by norm_num) (by norm_num) rows22000E_299 rows22000E_300 (by norm_num)

theorem c22000E_91_5 : rowsJD 91 92 77 272 ≤ 142245999509577 :=
  rowsJD_le_of_splitJ 91 92 (by norm_num) (by norm_num) rows22000E_298 c22000E_91_6 (by norm_num)

theorem c22000E_91_4 : rowsJD 91 92 68 272 ≤ 201555194598856 :=
  rowsJD_le_of_splitJ 91 92 (by norm_num) (by norm_num) rows22000E_297 c22000E_91_5 (by norm_num)

theorem c22000E_91_3 : rowsJD 91 92 58 272 ≤ 317403546326063 :=
  rowsJD_le_of_splitJ 91 92 (by norm_num) (by norm_num) rows22000E_296 c22000E_91_4 (by norm_num)

theorem c22000E_91_2 : rowsJD 91 92 49 272 ≤ 436724959490460 :=
  rowsJD_le_of_splitJ 91 92 (by norm_num) (by norm_num) rows22000E_295 c22000E_91_3 (by norm_num)

theorem c22000E_91_1 : rowsJD 91 92 38 272 ≤ 553499579159089 :=
  rowsJD_le_of_splitJ 91 92 (by norm_num) (by norm_num) rows22000E_294 c22000E_91_2 (by norm_num)

theorem c22000E_91_0 : rowsJD 91 92 0 272 ≤ 731968108711697 :=
  rowsJD_le_of_splitJ 91 92 (by norm_num) (by norm_num) rows22000E_293 c22000E_91_1 (by norm_num)

theorem c22000E_92_6 : rowsJD 92 93 85 272 ≤ 134802582038880 :=
  rowsJD_le_of_splitJ 92 93 (by norm_num) (by norm_num) rows22000E_307 rows22000E_308 (by norm_num)

theorem c22000E_92_5 : rowsJD 92 93 78 272 ≤ 166167911152140 :=
  rowsJD_le_of_splitJ 92 93 (by norm_num) (by norm_num) rows22000E_306 c22000E_92_6 (by norm_num)

theorem c22000E_92_4 : rowsJD 92 93 69 272 ≤ 219164530738179 :=
  rowsJD_le_of_splitJ 92 93 (by norm_num) (by norm_num) rows22000E_305 c22000E_92_5 (by norm_num)

theorem c22000E_92_3 : rowsJD 92 93 58 272 ≤ 339609118716292 :=
  rowsJD_le_of_splitJ 92 93 (by norm_num) (by norm_num) rows22000E_304 c22000E_92_4 (by norm_num)

theorem c22000E_92_2 : rowsJD 92 93 49 272 ≤ 457539217287516 :=
  rowsJD_le_of_splitJ 92 93 (by norm_num) (by norm_num) rows22000E_303 c22000E_92_3 (by norm_num)

theorem c22000E_92_1 : rowsJD 92 93 38 272 ≤ 575542084144008 :=
  rowsJD_le_of_splitJ 92 93 (by norm_num) (by norm_num) rows22000E_302 c22000E_92_2 (by norm_num)

theorem c22000E_92_0 : rowsJD 92 93 0 272 ≤ 749210580122195 :=
  rowsJD_le_of_splitJ 92 93 (by norm_num) (by norm_num) rows22000E_301 c22000E_92_1 (by norm_num)

theorem c22000E_93_7 : rowsJD 93 94 90 272 ≤ 113035419259933 :=
  rowsJD_le_of_splitJ 93 94 (by norm_num) (by norm_num) rows22000E_316 rows22000E_317 (by norm_num)

theorem c22000E_93_6 : rowsJD 93 94 85 272 ≤ 166111345406332 :=
  rowsJD_le_of_splitJ 93 94 (by norm_num) (by norm_num) rows22000E_315 c22000E_93_7 (by norm_num)

theorem c22000E_93_5 : rowsJD 93 94 79 272 ≤ 189734039041017 :=
  rowsJD_le_of_splitJ 93 94 (by norm_num) (by norm_num) rows22000E_314 c22000E_93_6 (by norm_num)

theorem c22000E_93_4 : rowsJD 93 94 70 272 ≤ 240350413895049 :=
  rowsJD_le_of_splitJ 93 94 (by norm_num) (by norm_num) rows22000E_313 c22000E_93_5 (by norm_num)

theorem c22000E_93_3 : rowsJD 93 94 59 272 ≤ 351815512188054 :=
  rowsJD_le_of_splitJ 93 94 (by norm_num) (by norm_num) rows22000E_312 c22000E_93_4 (by norm_num)

theorem c22000E_93_2 : rowsJD 93 94 49 272 ≤ 477012816264593 :=
  rowsJD_le_of_splitJ 93 94 (by norm_num) (by norm_num) rows22000E_311 c22000E_93_3 (by norm_num)

theorem c22000E_93_1 : rowsJD 93 94 38 272 ≤ 596354576254673 :=
  rowsJD_le_of_splitJ 93 94 (by norm_num) (by norm_num) rows22000E_310 c22000E_93_2 (by norm_num)

theorem c22000E_93_0 : rowsJD 93 94 0 272 ≤ 765275367887884 :=
  rowsJD_le_of_splitJ 93 94 (by norm_num) (by norm_num) rows22000E_309 c22000E_93_1 (by norm_num)

theorem c22000E_94_7 : rowsJD 94 95 90 272 ≤ 147492968774569 :=
  rowsJD_le_of_splitJ 94 95 (by norm_num) (by norm_num) rows22000E_325 rows22000E_326 (by norm_num)

theorem c22000E_94_6 : rowsJD 94 95 85 272 ≤ 199900294321493 :=
  rowsJD_le_of_splitJ 94 95 (by norm_num) (by norm_num) rows22000E_324 c22000E_94_7 (by norm_num)

theorem c22000E_94_5 : rowsJD 94 95 79 272 ≤ 221246745510598 :=
  rowsJD_le_of_splitJ 94 95 (by norm_num) (by norm_num) rows22000E_323 c22000E_94_6 (by norm_num)

theorem c22000E_94_4 : rowsJD 94 95 70 272 ≤ 271514568834765 :=
  rowsJD_le_of_splitJ 94 95 (by norm_num) (by norm_num) rows22000E_322 c22000E_94_5 (by norm_num)

theorem c22000E_94_3 : rowsJD 94 95 59 272 ≤ 377735585410882 :=
  rowsJD_le_of_splitJ 94 95 (by norm_num) (by norm_num) rows22000E_321 c22000E_94_4 (by norm_num)

theorem c22000E_94_2 : rowsJD 94 95 49 272 ≤ 500350789602784 :=
  rowsJD_le_of_splitJ 94 95 (by norm_num) (by norm_num) rows22000E_320 c22000E_94_3 (by norm_num)

theorem c22000E_94_1 : rowsJD 94 95 38 272 ≤ 621794280010077 :=
  rowsJD_le_of_splitJ 94 95 (by norm_num) (by norm_num) rows22000E_319 c22000E_94_2 (by norm_num)

theorem c22000E_94_0 : rowsJD 94 95 0 272 ≤ 786140584399165 :=
  rowsJD_le_of_splitJ 94 95 (by norm_num) (by norm_num) rows22000E_318 c22000E_94_1 (by norm_num)

theorem c22000E_95_7 : rowsJD 95 96 90 272 ≤ 180277096981214 :=
  rowsJD_le_of_splitJ 95 96 (by norm_num) (by norm_num) rows22000E_334 rows22000E_335 (by norm_num)

theorem c22000E_95_6 : rowsJD 95 96 85 272 ≤ 233238307947691 :=
  rowsJD_le_of_splitJ 95 96 (by norm_num) (by norm_num) rows22000E_333 c22000E_95_7 (by norm_num)

theorem c22000E_95_5 : rowsJD 95 96 79 272 ≤ 252340478889941 :=
  rowsJD_le_of_splitJ 95 96 (by norm_num) (by norm_num) rows22000E_332 c22000E_95_6 (by norm_num)

theorem c22000E_95_4 : rowsJD 95 96 71 272 ≤ 297072835909948 :=
  rowsJD_le_of_splitJ 95 96 (by norm_num) (by norm_num) rows22000E_331 c22000E_95_5 (by norm_num)

theorem c22000E_95_3 : rowsJD 95 96 60 272 ≤ 394579004711192 :=
  rowsJD_le_of_splitJ 95 96 (by norm_num) (by norm_num) rows22000E_330 c22000E_95_4 (by norm_num)

theorem c22000E_95_2 : rowsJD 95 96 49 272 ≤ 524069641464784 :=
  rowsJD_le_of_splitJ 95 96 (by norm_num) (by norm_num) rows22000E_329 c22000E_95_3 (by norm_num)

theorem c22000E_95_1 : rowsJD 95 96 38 272 ≤ 647810800396081 :=
  rowsJD_le_of_splitJ 95 96 (by norm_num) (by norm_num) rows22000E_328 c22000E_95_2 (by norm_num)

theorem c22000E_95_0 : rowsJD 95 96 0 272 ≤ 807556910356157 :=
  rowsJD_le_of_splitJ 95 96 (by norm_num) (by norm_num) rows22000E_327 c22000E_95_1 (by norm_num)

theorem c22000E_96_8 : rowsJD 96 97 93 272 ≤ 148064713829590 :=
  rowsJD_le_of_splitJ 96 97 (by norm_num) (by norm_num) rows22000E_344 rows22000E_345 (by norm_num)

theorem c22000E_96_7 : rowsJD 96 97 90 272 ≤ 219370421610851 :=
  rowsJD_le_of_splitJ 96 97 (by norm_num) (by norm_num) rows22000E_343 c22000E_96_8 (by norm_num)

theorem c22000E_96_6 : rowsJD 96 97 86 272 ≤ 265586185952319 :=
  rowsJD_le_of_splitJ 96 97 (by norm_num) (by norm_num) rows22000E_342 c22000E_96_7 (by norm_num)

theorem c22000E_96_5 : rowsJD 96 97 80 272 ≤ 283752024157093 :=
  rowsJD_le_of_splitJ 96 97 (by norm_num) (by norm_num) rows22000E_341 c22000E_96_6 (by norm_num)

theorem c22000E_96_4 : rowsJD 96 97 72 272 ≤ 327698671881399 :=
  rowsJD_le_of_splitJ 96 97 (by norm_num) (by norm_num) rows22000E_340 c22000E_96_5 (by norm_num)

theorem c22000E_96_3 : rowsJD 96 97 61 272 ≤ 416888010015496 :=
  rowsJD_le_of_splitJ 96 97 (by norm_num) (by norm_num) rows22000E_339 c22000E_96_4 (by norm_num)

theorem c22000E_96_2 : rowsJD 96 97 49 272 ≤ 552549130039073 :=
  rowsJD_le_of_splitJ 96 97 (by norm_num) (by norm_num) rows22000E_338 c22000E_96_3 (by norm_num)

theorem c22000E_96_1 : rowsJD 96 97 38 272 ≤ 678768444289967 :=
  rowsJD_le_of_splitJ 96 97 (by norm_num) (by norm_num) rows22000E_337 c22000E_96_2 (by norm_num)

theorem c22000E_96_0 : rowsJD 96 97 0 272 ≤ 834141475377717 :=
  rowsJD_le_of_splitJ 96 97 (by norm_num) (by norm_num) rows22000E_336 c22000E_96_1 (by norm_num)

theorem c22000E_97_8 : rowsJD 97 98 94 272 ≤ 162783461528233 :=
  rowsJD_le_of_splitJ 97 98 (by norm_num) (by norm_num) rows22000E_354 rows22000E_355 (by norm_num)

theorem c22000E_97_7 : rowsJD 97 98 91 272 ≤ 242249443975977 :=
  rowsJD_le_of_splitJ 97 98 (by norm_num) (by norm_num) rows22000E_353 c22000E_97_8 (by norm_num)

theorem c22000E_97_6 : rowsJD 97 98 87 272 ≤ 298927228109376 :=
  rowsJD_le_of_splitJ 97 98 (by norm_num) (by norm_num) rows22000E_352 c22000E_97_7 (by norm_num)

theorem c22000E_97_5 : rowsJD 97 98 81 272 ≤ 319579578582326 :=
  rowsJD_le_of_splitJ 97 98 (by norm_num) (by norm_num) rows22000E_351 c22000E_97_6 (by norm_num)

theorem c22000E_97_4 : rowsJD 97 98 74 272 ≤ 354028215877952 :=
  rowsJD_le_of_splitJ 97 98 (by norm_num) (by norm_num) rows22000E_350 c22000E_97_5 (by norm_num)

theorem c22000E_97_3 : rowsJD 97 98 63 272 ≤ 434995382262043 :=
  rowsJD_le_of_splitJ 97 98 (by norm_num) (by norm_num) rows22000E_349 c22000E_97_4 (by norm_num)

theorem c22000E_97_2 : rowsJD 97 98 50 272 ≤ 567658480177721 :=
  rowsJD_le_of_splitJ 97 98 (by norm_num) (by norm_num) rows22000E_348 c22000E_97_3 (by norm_num)

theorem c22000E_97_1 : rowsJD 97 98 39 272 ≤ 702723998668191 :=
  rowsJD_le_of_splitJ 97 98 (by norm_num) (by norm_num) rows22000E_347 c22000E_97_2 (by norm_num)

theorem c22000E_97_0 : rowsJD 97 98 0 272 ≤ 860759121308808 :=
  rowsJD_le_of_splitJ 97 98 (by norm_num) (by norm_num) rows22000E_346 c22000E_97_1 (by norm_num)

theorem c22000E_98_8 : rowsJD 98 99 94 272 ≤ 212545269988852 :=
  rowsJD_le_of_splitJ 98 99 (by norm_num) (by norm_num) rows22000E_364 rows22000E_365 (by norm_num)

theorem c22000E_98_7 : rowsJD 98 99 91 272 ≤ 289784538922115 :=
  rowsJD_le_of_splitJ 98 99 (by norm_num) (by norm_num) rows22000E_363 c22000E_98_8 (by norm_num)

theorem c22000E_98_6 : rowsJD 98 99 87 272 ≤ 344517484695391 :=
  rowsJD_le_of_splitJ 98 99 (by norm_num) (by norm_num) rows22000E_362 c22000E_98_7 (by norm_num)

theorem c22000E_98_5 : rowsJD 98 99 81 272 ≤ 364219301933065 :=
  rowsJD_le_of_splitJ 98 99 (by norm_num) (by norm_num) rows22000E_361 c22000E_98_6 (by norm_num)

theorem c22000E_98_4 : rowsJD 98 99 73 272 ≤ 406048898308530 :=
  rowsJD_le_of_splitJ 98 99 (by norm_num) (by norm_num) rows22000E_360 c22000E_98_5 (by norm_num)

theorem c22000E_98_3 : rowsJD 98 99 63 272 ≤ 478667334237164 :=
  rowsJD_le_of_splitJ 98 99 (by norm_num) (by norm_num) rows22000E_359 c22000E_98_4 (by norm_num)

theorem c22000E_98_2 : rowsJD 98 99 50 272 ≤ 605213155434924 :=
  rowsJD_le_of_splitJ 98 99 (by norm_num) (by norm_num) rows22000E_358 c22000E_98_3 (by norm_num)

theorem c22000E_98_1 : rowsJD 98 99 39 272 ≤ 741989040867960 :=
  rowsJD_le_of_splitJ 98 99 (by norm_num) (by norm_num) rows22000E_357 c22000E_98_2 (by norm_num)

theorem c22000E_98_0 : rowsJD 98 99 0 272 ≤ 896035907798649 :=
  rowsJD_le_of_splitJ 98 99 (by norm_num) (by norm_num) rows22000E_356 c22000E_98_1 (by norm_num)

theorem c22000E_99_8 : rowsJD 99 100 95 272 ≤ 230169954621346 :=
  rowsJD_le_of_splitJ 99 100 (by norm_num) (by norm_num) rows22000E_374 rows22000E_375 (by norm_num)

theorem c22000E_99_7 : rowsJD 99 100 91 272 ≤ 339060720229334 :=
  rowsJD_le_of_splitJ 99 100 (by norm_num) (by norm_num) rows22000E_373 c22000E_99_8 (by norm_num)

theorem c22000E_99_6 : rowsJD 99 100 87 272 ≤ 392108378395589 :=
  rowsJD_le_of_splitJ 99 100 (by norm_num) (by norm_num) rows22000E_372 c22000E_99_7 (by norm_num)

theorem c22000E_99_5 : rowsJD 99 100 81 272 ≤ 411865128475347 :=
  rowsJD_le_of_splitJ 99 100 (by norm_num) (by norm_num) rows22000E_371 c22000E_99_6 (by norm_num)

theorem c22000E_99_4 : rowsJD 99 100 74 272 ≤ 446141816051540 :=
  rowsJD_le_of_splitJ 99 100 (by norm_num) (by norm_num) rows22000E_370 c22000E_99_5 (by norm_num)

theorem c22000E_99_3 : rowsJD 99 100 64 272 ≤ 519656549214529 :=
  rowsJD_le_of_splitJ 99 100 (by norm_num) (by norm_num) rows22000E_369 c22000E_99_4 (by norm_num)

theorem c22000E_99_2 : rowsJD 99 100 50 272 ≤ 647807734797191 :=
  rowsJD_le_of_splitJ 99 100 (by norm_num) (by norm_num) rows22000E_368 c22000E_99_3 (by norm_num)

theorem c22000E_99_1 : rowsJD 99 100 39 272 ≤ 790381097976804 :=
  rowsJD_le_of_splitJ 99 100 (by norm_num) (by norm_num) rows22000E_367 c22000E_99_2 (by norm_num)

theorem c22000E_99_0 : rowsJD 99 100 0 272 ≤ 942305679030566 :=
  rowsJD_le_of_splitJ 99 100 (by norm_num) (by norm_num) rows22000E_366 c22000E_99_1 (by norm_num)

theorem c22000E_100_8 : rowsJD 100 101 95 272 ≤ 283333246475330 :=
  rowsJD_le_of_splitJ 100 101 (by norm_num) (by norm_num) rows22000E_384 rows22000E_385 (by norm_num)

theorem c22000E_100_7 : rowsJD 100 101 91 272 ≤ 388705762197818 :=
  rowsJD_le_of_splitJ 100 101 (by norm_num) (by norm_num) rows22000E_383 c22000E_100_8 (by norm_num)

theorem c22000E_100_6 : rowsJD 100 101 87 272 ≤ 439462144726336 :=
  rowsJD_le_of_splitJ 100 101 (by norm_num) (by norm_num) rows22000E_382 c22000E_100_7 (by norm_num)

theorem c22000E_100_5 : rowsJD 100 101 81 272 ≤ 459715079877697 :=
  rowsJD_le_of_splitJ 100 101 (by norm_num) (by norm_num) rows22000E_381 c22000E_100_6 (by norm_num)

theorem c22000E_100_4 : rowsJD 100 101 74 272 ≤ 492889275835183 :=
  rowsJD_le_of_splitJ 100 101 (by norm_num) (by norm_num) rows22000E_380 c22000E_100_5 (by norm_num)

theorem c22000E_100_3 : rowsJD 100 101 65 272 ≤ 560269530403380 :=
  rowsJD_le_of_splitJ 100 101 (by norm_num) (by norm_num) rows22000E_379 c22000E_100_4 (by norm_num)

theorem c22000E_100_2 : rowsJD 100 101 51 272 ≤ 678272328089643 :=
  rowsJD_le_of_splitJ 100 101 (by norm_num) (by norm_num) rows22000E_378 c22000E_100_3 (by norm_num)

theorem c22000E_100_1 : rowsJD 100 101 39 272 ≤ 839320419769568 :=
  rowsJD_le_of_splitJ 100 101 (by norm_num) (by norm_num) rows22000E_377 c22000E_100_2 (by norm_num)

theorem c22000E_100_0 : rowsJD 100 101 0 272 ≤ 990321544199844 :=
  rowsJD_le_of_splitJ 100 101 (by norm_num) (by norm_num) rows22000E_376 c22000E_100_1 (by norm_num)

theorem c22000E_101_9 : rowsJD 101 102 98 272 ≤ 218284728111531 :=
  rowsJD_le_of_splitJ 101 102 (by norm_num) (by norm_num) rows22000E_395 rows22000E_396 (by norm_num)

theorem c22000E_101_8 : rowsJD 101 102 95 272 ≤ 335244280205737 :=
  rowsJD_le_of_splitJ 101 102 (by norm_num) (by norm_num) rows22000E_394 c22000E_101_9 (by norm_num)

theorem c22000E_101_7 : rowsJD 101 102 91 272 ≤ 436132935233525 :=
  rowsJD_le_of_splitJ 101 102 (by norm_num) (by norm_num) rows22000E_393 c22000E_101_8 (by norm_num)

theorem c22000E_101_6 : rowsJD 101 102 87 272 ≤ 484764621871171 :=
  rowsJD_le_of_splitJ 101 102 (by norm_num) (by norm_num) rows22000E_392 c22000E_101_7 (by norm_num)

theorem c22000E_101_5 : rowsJD 101 102 81 272 ≤ 506949424505571 :=
  rowsJD_le_of_splitJ 101 102 (by norm_num) (by norm_num) rows22000E_391 c22000E_101_6 (by norm_num)

theorem c22000E_101_4 : rowsJD 101 102 74 272 ≤ 537698546571179 :=
  rowsJD_le_of_splitJ 101 102 (by norm_num) (by norm_num) rows22000E_390 c22000E_101_5 (by norm_num)

theorem c22000E_101_3 : rowsJD 101 102 65 272 ≤ 604779837247769 :=
  rowsJD_le_of_splitJ 101 102 (by norm_num) (by norm_num) rows22000E_389 c22000E_101_4 (by norm_num)

theorem c22000E_101_2 : rowsJD 101 102 51 272 ≤ 721532887216849 :=
  rowsJD_le_of_splitJ 101 102 (by norm_num) (by norm_num) rows22000E_388 c22000E_101_3 (by norm_num)

theorem c22000E_101_1 : rowsJD 101 102 39 272 ≤ 886776668631013 :=
  rowsJD_le_of_splitJ 101 102 (by norm_num) (by norm_num) rows22000E_387 c22000E_101_2 (by norm_num)

theorem c22000E_101_0 : rowsJD 101 102 0 272 ≤ 1037723593300154 :=
  rowsJD_le_of_splitJ 101 102 (by norm_num) (by norm_num) rows22000E_386 c22000E_101_1 (by norm_num)

theorem c22000E_102_9 : rowsJD 102 103 98 272 ≤ 274380147814761 :=
  rowsJD_le_of_splitJ 102 103 (by norm_num) (by norm_num) rows22000E_406 rows22000E_407 (by norm_num)

theorem c22000E_102_8 : rowsJD 102 103 95 272 ≤ 386786535632341 :=
  rowsJD_le_of_splitJ 102 103 (by norm_num) (by norm_num) rows22000E_405 c22000E_102_9 (by norm_num)

theorem c22000E_102_7 : rowsJD 102 103 91 272 ≤ 483276479872474 :=
  rowsJD_le_of_splitJ 102 103 (by norm_num) (by norm_num) rows22000E_404 c22000E_102_8 (by norm_num)

theorem c22000E_102_6 : rowsJD 102 103 87 272 ≤ 529113017794462 :=
  rowsJD_le_of_splitJ 102 103 (by norm_num) (by norm_num) rows22000E_403 c22000E_102_7 (by norm_num)

theorem c22000E_102_5 : rowsJD 102 103 81 272 ≤ 553893272868543 :=
  rowsJD_le_of_splitJ 102 103 (by norm_num) (by norm_num) rows22000E_402 c22000E_102_6 (by norm_num)

theorem c22000E_102_4 : rowsJD 102 103 74 272 ≤ 581845723059269 :=
  rowsJD_le_of_splitJ 102 103 (by norm_num) (by norm_num) rows22000E_401 c22000E_102_5 (by norm_num)

theorem c22000E_102_3 : rowsJD 102 103 66 272 ≤ 641300675958645 :=
  rowsJD_le_of_splitJ 102 103 (by norm_num) (by norm_num) rows22000E_400 c22000E_102_4 (by norm_num)

theorem c22000E_102_2 : rowsJD 102 103 52 272 ≤ 754268350370478 :=
  rowsJD_le_of_splitJ 102 103 (by norm_num) (by norm_num) rows22000E_399 c22000E_102_3 (by norm_num)

theorem c22000E_102_1 : rowsJD 102 103 39 272 ≤ 934071332834063 :=
  rowsJD_le_of_splitJ 102 103 (by norm_num) (by norm_num) rows22000E_398 c22000E_102_2 (by norm_num)

theorem c22000E_102_0 : rowsJD 102 103 0 272 ≤ 1085694732683205 :=
  rowsJD_le_of_splitJ 102 103 (by norm_num) (by norm_num) rows22000E_397 c22000E_102_1 (by norm_num)

theorem c22000E_103_9 : rowsJD 103 104 100 272 ≤ 233954931590726 :=
  rowsJD_le_of_splitJ 103 104 (by norm_num) (by norm_num) rows22000E_417 rows22000E_418 (by norm_num)

theorem c22000E_103_8 : rowsJD 103 104 97 272 ≤ 367038254347156 :=
  rowsJD_le_of_splitJ 103 104 (by norm_num) (by norm_num) rows22000E_416 c22000E_103_9 (by norm_num)

theorem c22000E_103_7 : rowsJD 103 104 93 272 ≤ 487833932398037 :=
  rowsJD_le_of_splitJ 103 104 (by norm_num) (by norm_num) rows22000E_415 c22000E_103_8 (by norm_num)

theorem c22000E_103_6 : rowsJD 103 104 89 272 ≤ 553081514689622 :=
  rowsJD_le_of_splitJ 103 104 (by norm_num) (by norm_num) rows22000E_414 c22000E_103_7 (by norm_num)

theorem c22000E_103_5 : rowsJD 103 104 83 272 ≤ 594016225160340 :=
  rowsJD_le_of_splitJ 103 104 (by norm_num) (by norm_num) rows22000E_413 c22000E_103_6 (by norm_num)

theorem c22000E_103_4 : rowsJD 103 104 75 272 ≤ 619019364532313 :=
  rowsJD_le_of_splitJ 103 104 (by norm_num) (by norm_num) rows22000E_412 c22000E_103_5 (by norm_num)

theorem c22000E_103_3 : rowsJD 103 104 67 272 ≤ 675819279657059 :=
  rowsJD_le_of_splitJ 103 104 (by norm_num) (by norm_num) rows22000E_411 c22000E_103_4 (by norm_num)

theorem c22000E_103_2 : rowsJD 103 104 52 272 ≤ 795894665465248 :=
  rowsJD_le_of_splitJ 103 104 (by norm_num) (by norm_num) rows22000E_410 c22000E_103_3 (by norm_num)

theorem c22000E_103_1 : rowsJD 103 104 39 272 ≤ 971864432089653 :=
  rowsJD_le_of_splitJ 103 104 (by norm_num) (by norm_num) rows22000E_409 c22000E_103_2 (by norm_num)

theorem c22000E_103_0 : rowsJD 103 104 0 272 ≤ 1121694758301864 :=
  rowsJD_le_of_splitJ 103 104 (by norm_num) (by norm_num) rows22000E_408 c22000E_103_1 (by norm_num)

theorem c22000E_104_9 : rowsJD 104 105 100 272 ≤ 291832911723192 :=
  rowsJD_le_of_splitJ 104 105 (by norm_num) (by norm_num) rows22000E_428 rows22000E_429 (by norm_num)

theorem c22000E_104_8 : rowsJD 104 105 97 272 ≤ 418526854433187 :=
  rowsJD_le_of_splitJ 104 105 (by norm_num) (by norm_num) rows22000E_427 c22000E_104_9 (by norm_num)

theorem c22000E_104_7 : rowsJD 104 105 93 272 ≤ 534702513308684 :=
  rowsJD_le_of_splitJ 104 105 (by norm_num) (by norm_num) rows22000E_426 c22000E_104_8 (by norm_num)

theorem c22000E_104_6 : rowsJD 104 105 89 272 ≤ 596065380804578 :=
  rowsJD_le_of_splitJ 104 105 (by norm_num) (by norm_num) rows22000E_425 c22000E_104_7 (by norm_num)

theorem c22000E_104_5 : rowsJD 104 105 83 272 ≤ 640141167883193 :=
  rowsJD_le_of_splitJ 104 105 (by norm_num) (by norm_num) rows22000E_424 c22000E_104_6 (by norm_num)

theorem c22000E_104_4 : rowsJD 104 105 75 272 ≤ 666102735666023 :=
  rowsJD_le_of_splitJ 104 105 (by norm_num) (by norm_num) rows22000E_423 c22000E_104_5 (by norm_num)

theorem c22000E_104_3 : rowsJD 104 105 67 272 ≤ 722454365841436 :=
  rowsJD_le_of_splitJ 104 105 (by norm_num) (by norm_num) rows22000E_422 c22000E_104_4 (by norm_num)

theorem c22000E_104_2 : rowsJD 104 105 53 272 ≤ 834379764909689 :=
  rowsJD_le_of_splitJ 104 105 (by norm_num) (by norm_num) rows22000E_421 c22000E_104_3 (by norm_num)

theorem c22000E_104_1 : rowsJD 104 105 39 272 ≤ 1010556712996496 :=
  rowsJD_le_of_splitJ 104 105 (by norm_num) (by norm_num) rows22000E_420 c22000E_104_2 (by norm_num)

theorem c22000E_104_0 : rowsJD 104 105 0 272 ≤ 1156113786427734 :=
  rowsJD_le_of_splitJ 104 105 (by norm_num) (by norm_num) rows22000E_419 c22000E_104_1 (by norm_num)

theorem c22000E_105_9 : rowsJD 105 106 102 272 ≤ 250119046818657 :=
  rowsJD_le_of_splitJ 105 106 (by norm_num) (by norm_num) rows22000E_439 rows22000E_440 (by norm_num)

theorem c22000E_105_8 : rowsJD 105 106 98 272 ≤ 432836540842940 :=
  rowsJD_le_of_splitJ 105 106 (by norm_num) (by norm_num) rows22000E_438 c22000E_105_9 (by norm_num)

theorem c22000E_105_7 : rowsJD 105 106 94 272 ≤ 558606356520254 :=
  rowsJD_le_of_splitJ 105 106 (by norm_num) (by norm_num) rows22000E_437 c22000E_105_8 (by norm_num)

theorem c22000E_105_6 : rowsJD 105 106 89 272 ≤ 639935446961298 :=
  rowsJD_le_of_splitJ 105 106 (by norm_num) (by norm_num) rows22000E_436 c22000E_105_7 (by norm_num)

theorem c22000E_105_5 : rowsJD 105 106 83 272 ≤ 683718743038585 :=
  rowsJD_le_of_splitJ 105 106 (by norm_num) (by norm_num) rows22000E_435 c22000E_105_6 (by norm_num)

theorem c22000E_105_4 : rowsJD 105 106 75 272 ≤ 709939239785256 :=
  rowsJD_le_of_splitJ 105 106 (by norm_num) (by norm_num) rows22000E_434 c22000E_105_5 (by norm_num)

theorem c22000E_105_3 : rowsJD 105 106 67 272 ≤ 763569043726124 :=
  rowsJD_le_of_splitJ 105 106 (by norm_num) (by norm_num) rows22000E_433 c22000E_105_4 (by norm_num)

theorem c22000E_105_2 : rowsJD 105 106 53 272 ≤ 874390798797838 :=
  rowsJD_le_of_splitJ 105 106 (by norm_num) (by norm_num) rows22000E_432 c22000E_105_3 (by norm_num)

theorem c22000E_105_1 : rowsJD 105 106 39 272 ≤ 1040172958661262 :=
  rowsJD_le_of_splitJ 105 106 (by norm_num) (by norm_num) rows22000E_431 c22000E_105_2 (by norm_num)

theorem c22000E_105_0 : rowsJD 105 106 0 272 ≤ 1181159647569489 :=
  rowsJD_le_of_splitJ 105 106 (by norm_num) (by norm_num) rows22000E_430 c22000E_105_1 (by norm_num)

theorem c22000E_106_9 : rowsJD 106 107 103 272 ≤ 258708727762626 :=
  rowsJD_le_of_splitJ 106 107 (by norm_num) (by norm_num) rows22000E_450 rows22000E_451 (by norm_num)

theorem c22000E_106_8 : rowsJD 106 107 99 272 ≤ 447747661907759 :=
  rowsJD_le_of_splitJ 106 107 (by norm_num) (by norm_num) rows22000E_449 c22000E_106_9 (by norm_num)

theorem c22000E_106_7 : rowsJD 106 107 95 272 ≤ 581480367062275 :=
  rowsJD_le_of_splitJ 106 107 (by norm_num) (by norm_num) rows22000E_448 c22000E_106_8 (by norm_num)

theorem c22000E_106_6 : rowsJD 106 107 90 272 ≤ 674844462736572 :=
  rowsJD_le_of_splitJ 106 107 (by norm_num) (by norm_num) rows22000E_447 c22000E_106_7 (by norm_num)

theorem c22000E_106_5 : rowsJD 106 107 84 272 ≤ 722259360593087 :=
  rowsJD_le_of_splitJ 106 107 (by norm_num) (by norm_num) rows22000E_446 c22000E_106_6 (by norm_num)

theorem c22000E_106_4 : rowsJD 106 107 76 272 ≤ 750944803312045 :=
  rowsJD_le_of_splitJ 106 107 (by norm_num) (by norm_num) rows22000E_445 c22000E_106_5 (by norm_num)

theorem c22000E_106_3 : rowsJD 106 107 68 272 ≤ 798098120657203 :=
  rowsJD_le_of_splitJ 106 107 (by norm_num) (by norm_num) rows22000E_444 c22000E_106_4 (by norm_num)

theorem c22000E_106_2 : rowsJD 106 107 54 272 ≤ 908037182270316 :=
  rowsJD_le_of_splitJ 106 107 (by norm_num) (by norm_num) rows22000E_443 c22000E_106_3 (by norm_num)

theorem c22000E_106_1 : rowsJD 106 107 39 272 ≤ 1071148763213194 :=
  rowsJD_le_of_splitJ 106 107 (by norm_num) (by norm_num) rows22000E_442 c22000E_106_2 (by norm_num)

theorem c22000E_106_0 : rowsJD 106 107 0 272 ≤ 1207474079067716 :=
  rowsJD_le_of_splitJ 106 107 (by norm_num) (by norm_num) rows22000E_441 c22000E_106_1 (by norm_num)

theorem c22000E_107_9 : rowsJD 107 108 103 272 ≤ 246929344734703 :=
  rowsJD_le_of_splitJ 107 108 (by norm_num) (by norm_num) rows22000E_461 rows22000E_462 (by norm_num)

theorem c22000E_107_8 : rowsJD 107 108 99 272 ≤ 427091990756906 :=
  rowsJD_le_of_splitJ 107 108 (by norm_num) (by norm_num) rows22000E_460 c22000E_107_9 (by norm_num)

theorem c22000E_107_7 : rowsJD 107 108 95 272 ≤ 553930345314228 :=
  rowsJD_le_of_splitJ 107 108 (by norm_num) (by norm_num) rows22000E_459 c22000E_107_8 (by norm_num)

theorem c22000E_107_6 : rowsJD 107 108 90 272 ≤ 642693333920286 :=
  rowsJD_le_of_splitJ 107 108 (by norm_num) (by norm_num) rows22000E_458 c22000E_107_7 (by norm_num)

theorem c22000E_107_5 : rowsJD 107 108 84 272 ≤ 688911725197644 :=
  rowsJD_le_of_splitJ 107 108 (by norm_num) (by norm_num) rows22000E_457 c22000E_107_6 (by norm_num)

theorem c22000E_107_4 : rowsJD 107 108 76 272 ≤ 719656981686461 :=
  rowsJD_le_of_splitJ 107 108 (by norm_num) (by norm_num) rows22000E_456 c22000E_107_5 (by norm_num)

theorem c22000E_107_3 : rowsJD 107 108 68 272 ≤ 764644639772244 :=
  rowsJD_le_of_splitJ 107 108 (by norm_num) (by norm_num) rows22000E_455 c22000E_107_4 (by norm_num)

theorem c22000E_107_2 : rowsJD 107 108 54 272 ≤ 873451321340643 :=
  rowsJD_le_of_splitJ 107 108 (by norm_num) (by norm_num) rows22000E_454 c22000E_107_3 (by norm_num)

theorem c22000E_107_1 : rowsJD 107 108 39 272 ≤ 1025655032289120 :=
  rowsJD_le_of_splitJ 107 108 (by norm_num) (by norm_num) rows22000E_453 c22000E_107_2 (by norm_num)

theorem c22000E_107_0 : rowsJD 107 108 0 272 ≤ 1156932052084626 :=
  rowsJD_le_of_splitJ 107 108 (by norm_num) (by norm_num) rows22000E_452 c22000E_107_1 (by norm_num)

theorem c22000E_108_8 : rowsJD 108 109 100 272 ≤ 304007669493223 :=
  rowsJD_le_of_splitJ 108 109 (by norm_num) (by norm_num) rows22000E_471 rows22000E_472 (by norm_num)

theorem c22000E_108_7 : rowsJD 108 109 96 272 ≤ 435632366770994 :=
  rowsJD_le_of_splitJ 108 109 (by norm_num) (by norm_num) rows22000E_470 c22000E_108_8 (by norm_num)

theorem c22000E_108_6 : rowsJD 108 109 91 272 ≤ 533000562792775 :=
  rowsJD_le_of_splitJ 108 109 (by norm_num) (by norm_num) rows22000E_469 c22000E_108_7 (by norm_num)

theorem c22000E_108_5 : rowsJD 108 109 85 272 ≤ 580903023481119 :=
  rowsJD_le_of_splitJ 108 109 (by norm_num) (by norm_num) rows22000E_468 c22000E_108_6 (by norm_num)

theorem c22000E_108_4 : rowsJD 108 109 77 272 ≤ 617973549583057 :=
  rowsJD_le_of_splitJ 108 109 (by norm_num) (by norm_num) rows22000E_467 c22000E_108_5 (by norm_num)

theorem c22000E_108_3 : rowsJD 108 109 69 272 ≤ 657076852611035 :=
  rowsJD_le_of_splitJ 108 109 (by norm_num) (by norm_num) rows22000E_466 c22000E_108_4 (by norm_num)

theorem c22000E_108_2 : rowsJD 108 109 57 272 ≤ 751545681869389 :=
  rowsJD_le_of_splitJ 108 109 (by norm_num) (by norm_num) rows22000E_465 c22000E_108_3 (by norm_num)

theorem c22000E_108_1 : rowsJD 108 109 40 272 ≤ 911766077294082 :=
  rowsJD_le_of_splitJ 108 109 (by norm_num) (by norm_num) rows22000E_464 c22000E_108_2 (by norm_num)

theorem c22000E_108_0 : rowsJD 108 109 0 272 ≤ 1057322445123154 :=
  rowsJD_le_of_splitJ 108 109 (by norm_num) (by norm_num) rows22000E_463 c22000E_108_1 (by norm_num)

theorem c22000E_109_7 : rowsJD 109 110 97 272 ≤ 328892332211592 :=
  rowsJD_le_of_splitJ 109 110 (by norm_num) (by norm_num) rows22000E_480 rows22000E_481 (by norm_num)

theorem c22000E_109_6 : rowsJD 109 110 92 272 ≤ 432990203098465 :=
  rowsJD_le_of_splitJ 109 110 (by norm_num) (by norm_num) rows22000E_479 c22000E_109_7 (by norm_num)

theorem c22000E_109_5 : rowsJD 109 110 86 272 ≤ 487012561181210 :=
  rowsJD_le_of_splitJ 109 110 (by norm_num) (by norm_num) rows22000E_478 c22000E_109_6 (by norm_num)

theorem c22000E_109_4 : rowsJD 109 110 78 272 ≤ 532713317126664 :=
  rowsJD_le_of_splitJ 109 110 (by norm_num) (by norm_num) rows22000E_477 c22000E_109_5 (by norm_num)

theorem c22000E_109_3 : rowsJD 109 110 69 272 ≤ 575693170459010 :=
  rowsJD_le_of_splitJ 109 110 (by norm_num) (by norm_num) rows22000E_476 c22000E_109_4 (by norm_num)

theorem c22000E_109_2 : rowsJD 109 110 57 272 ≤ 679488606271658 :=
  rowsJD_le_of_splitJ 109 110 (by norm_num) (by norm_num) rows22000E_475 c22000E_109_3 (by norm_num)

theorem c22000E_109_1 : rowsJD 109 110 40 272 ≤ 836640489627163 :=
  rowsJD_le_of_splitJ 109 110 (by norm_num) (by norm_num) rows22000E_474 c22000E_109_2 (by norm_num)

theorem c22000E_109_0 : rowsJD 109 110 0 272 ≤ 986020042008384 :=
  rowsJD_le_of_splitJ 109 110 (by norm_num) (by norm_num) rows22000E_473 c22000E_109_1 (by norm_num)

theorem c22000E_110_7 : rowsJD 110 111 97 272 ≤ 263016578999743 :=
  rowsJD_le_of_splitJ 110 111 (by norm_num) (by norm_num) rows22000E_489 rows22000E_490 (by norm_num)

theorem c22000E_110_6 : rowsJD 110 111 92 272 ≤ 361072485134216 :=
  rowsJD_le_of_splitJ 110 111 (by norm_num) (by norm_num) rows22000E_488 c22000E_110_7 (by norm_num)

theorem c22000E_110_5 : rowsJD 110 111 86 272 ≤ 417346818352496 :=
  rowsJD_le_of_splitJ 110 111 (by norm_num) (by norm_num) rows22000E_487 c22000E_110_6 (by norm_num)

theorem c22000E_110_4 : rowsJD 110 111 78 272 ≤ 469181589793260 :=
  rowsJD_le_of_splitJ 110 111 (by norm_num) (by norm_num) rows22000E_486 c22000E_110_5 (by norm_num)

theorem c22000E_110_3 : rowsJD 110 111 69 272 ≤ 515908111068491 :=
  rowsJD_le_of_splitJ 110 111 (by norm_num) (by norm_num) rows22000E_485 c22000E_110_4 (by norm_num)

theorem c22000E_110_2 : rowsJD 110 111 58 272 ≤ 623501087750039 :=
  rowsJD_le_of_splitJ 110 111 (by norm_num) (by norm_num) rows22000E_484 c22000E_110_3 (by norm_num)

theorem c22000E_110_1 : rowsJD 110 111 40 272 ≤ 784148438371865 :=
  rowsJD_le_of_splitJ 110 111 (by norm_num) (by norm_num) rows22000E_483 c22000E_110_2 (by norm_num)

theorem c22000E_110_0 : rowsJD 110 111 0 272 ≤ 936593147316404 :=
  rowsJD_le_of_splitJ 110 111 (by norm_num) (by norm_num) rows22000E_482 c22000E_110_1 (by norm_num)

theorem c22000E_111_7 : rowsJD 111 112 98 272 ≤ 179891660955638 :=
  rowsJD_le_of_splitJ 111 112 (by norm_num) (by norm_num) rows22000E_498 rows22000E_499 (by norm_num)

theorem c22000E_111_6 : rowsJD 111 112 93 272 ≤ 287858854302003 :=
  rowsJD_le_of_splitJ 111 112 (by norm_num) (by norm_num) rows22000E_497 c22000E_111_7 (by norm_num)

theorem c22000E_111_5 : rowsJD 111 112 87 272 ≤ 355359330405693 :=
  rowsJD_le_of_splitJ 111 112 (by norm_num) (by norm_num) rows22000E_496 c22000E_111_6 (by norm_num)

theorem c22000E_111_4 : rowsJD 111 112 80 272 ≤ 417707403644260 :=
  rowsJD_le_of_splitJ 111 112 (by norm_num) (by norm_num) rows22000E_495 c22000E_111_5 (by norm_num)

theorem c22000E_111_3 : rowsJD 111 112 70 272 ≤ 467885269320492 :=
  rowsJD_le_of_splitJ 111 112 (by norm_num) (by norm_num) rows22000E_494 c22000E_111_4 (by norm_num)

theorem c22000E_111_2 : rowsJD 111 112 59 272 ≤ 590742413750671 :=
  rowsJD_le_of_splitJ 111 112 (by norm_num) (by norm_num) rows22000E_493 c22000E_111_3 (by norm_num)

theorem c22000E_111_1 : rowsJD 111 112 40 272 ≤ 755155169407021 :=
  rowsJD_le_of_splitJ 111 112 (by norm_num) (by norm_num) rows22000E_492 c22000E_111_2 (by norm_num)

theorem c22000E_111_0 : rowsJD 111 112 0 272 ≤ 909466989286267 :=
  rowsJD_le_of_splitJ 111 112 (by norm_num) (by norm_num) rows22000E_491 c22000E_111_1 (by norm_num)

theorem c22000E_112_6 : rowsJD 112 113 93 272 ≤ 238398907859857 :=
  rowsJD_le_of_splitJ 112 113 (by norm_num) (by norm_num) rows22000E_506 rows22000E_507 (by norm_num)

theorem c22000E_112_5 : rowsJD 112 113 87 272 ≤ 313930127219216 :=
  rowsJD_le_of_splitJ 112 113 (by norm_num) (by norm_num) rows22000E_505 c22000E_112_6 (by norm_num)

theorem c22000E_112_4 : rowsJD 112 113 80 272 ≤ 386653904033507 :=
  rowsJD_le_of_splitJ 112 113 (by norm_num) (by norm_num) rows22000E_504 c22000E_112_5 (by norm_num)

theorem c22000E_112_3 : rowsJD 112 113 70 272 ≤ 446243527074156 :=
  rowsJD_le_of_splitJ 112 113 (by norm_num) (by norm_num) rows22000E_503 c22000E_112_4 (by norm_num)

theorem c22000E_112_2 : rowsJD 112 113 60 272 ≤ 575278255147178 :=
  rowsJD_le_of_splitJ 112 113 (by norm_num) (by norm_num) rows22000E_502 c22000E_112_3 (by norm_num)

theorem c22000E_112_1 : rowsJD 112 113 40 272 ≤ 743886765212654 :=
  rowsJD_le_of_splitJ 112 113 (by norm_num) (by norm_num) rows22000E_501 c22000E_112_2 (by norm_num)

theorem c22000E_112_0 : rowsJD 112 113 0 272 ≤ 897705536900070 :=
  rowsJD_le_of_splitJ 112 113 (by norm_num) (by norm_num) rows22000E_500 c22000E_112_1 (by norm_num)

theorem c22000E_113_6 : rowsJD 113 114 93 272 ≤ 198396890679927 :=
  rowsJD_le_of_splitJ 113 114 (by norm_num) (by norm_num) rows22000E_514 rows22000E_515 (by norm_num)

theorem c22000E_113_5 : rowsJD 113 114 87 272 ≤ 284251891265217 :=
  rowsJD_le_of_splitJ 113 114 (by norm_num) (by norm_num) rows22000E_513 c22000E_113_6 (by norm_num)

theorem c22000E_113_4 : rowsJD 113 114 80 272 ≤ 367922353613801 :=
  rowsJD_le_of_splitJ 113 114 (by norm_num) (by norm_num) rows22000E_512 c22000E_113_5 (by norm_num)

theorem c22000E_113_3 : rowsJD 113 114 70 272 ≤ 435183083975162 :=
  rowsJD_le_of_splitJ 113 114 (by norm_num) (by norm_num) rows22000E_511 c22000E_113_4 (by norm_num)

theorem c22000E_113_2 : rowsJD 113 114 60 272 ≤ 569694575743365 :=
  rowsJD_le_of_splitJ 113 114 (by norm_num) (by norm_num) rows22000E_510 c22000E_113_3 (by norm_num)

theorem c22000E_113_1 : rowsJD 113 114 40 272 ≤ 728649263757112 :=
  rowsJD_le_of_splitJ 113 114 (by norm_num) (by norm_num) rows22000E_509 c22000E_113_2 (by norm_num)

theorem c22000E_113_0 : rowsJD 113 114 0 272 ≤ 880178553625707 :=
  rowsJD_le_of_splitJ 113 114 (by norm_num) (by norm_num) rows22000E_508 c22000E_113_1 (by norm_num)

theorem c22000E_114_6 : rowsJD 114 115 93 272 ≤ 168530793727322 :=
  rowsJD_le_of_splitJ 114 115 (by norm_num) (by norm_num) rows22000E_522 rows22000E_523 (by norm_num)

theorem c22000E_114_5 : rowsJD 114 115 87 272 ≤ 269060350411939 :=
  rowsJD_le_of_splitJ 114 115 (by norm_num) (by norm_num) rows22000E_521 c22000E_114_6 (by norm_num)

theorem c22000E_114_4 : rowsJD 114 115 80 272 ≤ 366431662468305 :=
  rowsJD_le_of_splitJ 114 115 (by norm_num) (by norm_num) rows22000E_520 c22000E_114_5 (by norm_num)

theorem c22000E_114_3 : rowsJD 114 115 70 272 ≤ 441637509371506 :=
  rowsJD_le_of_splitJ 114 115 (by norm_num) (by norm_num) rows22000E_519 c22000E_114_4 (by norm_num)

theorem c22000E_114_2 : rowsJD 114 115 60 272 ≤ 581799404533718 :=
  rowsJD_le_of_splitJ 114 115 (by norm_num) (by norm_num) rows22000E_518 c22000E_114_3 (by norm_num)

theorem c22000E_114_1 : rowsJD 114 115 40 272 ≤ 730969565908498 :=
  rowsJD_le_of_splitJ 114 115 (by norm_num) (by norm_num) rows22000E_517 c22000E_114_2 (by norm_num)

theorem c22000E_114_0 : rowsJD 114 115 0 272 ≤ 879982696971058 :=
  rowsJD_le_of_splitJ 114 115 (by norm_num) (by norm_num) rows22000E_516 c22000E_114_1 (by norm_num)

theorem c22000E_115_5 : rowsJD 115 116 87 272 ≤ 257044592656564 :=
  rowsJD_le_of_splitJ 115 116 (by norm_num) (by norm_num) rows22000E_529 rows22000E_530 (by norm_num)

theorem c22000E_115_4 : rowsJD 115 116 80 272 ≤ 368940268172870 :=
  rowsJD_le_of_splitJ 115 116 (by norm_num) (by norm_num) rows22000E_528 c22000E_115_5 (by norm_num)

theorem c22000E_115_3 : rowsJD 115 116 70 272 ≤ 450990410885653 :=
  rowsJD_le_of_splitJ 115 116 (by norm_num) (by norm_num) rows22000E_527 c22000E_115_4 (by norm_num)

theorem c22000E_115_2 : rowsJD 115 116 60 272 ≤ 595097519992306 :=
  rowsJD_le_of_splitJ 115 116 (by norm_num) (by norm_num) rows22000E_526 c22000E_115_3 (by norm_num)

theorem c22000E_115_1 : rowsJD 115 116 40 272 ≤ 735223198758499 :=
  rowsJD_le_of_splitJ 115 116 (by norm_num) (by norm_num) rows22000E_525 c22000E_115_2 (by norm_num)

theorem c22000E_115_0 : rowsJD 115 116 0 272 ≤ 880390237647290 :=
  rowsJD_le_of_splitJ 115 116 (by norm_num) (by norm_num) rows22000E_524 c22000E_115_1 (by norm_num)

theorem c22000E_116_5 : rowsJD 116 117 87 272 ≤ 392622166370632 :=
  rowsJD_le_of_splitJ 116 117 (by norm_num) (by norm_num) rows22000E_536 rows22000E_537 (by norm_num)

theorem c22000E_116_4 : rowsJD 116 117 80 272 ≤ 519115721543039 :=
  rowsJD_le_of_splitJ 116 117 (by norm_num) (by norm_num) rows22000E_535 c22000E_116_5 (by norm_num)

theorem c22000E_116_3 : rowsJD 116 117 70 272 ≤ 602709460303146 :=
  rowsJD_le_of_splitJ 116 117 (by norm_num) (by norm_num) rows22000E_534 c22000E_116_4 (by norm_num)

theorem c22000E_116_2 : rowsJD 116 117 61 272 ≤ 736130310917949 :=
  rowsJD_le_of_splitJ 116 117 (by norm_num) (by norm_num) rows22000E_533 c22000E_116_3 (by norm_num)

theorem c22000E_116_1 : rowsJD 116 117 40 272 ≤ 877729874935228 :=
  rowsJD_le_of_splitJ 116 117 (by norm_num) (by norm_num) rows22000E_532 c22000E_116_2 (by norm_num)

theorem c22000E_116_0 : rowsJD 116 117 0 272 ≤ 1018782213347199 :=
  rowsJD_le_of_splitJ 116 117 (by norm_num) (by norm_num) rows22000E_531 c22000E_116_1 (by norm_num)

theorem c22000E_117_6 : rowsJD 117 118 92 272 ≤ 522653838615319 :=
  rowsJD_le_of_splitJ 117 118 (by norm_num) (by norm_num) rows22000E_544 rows22000E_545 (by norm_num)

theorem c22000E_117_5 : rowsJD 117 118 87 272 ≤ 641271071225352 :=
  rowsJD_le_of_splitJ 117 118 (by norm_num) (by norm_num) rows22000E_543 c22000E_117_6 (by norm_num)

theorem c22000E_117_4 : rowsJD 117 118 80 272 ≤ 784511928143403 :=
  rowsJD_le_of_splitJ 117 118 (by norm_num) (by norm_num) rows22000E_542 c22000E_117_5 (by norm_num)

theorem c22000E_117_3 : rowsJD 117 118 70 272 ≤ 880127240511815 :=
  rowsJD_le_of_splitJ 117 118 (by norm_num) (by norm_num) rows22000E_541 c22000E_117_4 (by norm_num)

theorem c22000E_117_2 : rowsJD 117 118 61 272 ≤ 1023996541671482 :=
  rowsJD_le_of_splitJ 117 118 (by norm_num) (by norm_num) rows22000E_540 c22000E_117_3 (by norm_num)

theorem c22000E_117_1 : rowsJD 117 118 40 272 ≤ 1170124548510894 :=
  rowsJD_le_of_splitJ 117 118 (by norm_num) (by norm_num) rows22000E_539 c22000E_117_2 (by norm_num)

theorem c22000E_117_0 : rowsJD 117 118 0 272 ≤ 1310243971223458 :=
  rowsJD_le_of_splitJ 117 118 (by norm_num) (by norm_num) rows22000E_538 c22000E_117_1 (by norm_num)

theorem c22000E_118_6 : rowsJD 118 119 92 272 ≤ 718884283852762 :=
  rowsJD_le_of_splitJ 118 119 (by norm_num) (by norm_num) rows22000E_552 rows22000E_553 (by norm_num)

theorem c22000E_118_5 : rowsJD 118 119 87 272 ≤ 849930103527399 :=
  rowsJD_le_of_splitJ 118 119 (by norm_num) (by norm_num) rows22000E_551 c22000E_118_6 (by norm_num)

theorem c22000E_118_4 : rowsJD 118 119 81 272 ≤ 992251679483735 :=
  rowsJD_le_of_splitJ 118 119 (by norm_num) (by norm_num) rows22000E_550 c22000E_118_5 (by norm_num)

theorem c22000E_118_3 : rowsJD 118 119 71 272 ≤ 1108370798006094 :=
  rowsJD_le_of_splitJ 118 119 (by norm_num) (by norm_num) rows22000E_549 c22000E_118_4 (by norm_num)

theorem c22000E_118_2 : rowsJD 118 119 62 272 ≤ 1255872981239047 :=
  rowsJD_le_of_splitJ 118 119 (by norm_num) (by norm_num) rows22000E_548 c22000E_118_3 (by norm_num)

theorem c22000E_118_1 : rowsJD 118 119 41 272 ≤ 1414337518350558 :=
  rowsJD_le_of_splitJ 118 119 (by norm_num) (by norm_num) rows22000E_547 c22000E_118_2 (by norm_num)

theorem c22000E_118_0 : rowsJD 118 119 0 272 ≤ 1562101458298102 :=
  rowsJD_le_of_splitJ 118 119 (by norm_num) (by norm_num) rows22000E_546 c22000E_118_1 (by norm_num)

theorem c22000E_119_6 : rowsJD 119 120 91 272 ≤ 911995306388762 :=
  rowsJD_le_of_splitJ 119 120 (by norm_num) (by norm_num) rows22000E_560 rows22000E_561 (by norm_num)

theorem c22000E_119_5 : rowsJD 119 120 86 272 ≤ 1053488511107553 :=
  rowsJD_le_of_splitJ 119 120 (by norm_num) (by norm_num) rows22000E_559 c22000E_119_6 (by norm_num)

theorem c22000E_119_4 : rowsJD 119 120 80 272 ≤ 1206272882842314 :=
  rowsJD_le_of_splitJ 119 120 (by norm_num) (by norm_num) rows22000E_558 c22000E_119_5 (by norm_num)

theorem c22000E_119_3 : rowsJD 119 120 70 272 ≤ 1319955749517622 :=
  rowsJD_le_of_splitJ 119 120 (by norm_num) (by norm_num) rows22000E_557 c22000E_119_4 (by norm_num)

theorem c22000E_119_2 : rowsJD 119 120 61 272 ≤ 1464345498067226 :=
  rowsJD_le_of_splitJ 119 120 (by norm_num) (by norm_num) rows22000E_556 c22000E_119_3 (by norm_num)

theorem c22000E_119_1 : rowsJD 119 120 41 272 ≤ 1603197869040754 :=
  rowsJD_le_of_splitJ 119 120 (by norm_num) (by norm_num) rows22000E_555 c22000E_119_2 (by norm_num)

theorem c22000E_119_0 : rowsJD 119 120 0 272 ≤ 1748736164292632 :=
  rowsJD_le_of_splitJ 119 120 (by norm_num) (by norm_num) rows22000E_554 c22000E_119_1 (by norm_num)

theorem c22000E_120_6 : rowsJD 120 121 92 272 ≤ 1023121974728829 :=
  rowsJD_le_of_splitJ 120 121 (by norm_num) (by norm_num) rows22000E_568 rows22000E_569 (by norm_num)

theorem c22000E_120_5 : rowsJD 120 121 87 272 ≤ 1173864669489422 :=
  rowsJD_le_of_splitJ 120 121 (by norm_num) (by norm_num) rows22000E_567 c22000E_120_6 (by norm_num)

theorem c22000E_120_4 : rowsJD 120 121 81 272 ≤ 1349795145337245 :=
  rowsJD_le_of_splitJ 120 121 (by norm_num) (by norm_num) rows22000E_566 c22000E_120_5 (by norm_num)

theorem c22000E_120_3 : rowsJD 120 121 72 272 ≤ 1481147549209362 :=
  rowsJD_le_of_splitJ 120 121 (by norm_num) (by norm_num) rows22000E_565 c22000E_120_4 (by norm_num)

theorem c22000E_120_2 : rowsJD 120 121 62 272 ≤ 1614750160546227 :=
  rowsJD_le_of_splitJ 120 121 (by norm_num) (by norm_num) rows22000E_564 c22000E_120_3 (by norm_num)

theorem c22000E_120_1 : rowsJD 120 121 42 272 ≤ 1757159010773972 :=
  rowsJD_le_of_splitJ 120 121 (by norm_num) (by norm_num) rows22000E_563 c22000E_120_2 (by norm_num)

theorem c22000E_120_0 : rowsJD 120 121 0 272 ≤ 1907242451538624 :=
  rowsJD_le_of_splitJ 120 121 (by norm_num) (by norm_num) rows22000E_562 c22000E_120_1 (by norm_num)

theorem c22000E_121_6 : rowsJD 121 122 91 272 ≤ 1167554574644973 :=
  rowsJD_le_of_splitJ 121 122 (by norm_num) (by norm_num) rows22000E_576 rows22000E_577 (by norm_num)

theorem c22000E_121_5 : rowsJD 121 122 86 272 ≤ 1328670841574941 :=
  rowsJD_le_of_splitJ 121 122 (by norm_num) (by norm_num) rows22000E_575 c22000E_121_6 (by norm_num)

theorem c22000E_121_4 : rowsJD 121 122 80 272 ≤ 1515358253297611 :=
  rowsJD_le_of_splitJ 121 122 (by norm_num) (by norm_num) rows22000E_574 c22000E_121_5 (by norm_num)

theorem c22000E_121_3 : rowsJD 121 122 72 272 ≤ 1635751410064523 :=
  rowsJD_le_of_splitJ 121 122 (by norm_num) (by norm_num) rows22000E_573 c22000E_121_4 (by norm_num)

theorem c22000E_121_2 : rowsJD 121 122 62 272 ≤ 1755336145376547 :=
  rowsJD_le_of_splitJ 121 122 (by norm_num) (by norm_num) rows22000E_572 c22000E_121_3 (by norm_num)

theorem c22000E_121_1 : rowsJD 121 122 42 272 ≤ 1891981513525169 :=
  rowsJD_le_of_splitJ 121 122 (by norm_num) (by norm_num) rows22000E_571 c22000E_121_2 (by norm_num)

theorem c22000E_121_0 : rowsJD 121 122 0 272 ≤ 2038676900567199 :=
  rowsJD_le_of_splitJ 121 122 (by norm_num) (by norm_num) rows22000E_570 c22000E_121_1 (by norm_num)

theorem c22000E_122_6 : rowsJD 122 123 91 272 ≤ 1265961538845664 :=
  rowsJD_le_of_splitJ 122 123 (by norm_num) (by norm_num) rows22000E_584 rows22000E_585 (by norm_num)

theorem c22000E_122_5 : rowsJD 122 123 86 272 ≤ 1434654019166181 :=
  rowsJD_le_of_splitJ 122 123 (by norm_num) (by norm_num) rows22000E_583 c22000E_122_6 (by norm_num)

theorem c22000E_122_4 : rowsJD 122 123 80 272 ≤ 1638242369382552 :=
  rowsJD_le_of_splitJ 122 123 (by norm_num) (by norm_num) rows22000E_582 c22000E_122_5 (by norm_num)

theorem c22000E_122_3 : rowsJD 122 123 72 272 ≤ 1773822063334132 :=
  rowsJD_le_of_splitJ 122 123 (by norm_num) (by norm_num) rows22000E_581 c22000E_122_4 (by norm_num)

theorem c22000E_122_2 : rowsJD 122 123 62 272 ≤ 1880268549628728 :=
  rowsJD_le_of_splitJ 122 123 (by norm_num) (by norm_num) rows22000E_580 c22000E_122_3 (by norm_num)

theorem c22000E_122_1 : rowsJD 122 123 43 272 ≤ 2006490654412879 :=
  rowsJD_le_of_splitJ 122 123 (by norm_num) (by norm_num) rows22000E_579 c22000E_122_2 (by norm_num)

theorem c22000E_122_0 : rowsJD 122 123 0 272 ≤ 2155007884628853 :=
  rowsJD_le_of_splitJ 122 123 (by norm_num) (by norm_num) rows22000E_578 c22000E_122_1 (by norm_num)

theorem c22000E_123_6 : rowsJD 123 124 109 272 ≤ 1348732970802754 :=
  rowsJD_le_of_splitJ 123 124 (by norm_num) (by norm_num) rows22000E_592 rows22000E_593 (by norm_num)

theorem c22000E_123_5 : rowsJD 123 124 86 272 ≤ 1523276503898869 :=
  rowsJD_le_of_splitJ 123 124 (by norm_num) (by norm_num) rows22000E_591 c22000E_123_6 (by norm_num)

theorem c22000E_123_4 : rowsJD 123 124 80 272 ≤ 1743200805746637 :=
  rowsJD_le_of_splitJ 123 124 (by norm_num) (by norm_num) rows22000E_590 c22000E_123_5 (by norm_num)

theorem c22000E_123_3 : rowsJD 123 124 73 272 ≤ 1891725132119453 :=
  rowsJD_le_of_splitJ 123 124 (by norm_num) (by norm_num) rows22000E_589 c22000E_123_4 (by norm_num)

theorem c22000E_123_2 : rowsJD 123 124 62 272 ≤ 1990288974267848 :=
  rowsJD_le_of_splitJ 123 124 (by norm_num) (by norm_num) rows22000E_588 c22000E_123_3 (by norm_num)

theorem c22000E_123_1 : rowsJD 123 124 44 272 ≤ 2107326971220603 :=
  rowsJD_le_of_splitJ 123 124 (by norm_num) (by norm_num) rows22000E_587 c22000E_123_2 (by norm_num)

theorem c22000E_123_0 : rowsJD 123 124 0 272 ≤ 2255425733939684 :=
  rowsJD_le_of_splitJ 123 124 (by norm_num) (by norm_num) rows22000E_586 c22000E_123_1 (by norm_num)

theorem c22000E_124_5 : rowsJD 124 125 86 272 ≤ 1601299529694247 :=
  rowsJD_le_of_splitJ 124 125 (by norm_num) (by norm_num) rows22000E_599 rows22000E_600 (by norm_num)

theorem c22000E_124_4 : rowsJD 124 125 80 272 ≤ 1836580957148785 :=
  rowsJD_le_of_splitJ 124 125 (by norm_num) (by norm_num) rows22000E_598 c22000E_124_5 (by norm_num)

theorem c22000E_124_3 : rowsJD 124 125 73 272 ≤ 2003763218856735 :=
  rowsJD_le_of_splitJ 124 125 (by norm_num) (by norm_num) rows22000E_597 c22000E_124_4 (by norm_num)

theorem c22000E_124_2 : rowsJD 124 125 62 272 ≤ 2092944352116911 :=
  rowsJD_le_of_splitJ 124 125 (by norm_num) (by norm_num) rows22000E_596 c22000E_124_3 (by norm_num)

theorem c22000E_124_1 : rowsJD 124 125 44 272 ≤ 2204536060169220 :=
  rowsJD_le_of_splitJ 124 125 (by norm_num) (by norm_num) rows22000E_595 c22000E_124_2 (by norm_num)

theorem c22000E_124_0 : rowsJD 124 125 0 272 ≤ 2348130082740363 :=
  rowsJD_le_of_splitJ 124 125 (by norm_num) (by norm_num) rows22000E_594 c22000E_124_1 (by norm_num)

theorem c22000E_125_6 : rowsJD 125 126 109 272 ≤ 1502101002514654 :=
  rowsJD_le_of_splitJ 125 126 (by norm_num) (by norm_num) rows22000E_607 rows22000E_608 (by norm_num)

theorem c22000E_125_5 : rowsJD 125 126 85 272 ≤ 1710680348783879 :=
  rowsJD_le_of_splitJ 125 126 (by norm_num) (by norm_num) rows22000E_606 c22000E_125_6 (by norm_num)

theorem c22000E_125_4 : rowsJD 125 126 80 272 ≤ 1918020978250429 :=
  rowsJD_le_of_splitJ 125 126 (by norm_num) (by norm_num) rows22000E_605 c22000E_125_5 (by norm_num)

theorem c22000E_125_3 : rowsJD 125 126 73 272 ≤ 2104647147622430 :=
  rowsJD_le_of_splitJ 125 126 (by norm_num) (by norm_num) rows22000E_604 c22000E_125_4 (by norm_num)

theorem c22000E_125_2 : rowsJD 125 126 62 272 ≤ 2187089628296637 :=
  rowsJD_le_of_splitJ 125 126 (by norm_num) (by norm_num) rows22000E_603 c22000E_125_3 (by norm_num)

theorem c22000E_125_1 : rowsJD 125 126 45 272 ≤ 2290228050126301 :=
  rowsJD_le_of_splitJ 125 126 (by norm_num) (by norm_num) rows22000E_602 c22000E_125_2 (by norm_num)

theorem c22000E_125_0 : rowsJD 125 126 0 272 ≤ 2432082143384464 :=
  rowsJD_le_of_splitJ 125 126 (by norm_num) (by norm_num) rows22000E_601 c22000E_125_1 (by norm_num)

theorem c22000E_126_5 : rowsJD 126 127 85 272 ≤ 1793464978557231 :=
  rowsJD_le_of_splitJ 126 127 (by norm_num) (by norm_num) rows22000E_614 rows22000E_615 (by norm_num)

theorem c22000E_126_4 : rowsJD 126 127 80 272 ≤ 2013027252515235 :=
  rowsJD_le_of_splitJ 126 127 (by norm_num) (by norm_num) rows22000E_613 c22000E_126_5 (by norm_num)

theorem c22000E_126_3 : rowsJD 126 127 73 272 ≤ 2219010300951690 :=
  rowsJD_le_of_splitJ 126 127 (by norm_num) (by norm_num) rows22000E_612 c22000E_126_4 (by norm_num)

theorem c22000E_126_2 : rowsJD 126 127 62 272 ≤ 2296802851980957 :=
  rowsJD_le_of_splitJ 126 127 (by norm_num) (by norm_num) rows22000E_611 c22000E_126_3 (by norm_num)

theorem c22000E_126_1 : rowsJD 126 127 46 272 ≤ 2393124138669516 :=
  rowsJD_le_of_splitJ 126 127 (by norm_num) (by norm_num) rows22000E_610 c22000E_126_2 (by norm_num)

theorem c22000E_126_0 : rowsJD 126 127 0 272 ≤ 2533133761242195 :=
  rowsJD_le_of_splitJ 126 127 (by norm_num) (by norm_num) rows22000E_609 c22000E_126_1 (by norm_num)

theorem c22000E_127_5 : rowsJD 127 128 85 272 ≤ 1898740869752986 :=
  rowsJD_le_of_splitJ 127 128 (by norm_num) (by norm_num) rows22000E_621 rows22000E_622 (by norm_num)

theorem c22000E_127_4 : rowsJD 127 128 80 272 ≤ 2130317200231751 :=
  rowsJD_le_of_splitJ 127 128 (by norm_num) (by norm_num) rows22000E_620 c22000E_127_5 (by norm_num)

theorem c22000E_127_3 : rowsJD 127 128 73 272 ≤ 2355029469505750 :=
  rowsJD_le_of_splitJ 127 128 (by norm_num) (by norm_num) rows22000E_619 c22000E_127_4 (by norm_num)

theorem c22000E_127_2 : rowsJD 127 128 62 272 ≤ 2432551888522006 :=
  rowsJD_le_of_splitJ 127 128 (by norm_num) (by norm_num) rows22000E_618 c22000E_127_3 (by norm_num)

theorem c22000E_127_1 : rowsJD 127 128 46 272 ≤ 2524753560555004 :=
  rowsJD_le_of_splitJ 127 128 (by norm_num) (by norm_num) rows22000E_617 c22000E_127_2 (by norm_num)

theorem c22000E_127_0 : rowsJD 127 128 0 272 ≤ 2659223164718645 :=
  rowsJD_le_of_splitJ 127 128 (by norm_num) (by norm_num) rows22000E_616 c22000E_127_1 (by norm_num)

theorem c22000E_128_5 : rowsJD 128 129 85 272 ≤ 2011225048111775 :=
  rowsJD_le_of_splitJ 128 129 (by norm_num) (by norm_num) rows22000E_628 rows22000E_629 (by norm_num)

theorem c22000E_128_4 : rowsJD 128 129 80 272 ≤ 2253921570167753 :=
  rowsJD_le_of_splitJ 128 129 (by norm_num) (by norm_num) rows22000E_627 c22000E_128_5 (by norm_num)

theorem c22000E_128_3 : rowsJD 128 129 73 272 ≤ 2496366335037867 :=
  rowsJD_le_of_splitJ 128 129 (by norm_num) (by norm_num) rows22000E_626 c22000E_128_4 (by norm_num)

theorem c22000E_128_2 : rowsJD 128 129 62 272 ≤ 2575682512987013 :=
  rowsJD_le_of_splitJ 128 129 (by norm_num) (by norm_num) rows22000E_625 c22000E_128_3 (by norm_num)

theorem c22000E_128_1 : rowsJD 128 129 47 272 ≤ 2662331981345667 :=
  rowsJD_le_of_splitJ 128 129 (by norm_num) (by norm_num) rows22000E_624 c22000E_128_2 (by norm_num)

theorem c22000E_128_0 : rowsJD 128 129 0 272 ≤ 2794223902201851 :=
  rowsJD_le_of_splitJ 128 129 (by norm_num) (by norm_num) rows22000E_623 c22000E_128_1 (by norm_num)

theorem c22000E_129_5 : rowsJD 129 130 104 272 ≤ 2078717695844406 :=
  rowsJD_le_of_splitJ 129 130 (by norm_num) (by norm_num) rows22000E_635 rows22000E_636 (by norm_num)

theorem c22000E_129_4 : rowsJD 129 130 80 272 ≤ 2367371981262296 :=
  rowsJD_le_of_splitJ 129 130 (by norm_num) (by norm_num) rows22000E_634 c22000E_129_5 (by norm_num)

theorem c22000E_129_3 : rowsJD 129 130 73 272 ≤ 2626726482057094 :=
  rowsJD_le_of_splitJ 129 130 (by norm_num) (by norm_num) rows22000E_633 c22000E_129_4 (by norm_num)

theorem c22000E_129_2 : rowsJD 129 130 62 272 ≤ 2710249129403383 :=
  rowsJD_le_of_splitJ 129 130 (by norm_num) (by norm_num) rows22000E_632 c22000E_129_3 (by norm_num)

theorem c22000E_129_1 : rowsJD 129 130 47 272 ≤ 2793050964444197 :=
  rowsJD_le_of_splitJ 129 130 (by norm_num) (by norm_num) rows22000E_631 c22000E_129_2 (by norm_num)

theorem c22000E_129_0 : rowsJD 129 130 0 272 ≤ 2918276425594004 :=
  rowsJD_le_of_splitJ 129 130 (by norm_num) (by norm_num) rows22000E_630 c22000E_129_1 (by norm_num)

theorem c22000E_130_5 : rowsJD 130 131 104 272 ≤ 2191835811548609 :=
  rowsJD_le_of_splitJ 130 131 (by norm_num) (by norm_num) rows22000E_642 rows22000E_643 (by norm_num)

theorem c22000E_130_4 : rowsJD 130 131 80 272 ≤ 2476935626095780 :=
  rowsJD_le_of_splitJ 130 131 (by norm_num) (by norm_num) rows22000E_641 c22000E_130_5 (by norm_num)

theorem c22000E_130_3 : rowsJD 130 131 73 272 ≤ 2751396252275792 :=
  rowsJD_le_of_splitJ 130 131 (by norm_num) (by norm_num) rows22000E_640 c22000E_130_4 (by norm_num)

theorem c22000E_130_2 : rowsJD 130 131 62 272 ≤ 2838634405721883 :=
  rowsJD_le_of_splitJ 130 131 (by norm_num) (by norm_num) rows22000E_639 c22000E_130_3 (by norm_num)

theorem c22000E_130_1 : rowsJD 130 131 47 272 ≤ 2918230739742261 :=
  rowsJD_le_of_splitJ 130 131 (by norm_num) (by norm_num) rows22000E_638 c22000E_130_2 (by norm_num)

theorem c22000E_130_0 : rowsJD 130 131 0 272 ≤ 3037088636096556 :=
  rowsJD_le_of_splitJ 130 131 (by norm_num) (by norm_num) rows22000E_637 c22000E_130_1 (by norm_num)

theorem c22000E_131_5 : rowsJD 131 132 104 272 ≤ 2298533549208602 :=
  rowsJD_le_of_splitJ 131 132 (by norm_num) (by norm_num) rows22000E_649 rows22000E_650 (by norm_num)

theorem c22000E_131_4 : rowsJD 131 132 80 272 ≤ 2575375865837949 :=
  rowsJD_le_of_splitJ 131 132 (by norm_num) (by norm_num) rows22000E_648 c22000E_131_5 (by norm_num)

theorem c22000E_131_3 : rowsJD 131 132 73 272 ≤ 2862864879744703 :=
  rowsJD_le_of_splitJ 131 132 (by norm_num) (by norm_num) rows22000E_647 c22000E_131_4 (by norm_num)

theorem c22000E_131_2 : rowsJD 131 132 62 272 ≤ 2955590391978520 :=
  rowsJD_le_of_splitJ 131 132 (by norm_num) (by norm_num) rows22000E_646 c22000E_131_3 (by norm_num)

theorem c22000E_131_1 : rowsJD 131 132 48 272 ≤ 3028998355304684 :=
  rowsJD_le_of_splitJ 131 132 (by norm_num) (by norm_num) rows22000E_645 c22000E_131_2 (by norm_num)

theorem c22000E_131_0 : rowsJD 131 132 0 272 ≤ 3142746994440903 :=
  rowsJD_le_of_splitJ 131 132 (by norm_num) (by norm_num) rows22000E_644 c22000E_131_1 (by norm_num)

theorem c22000E_132_5 : rowsJD 132 133 105 272 ≤ 2355531272099847 :=
  rowsJD_le_of_splitJ 132 133 (by norm_num) (by norm_num) rows22000E_656 rows22000E_657 (by norm_num)

theorem c22000E_132_4 : rowsJD 132 133 80 272 ≤ 2664346320606544 :=
  rowsJD_le_of_splitJ 132 133 (by norm_num) (by norm_num) rows22000E_655 c22000E_132_5 (by norm_num)

theorem c22000E_132_3 : rowsJD 132 133 73 272 ≤ 2962286224142449 :=
  rowsJD_le_of_splitJ 132 133 (by norm_num) (by norm_num) rows22000E_654 c22000E_132_4 (by norm_num)

theorem c22000E_132_2 : rowsJD 132 133 62 272 ≤ 3060176121984708 :=
  rowsJD_le_of_splitJ 132 133 (by norm_num) (by norm_num) rows22000E_653 c22000E_132_3 (by norm_num)

theorem c22000E_132_1 : rowsJD 132 133 48 272 ≤ 3129539634639552 :=
  rowsJD_le_of_splitJ 132 133 (by norm_num) (by norm_num) rows22000E_652 c22000E_132_2 (by norm_num)

theorem c22000E_132_0 : rowsJD 132 133 0 272 ≤ 3236390134695558 :=
  rowsJD_le_of_splitJ 132 133 (by norm_num) (by norm_num) rows22000E_651 c22000E_132_1 (by norm_num)

theorem c22000E_133_5 : rowsJD 133 134 105 272 ≤ 2458082201619025 :=
  rowsJD_le_of_splitJ 133 134 (by norm_num) (by norm_num) rows22000E_663 rows22000E_664 (by norm_num)

theorem c22000E_133_4 : rowsJD 133 134 80 272 ≤ 2744842928817739 :=
  rowsJD_le_of_splitJ 133 134 (by norm_num) (by norm_num) rows22000E_662 c22000E_133_5 (by norm_num)

theorem c22000E_133_3 : rowsJD 133 134 73 272 ≤ 3049472906990947 :=
  rowsJD_le_of_splitJ 133 134 (by norm_num) (by norm_num) rows22000E_661 c22000E_133_4 (by norm_num)

theorem c22000E_133_2 : rowsJD 133 134 62 272 ≤ 3153357238529967 :=
  rowsJD_le_of_splitJ 133 134 (by norm_num) (by norm_num) rows22000E_660 c22000E_133_3 (by norm_num)

theorem c22000E_133_1 : rowsJD 133 134 48 272 ≤ 3217532205479812 :=
  rowsJD_le_of_splitJ 133 134 (by norm_num) (by norm_num) rows22000E_659 c22000E_133_2 (by norm_num)

theorem c22000E_133_0 : rowsJD 133 134 0 272 ≤ 3320457231298079 :=
  rowsJD_le_of_splitJ 133 134 (by norm_num) (by norm_num) rows22000E_658 c22000E_133_1 (by norm_num)

theorem c22000E_134_5 : rowsJD 134 135 106 272 ≤ 2508872354071340 :=
  rowsJD_le_of_splitJ 134 135 (by norm_num) (by norm_num) rows22000E_670 rows22000E_671 (by norm_num)

theorem c22000E_134_4 : rowsJD 134 135 98 272 ≤ 2813533713140767 :=
  rowsJD_le_of_splitJ 134 135 (by norm_num) (by norm_num) rows22000E_669 c22000E_134_5 (by norm_num)

theorem c22000E_134_3 : rowsJD 134 135 73 272 ≤ 3120475505858334 :=
  rowsJD_le_of_splitJ 134 135 (by norm_num) (by norm_num) rows22000E_668 c22000E_134_4 (by norm_num)

theorem c22000E_134_2 : rowsJD 134 135 62 272 ≤ 3229567572628927 :=
  rowsJD_le_of_splitJ 134 135 (by norm_num) (by norm_num) rows22000E_667 c22000E_134_3 (by norm_num)

theorem c22000E_134_1 : rowsJD 134 135 48 272 ≤ 3288716952569428 :=
  rowsJD_le_of_splitJ 134 135 (by norm_num) (by norm_num) rows22000E_666 c22000E_134_2 (by norm_num)

theorem c22000E_134_0 : rowsJD 134 135 0 272 ≤ 3388094504109586 :=
  rowsJD_le_of_splitJ 134 135 (by norm_num) (by norm_num) rows22000E_665 c22000E_134_1 (by norm_num)

theorem c22000E_135_5 : rowsJD 135 136 106 272 ≤ 2491253907146620 :=
  rowsJD_le_of_splitJ 135 136 (by norm_num) (by norm_num) rows22000E_677 rows22000E_678 (by norm_num)

theorem c22000E_135_4 : rowsJD 135 136 98 272 ≤ 2789762009583126 :=
  rowsJD_le_of_splitJ 135 136 (by norm_num) (by norm_num) rows22000E_676 c22000E_135_5 (by norm_num)

theorem c22000E_135_3 : rowsJD 135 136 73 272 ≤ 3061596122055784 :=
  rowsJD_le_of_splitJ 135 136 (by norm_num) (by norm_num) rows22000E_675 c22000E_135_4 (by norm_num)

theorem c22000E_135_2 : rowsJD 135 136 62 272 ≤ 3176455802104990 :=
  rowsJD_le_of_splitJ 135 136 (by norm_num) (by norm_num) rows22000E_674 c22000E_135_3 (by norm_num)

theorem c22000E_135_1 : rowsJD 135 136 48 272 ≤ 3229905945063667 :=
  rowsJD_le_of_splitJ 135 136 (by norm_num) (by norm_num) rows22000E_673 c22000E_135_2 (by norm_num)

theorem c22000E_135_0 : rowsJD 135 136 0 272 ≤ 3325288039388318 :=
  rowsJD_le_of_splitJ 135 136 (by norm_num) (by norm_num) rows22000E_672 c22000E_135_1 (by norm_num)

theorem c22000E_136_5 : rowsJD 136 137 107 272 ≤ 2302384046810103 :=
  rowsJD_le_of_splitJ 136 137 (by norm_num) (by norm_num) rows22000E_684 rows22000E_685 (by norm_num)

theorem c22000E_136_4 : rowsJD 136 137 99 272 ≤ 2618365350055298 :=
  rowsJD_le_of_splitJ 136 137 (by norm_num) (by norm_num) rows22000E_683 c22000E_136_5 (by norm_num)

theorem c22000E_136_3 : rowsJD 136 137 73 272 ≤ 2878589734988584 :=
  rowsJD_le_of_splitJ 136 137 (by norm_num) (by norm_num) rows22000E_682 c22000E_136_4 (by norm_num)

theorem c22000E_136_2 : rowsJD 136 137 62 272 ≤ 2994147583897957 :=
  rowsJD_le_of_splitJ 136 137 (by norm_num) (by norm_num) rows22000E_681 c22000E_136_3 (by norm_num)

theorem c22000E_136_1 : rowsJD 136 137 48 272 ≤ 3042428289918151 :=
  rowsJD_le_of_splitJ 136 137 (by norm_num) (by norm_num) rows22000E_680 c22000E_136_2 (by norm_num)

theorem c22000E_136_0 : rowsJD 136 137 0 272 ≤ 3134160563343327 :=
  rowsJD_le_of_splitJ 136 137 (by norm_num) (by norm_num) rows22000E_679 c22000E_136_1 (by norm_num)

theorem c22000E_137_5 : rowsJD 137 138 108 272 ≤ 2104337755957740 :=
  rowsJD_le_of_splitJ 137 138 (by norm_num) (by norm_num) rows22000E_691 rows22000E_692 (by norm_num)

theorem c22000E_137_4 : rowsJD 137 138 99 272 ≤ 2453729116301172 :=
  rowsJD_le_of_splitJ 137 138 (by norm_num) (by norm_num) rows22000E_690 c22000E_137_5 (by norm_num)

theorem c22000E_137_3 : rowsJD 137 138 73 272 ≤ 2681633368341548 :=
  rowsJD_le_of_splitJ 137 138 (by norm_num) (by norm_num) rows22000E_689 c22000E_137_4 (by norm_num)

theorem c22000E_137_2 : rowsJD 137 138 62 272 ≤ 2796323203295550 :=
  rowsJD_le_of_splitJ 137 138 (by norm_num) (by norm_num) rows22000E_688 c22000E_137_3 (by norm_num)

theorem c22000E_137_1 : rowsJD 137 138 48 272 ≤ 2838827540172238 :=
  rowsJD_le_of_splitJ 137 138 (by norm_num) (by norm_num) rows22000E_687 c22000E_137_2 (by norm_num)

theorem c22000E_137_0 : rowsJD 137 138 0 272 ≤ 2926339285483015 :=
  rowsJD_le_of_splitJ 137 138 (by norm_num) (by norm_num) rows22000E_686 c22000E_137_1 (by norm_num)

theorem c22000E_138_5 : rowsJD 138 139 108 272 ≤ 1979164747112651 :=
  rowsJD_le_of_splitJ 138 139 (by norm_num) (by norm_num) rows22000E_698 rows22000E_699 (by norm_num)

theorem c22000E_138_4 : rowsJD 138 139 99 272 ≤ 2310483248710591 :=
  rowsJD_le_of_splitJ 138 139 (by norm_num) (by norm_num) rows22000E_697 c22000E_138_5 (by norm_num)

theorem c22000E_138_3 : rowsJD 138 139 73 272 ≤ 2520386058183176 :=
  rowsJD_le_of_splitJ 138 139 (by norm_num) (by norm_num) rows22000E_696 c22000E_138_4 (by norm_num)

theorem c22000E_138_2 : rowsJD 138 139 62 272 ≤ 2639896355917386 :=
  rowsJD_le_of_splitJ 138 139 (by norm_num) (by norm_num) rows22000E_695 c22000E_138_3 (by norm_num)

theorem c22000E_138_1 : rowsJD 138 139 48 272 ≤ 2677780971309022 :=
  rowsJD_le_of_splitJ 138 139 (by norm_num) (by norm_num) rows22000E_694 c22000E_138_2 (by norm_num)

theorem c22000E_138_0 : rowsJD 138 139 0 272 ≤ 2761558025714027 :=
  rowsJD_le_of_splitJ 138 139 (by norm_num) (by norm_num) rows22000E_693 c22000E_138_1 (by norm_num)

theorem c22000E_139_5 : rowsJD 139 140 109 272 ≤ 1823934983302487 :=
  rowsJD_le_of_splitJ 139 140 (by norm_num) (by norm_num) rows22000E_705 rows22000E_706 (by norm_num)

theorem c22000E_139_4 : rowsJD 139 140 100 272 ≤ 2164434042638777 :=
  rowsJD_le_of_splitJ 139 140 (by norm_num) (by norm_num) rows22000E_704 c22000E_139_5 (by norm_num)

theorem c22000E_139_3 : rowsJD 139 140 73 272 ≤ 2397663777675702 :=
  rowsJD_le_of_splitJ 139 140 (by norm_num) (by norm_num) rows22000E_703 c22000E_139_4 (by norm_num)

theorem c22000E_139_2 : rowsJD 139 140 62 272 ≤ 2534702862991631 :=
  rowsJD_le_of_splitJ 139 140 (by norm_num) (by norm_num) rows22000E_702 c22000E_139_3 (by norm_num)

theorem c22000E_139_1 : rowsJD 139 140 48 272 ≤ 2568279334667450 :=
  rowsJD_le_of_splitJ 139 140 (by norm_num) (by norm_num) rows22000E_701 c22000E_139_2 (by norm_num)

theorem c22000E_139_0 : rowsJD 139 140 0 272 ≤ 2648172893597479 :=
  rowsJD_le_of_splitJ 139 140 (by norm_num) (by norm_num) rows22000E_700 c22000E_139_1 (by norm_num)

theorem c22000E_140_5 : rowsJD 140 141 109 272 ≤ 1716098152069689 :=
  rowsJD_le_of_splitJ 140 141 (by norm_num) (by norm_num) rows22000E_712 rows22000E_713 (by norm_num)

theorem c22000E_140_4 : rowsJD 140 141 100 272 ≤ 2057495269753614 :=
  rowsJD_le_of_splitJ 140 141 (by norm_num) (by norm_num) rows22000E_711 c22000E_140_5 (by norm_num)

theorem c22000E_140_3 : rowsJD 140 141 73 272 ≤ 2310693351047241 :=
  rowsJD_le_of_splitJ 140 141 (by norm_num) (by norm_num) rows22000E_710 c22000E_140_4 (by norm_num)

theorem c22000E_140_2 : rowsJD 140 141 62 272 ≤ 2474817372470450 :=
  rowsJD_le_of_splitJ 140 141 (by norm_num) (by norm_num) rows22000E_709 c22000E_140_3 (by norm_num)

theorem c22000E_140_1 : rowsJD 140 141 48 272 ≤ 2505185578666711 :=
  rowsJD_le_of_splitJ 140 141 (by norm_num) (by norm_num) rows22000E_708 c22000E_140_2 (by norm_num)

theorem c22000E_140_0 : rowsJD 140 141 0 272 ≤ 2581835102318614 :=
  rowsJD_le_of_splitJ 140 141 (by norm_num) (by norm_num) rows22000E_707 c22000E_140_1 (by norm_num)

theorem c22000E_141_5 : rowsJD 141 142 108 272 ≤ 1670607062809156 :=
  rowsJD_le_of_splitJ 141 142 (by norm_num) (by norm_num) rows22000E_719 rows22000E_720 (by norm_num)

theorem c22000E_141_4 : rowsJD 141 142 99 272 ≤ 2024053725500442 :=
  rowsJD_le_of_splitJ 141 142 (by norm_num) (by norm_num) rows22000E_718 c22000E_141_5 (by norm_num)

theorem c22000E_141_3 : rowsJD 141 142 72 272 ≤ 2313554037765004 :=
  rowsJD_le_of_splitJ 141 142 (by norm_num) (by norm_num) rows22000E_717 c22000E_141_4 (by norm_num)

theorem c22000E_141_2 : rowsJD 141 142 61 272 ≤ 2506924132907939 :=
  rowsJD_le_of_splitJ 141 142 (by norm_num) (by norm_num) rows22000E_716 c22000E_141_3 (by norm_num)

theorem c22000E_141_1 : rowsJD 141 142 48 272 ≤ 2533999251849477 :=
  rowsJD_le_of_splitJ 141 142 (by norm_num) (by norm_num) rows22000E_715 c22000E_141_2 (by norm_num)

theorem c22000E_141_0 : rowsJD 141 142 0 272 ≤ 2608054483600499 :=
  rowsJD_le_of_splitJ 141 142 (by norm_num) (by norm_num) rows22000E_714 c22000E_141_1 (by norm_num)

theorem c22000E_142_5 : rowsJD 142 143 108 272 ≤ 1600513631432942 :=
  rowsJD_le_of_splitJ 142 143 (by norm_num) (by norm_num) rows22000E_726 rows22000E_727 (by norm_num)

theorem c22000E_142_4 : rowsJD 142 143 99 272 ≤ 1987654769892741 :=
  rowsJD_le_of_splitJ 142 143 (by norm_num) (by norm_num) rows22000E_725 c22000E_142_5 (by norm_num)

theorem c22000E_142_3 : rowsJD 142 143 90 272 ≤ 2340390807409945 :=
  rowsJD_le_of_splitJ 142 143 (by norm_num) (by norm_num) rows22000E_724 c22000E_142_4 (by norm_num)

theorem c22000E_142_2 : rowsJD 142 143 61 272 ≤ 2577388389320518 :=
  rowsJD_le_of_splitJ 142 143 (by norm_num) (by norm_num) rows22000E_723 c22000E_142_3 (by norm_num)

theorem c22000E_142_1 : rowsJD 142 143 48 272 ≤ 2602544269002804 :=
  rowsJD_le_of_splitJ 142 143 (by norm_num) (by norm_num) rows22000E_722 c22000E_142_2 (by norm_num)

theorem c22000E_142_0 : rowsJD 142 143 0 272 ≤ 2674273801265533 :=
  rowsJD_le_of_splitJ 142 143 (by norm_num) (by norm_num) rows22000E_721 c22000E_142_1 (by norm_num)

theorem c22000E_143_5 : rowsJD 143 144 107 272 ≤ 1581549875235673 :=
  rowsJD_le_of_splitJ 143 144 (by norm_num) (by norm_num) rows22000E_733 rows22000E_734 (by norm_num)

theorem c22000E_143_4 : rowsJD 143 144 98 272 ≤ 2004471803485793 :=
  rowsJD_le_of_splitJ 143 144 (by norm_num) (by norm_num) rows22000E_732 c22000E_143_5 (by norm_num)

theorem c22000E_143_3 : rowsJD 143 144 90 272 ≤ 2371710416932599 :=
  rowsJD_le_of_splitJ 143 144 (by norm_num) (by norm_num) rows22000E_731 c22000E_143_4 (by norm_num)

theorem c22000E_143_2 : rowsJD 143 144 61 272 ≤ 2649913807514433 :=
  rowsJD_le_of_splitJ 143 144 (by norm_num) (by norm_num) rows22000E_730 c22000E_143_3 (by norm_num)

theorem c22000E_143_1 : rowsJD 143 144 48 272 ≤ 2673059373208734 :=
  rowsJD_le_of_splitJ 143 144 (by norm_num) (by norm_num) rows22000E_729 c22000E_143_2 (by norm_num)

theorem c22000E_143_0 : rowsJD 143 144 0 272 ≤ 2741795188361032 :=
  rowsJD_le_of_splitJ 143 144 (by norm_num) (by norm_num) rows22000E_728 c22000E_143_1 (by norm_num)

theorem c22000E_144_5 : rowsJD 144 145 106 272 ≤ 1670391792900890 :=
  rowsJD_le_of_splitJ 144 145 (by norm_num) (by norm_num) rows22000E_740 rows22000E_741 (by norm_num)

theorem c22000E_144_4 : rowsJD 144 145 98 272 ≤ 2089490010798562 :=
  rowsJD_le_of_splitJ 144 145 (by norm_num) (by norm_num) rows22000E_739 c22000E_144_5 (by norm_num)

theorem c22000E_144_3 : rowsJD 144 145 90 272 ≤ 2511271285271282 :=
  rowsJD_le_of_splitJ 144 145 (by norm_num) (by norm_num) rows22000E_738 c22000E_144_4 (by norm_num)

theorem c22000E_144_2 : rowsJD 144 145 60 272 ≤ 2816250974752621 :=
  rowsJD_le_of_splitJ 144 145 (by norm_num) (by norm_num) rows22000E_737 c22000E_144_3 (by norm_num)

theorem c22000E_144_1 : rowsJD 144 145 48 272 ≤ 2836532323531363 :=
  rowsJD_le_of_splitJ 144 145 (by norm_num) (by norm_num) rows22000E_736 c22000E_144_2 (by norm_num)

theorem c22000E_144_0 : rowsJD 144 145 0 272 ≤ 2902571404613702 :=
  rowsJD_le_of_splitJ 144 145 (by norm_num) (by norm_num) rows22000E_735 c22000E_144_1 (by norm_num)

theorem c22000E_145_5 : rowsJD 145 146 105 272 ≤ 1862847695404751 :=
  rowsJD_le_of_splitJ 145 146 (by norm_num) (by norm_num) rows22000E_747 rows22000E_748 (by norm_num)

theorem c22000E_145_4 : rowsJD 145 146 97 272 ≤ 2306171997687210 :=
  rowsJD_le_of_splitJ 145 146 (by norm_num) (by norm_num) rows22000E_746 c22000E_145_5 (by norm_num)

theorem c22000E_145_3 : rowsJD 145 146 89 272 ≤ 2762878932125930 :=
  rowsJD_le_of_splitJ 145 146 (by norm_num) (by norm_num) rows22000E_745 c22000E_145_4 (by norm_num)

theorem c22000E_145_2 : rowsJD 145 146 60 272 ≤ 3046548725463959 :=
  rowsJD_le_of_splitJ 145 146 (by norm_num) (by norm_num) rows22000E_744 c22000E_145_3 (by norm_num)

theorem c22000E_145_1 : rowsJD 145 146 48 272 ≤ 3066353976714626 :=
  rowsJD_le_of_splitJ 145 146 (by norm_num) (by norm_num) rows22000E_743 c22000E_145_2 (by norm_num)

theorem c22000E_145_0 : rowsJD 145 146 0 272 ≤ 3129097552229963 :=
  rowsJD_le_of_splitJ 145 146 (by norm_num) (by norm_num) rows22000E_742 c22000E_145_1 (by norm_num)

theorem c22000E_146_5 : rowsJD 146 147 105 272 ≤ 1999048745568494 :=
  rowsJD_le_of_splitJ 146 147 (by norm_num) (by norm_num) rows22000E_754 rows22000E_755 (by norm_num)

theorem c22000E_146_4 : rowsJD 146 147 97 272 ≤ 2462738702610089 :=
  rowsJD_le_of_splitJ 146 147 (by norm_num) (by norm_num) rows22000E_753 c22000E_146_5 (by norm_num)

theorem c22000E_146_3 : rowsJD 146 147 89 272 ≤ 2952117635896597 :=
  rowsJD_le_of_splitJ 146 147 (by norm_num) (by norm_num) rows22000E_752 c22000E_146_4 (by norm_num)

theorem c22000E_146_2 : rowsJD 146 147 60 272 ≤ 3246547756188209 :=
  rowsJD_le_of_splitJ 146 147 (by norm_num) (by norm_num) rows22000E_751 c22000E_146_3 (by norm_num)

theorem c22000E_146_1 : rowsJD 146 147 48 272 ≤ 3265645343952211 :=
  rowsJD_le_of_splitJ 146 147 (by norm_num) (by norm_num) rows22000E_750 c22000E_146_2 (by norm_num)

theorem c22000E_146_0 : rowsJD 146 147 0 272 ≤ 3324929452395194 :=
  rowsJD_le_of_splitJ 146 147 (by norm_num) (by norm_num) rows22000E_749 c22000E_146_1 (by norm_num)

theorem c22000E_147_5 : rowsJD 147 148 104 272 ≤ 2178861551802812 :=
  rowsJD_le_of_splitJ 147 148 (by norm_num) (by norm_num) rows22000E_761 rows22000E_762 (by norm_num)

theorem c22000E_147_4 : rowsJD 147 148 97 272 ≤ 2595507993141042 :=
  rowsJD_le_of_splitJ 147 148 (by norm_num) (by norm_num) rows22000E_760 c22000E_147_5 (by norm_num)

theorem c22000E_147_3 : rowsJD 147 148 89 272 ≤ 3098912852571813 :=
  rowsJD_le_of_splitJ 147 148 (by norm_num) (by norm_num) rows22000E_759 c22000E_147_4 (by norm_num)

theorem c22000E_147_2 : rowsJD 147 148 60 272 ≤ 3406258748519429 :=
  rowsJD_le_of_splitJ 147 148 (by norm_num) (by norm_num) rows22000E_758 c22000E_147_3 (by norm_num)

theorem c22000E_147_1 : rowsJD 147 148 48 272 ≤ 3424481509047273 :=
  rowsJD_le_of_splitJ 147 148 (by norm_num) (by norm_num) rows22000E_757 c22000E_147_2 (by norm_num)

theorem c22000E_147_0 : rowsJD 147 148 0 272 ≤ 3479692573218274 :=
  rowsJD_le_of_splitJ 147 148 (by norm_num) (by norm_num) rows22000E_756 c22000E_147_1 (by norm_num)

theorem c22000E_148_6 : rowsJD 148 149 110 272 ≤ 1903255591183679 :=
  rowsJD_le_of_splitJ 148 149 (by norm_num) (by norm_num) rows22000E_769 rows22000E_770 (by norm_num)

theorem c22000E_148_5 : rowsJD 148 149 104 272 ≤ 2282440865168490 :=
  rowsJD_le_of_splitJ 148 149 (by norm_num) (by norm_num) rows22000E_768 c22000E_148_6 (by norm_num)

theorem c22000E_148_4 : rowsJD 148 149 97 272 ≤ 2704757223084253 :=
  rowsJD_le_of_splitJ 148 149 (by norm_num) (by norm_num) rows22000E_767 c22000E_148_5 (by norm_num)

theorem c22000E_148_3 : rowsJD 148 149 89 272 ≤ 3207721093509271 :=
  rowsJD_le_of_splitJ 148 149 (by norm_num) (by norm_num) rows22000E_766 c22000E_148_4 (by norm_num)

theorem c22000E_148_2 : rowsJD 148 149 60 272 ≤ 3520882951731630 :=
  rowsJD_le_of_splitJ 148 149 (by norm_num) (by norm_num) rows22000E_765 c22000E_148_3 (by norm_num)

theorem c22000E_148_1 : rowsJD 148 149 48 272 ≤ 3538825815582007 :=
  rowsJD_le_of_splitJ 148 149 (by norm_num) (by norm_num) rows22000E_764 c22000E_148_2 (by norm_num)

theorem c22000E_148_0 : rowsJD 148 149 0 272 ≤ 3590565416036702 :=
  rowsJD_le_of_splitJ 148 149 (by norm_num) (by norm_num) rows22000E_763 c22000E_148_1 (by norm_num)

theorem c22000E_149_6 : rowsJD 149 150 109 272 ≤ 2063029324096613 :=
  rowsJD_le_of_splitJ 149 150 (by norm_num) (by norm_num) rows22000E_777 rows22000E_778 (by norm_num)

theorem c22000E_149_5 : rowsJD 149 150 103 272 ≤ 2461741111206415 :=
  rowsJD_le_of_splitJ 149 150 (by norm_num) (by norm_num) rows22000E_776 c22000E_149_6 (by norm_num)

theorem c22000E_149_4 : rowsJD 149 150 96 272 ≤ 2909661961546360 :=
  rowsJD_le_of_splitJ 149 150 (by norm_num) (by norm_num) rows22000E_775 c22000E_149_5 (by norm_num)

theorem c22000E_149_3 : rowsJD 149 150 88 272 ≤ 3397256528123082 :=
  rowsJD_le_of_splitJ 149 150 (by norm_num) (by norm_num) rows22000E_774 c22000E_149_4 (by norm_num)

theorem c22000E_149_2 : rowsJD 149 150 58 272 ≤ 3668736626322985 :=
  rowsJD_le_of_splitJ 149 150 (by norm_num) (by norm_num) rows22000E_773 c22000E_149_3 (by norm_num)

theorem c22000E_149_1 : rowsJD 149 150 47 272 ≤ 3684486476737786 :=
  rowsJD_le_of_splitJ 149 150 (by norm_num) (by norm_num) rows22000E_772 c22000E_149_2 (by norm_num)

theorem c22000E_149_0 : rowsJD 149 150 0 272 ≤ 3732652190396555 :=
  rowsJD_le_of_splitJ 149 150 (by norm_num) (by norm_num) rows22000E_771 c22000E_149_1 (by norm_num)

theorem c22000E_150_6 : rowsJD 150 151 109 272 ≤ 2158303170465636 :=
  rowsJD_le_of_splitJ 150 151 (by norm_num) (by norm_num) rows22000E_785 rows22000E_786 (by norm_num)

theorem c22000E_150_5 : rowsJD 150 151 103 272 ≤ 2574089122228933 :=
  rowsJD_le_of_splitJ 150 151 (by norm_num) (by norm_num) rows22000E_784 c22000E_150_6 (by norm_num)

theorem c22000E_150_4 : rowsJD 150 151 96 272 ≤ 3053135510667870 :=
  rowsJD_le_of_splitJ 150 151 (by norm_num) (by norm_num) rows22000E_783 c22000E_150_5 (by norm_num)

theorem c22000E_150_3 : rowsJD 150 151 88 272 ≤ 3529501060991095 :=
  rowsJD_le_of_splitJ 150 151 (by norm_num) (by norm_num) rows22000E_782 c22000E_150_4 (by norm_num)

theorem c22000E_150_2 : rowsJD 150 151 58 272 ≤ 3802320858421311 :=
  rowsJD_le_of_splitJ 150 151 (by norm_num) (by norm_num) rows22000E_781 c22000E_150_3 (by norm_num)

theorem c22000E_150_1 : rowsJD 150 151 47 272 ≤ 3817870998001341 :=
  rowsJD_le_of_splitJ 150 151 (by norm_num) (by norm_num) rows22000E_780 c22000E_150_2 (by norm_num)

theorem c22000E_150_0 : rowsJD 150 151 0 272 ≤ 3863028169419903 :=
  rowsJD_le_of_splitJ 150 151 (by norm_num) (by norm_num) rows22000E_779 c22000E_150_1 (by norm_num)

theorem c22000E_151_6 : rowsJD 151 152 109 272 ≤ 2249476566366625 :=
  rowsJD_le_of_splitJ 151 152 (by norm_num) (by norm_num) rows22000E_793 rows22000E_794 (by norm_num)

theorem c22000E_151_5 : rowsJD 151 152 103 272 ≤ 2686467790014438 :=
  rowsJD_le_of_splitJ 151 152 (by norm_num) (by norm_num) rows22000E_792 c22000E_151_6 (by norm_num)

theorem c22000E_151_4 : rowsJD 151 152 96 272 ≤ 3197400565271842 :=
  rowsJD_le_of_splitJ 151 152 (by norm_num) (by norm_num) rows22000E_791 c22000E_151_5 (by norm_num)

theorem c22000E_151_3 : rowsJD 151 152 88 272 ≤ 3660631016552135 :=
  rowsJD_le_of_splitJ 151 152 (by norm_num) (by norm_num) rows22000E_790 c22000E_151_4 (by norm_num)

theorem c22000E_151_2 : rowsJD 151 152 59 272 ≤ 3933763378180738 :=
  rowsJD_le_of_splitJ 151 152 (by norm_num) (by norm_num) rows22000E_789 c22000E_151_3 (by norm_num)

theorem c22000E_151_1 : rowsJD 151 152 47 272 ≤ 3951642350505745 :=
  rowsJD_le_of_splitJ 151 152 (by norm_num) (by norm_num) rows22000E_788 c22000E_151_2 (by norm_num)

theorem c22000E_151_0 : rowsJD 151 152 0 272 ≤ 3993384333149286 :=
  rowsJD_le_of_splitJ 151 152 (by norm_num) (by norm_num) rows22000E_787 c22000E_151_1 (by norm_num)

theorem c22000E_152_6 : rowsJD 152 153 108 272 ≤ 2406456493782069 :=
  rowsJD_le_of_splitJ 152 153 (by norm_num) (by norm_num) rows22000E_801 rows22000E_802 (by norm_num)

theorem c22000E_152_5 : rowsJD 152 153 103 272 ≤ 2798522365960912 :=
  rowsJD_le_of_splitJ 152 153 (by norm_num) (by norm_num) rows22000E_800 c22000E_152_6 (by norm_num)

theorem c22000E_152_4 : rowsJD 152 153 96 272 ≤ 3342500997477058 :=
  rowsJD_le_of_splitJ 152 153 (by norm_num) (by norm_num) rows22000E_799 c22000E_152_5 (by norm_num)

theorem c22000E_152_3 : rowsJD 152 153 88 272 ≤ 3794456962048307 :=
  rowsJD_le_of_splitJ 152 153 (by norm_num) (by norm_num) rows22000E_798 c22000E_152_4 (by norm_num)

theorem c22000E_152_2 : rowsJD 152 153 59 272 ≤ 4079261060913846 :=
  rowsJD_le_of_splitJ 152 153 (by norm_num) (by norm_num) rows22000E_797 c22000E_152_3 (by norm_num)

theorem c22000E_152_1 : rowsJD 152 153 47 272 ≤ 4097958337857538 :=
  rowsJD_le_of_splitJ 152 153 (by norm_num) (by norm_num) rows22000E_796 c22000E_152_2 (by norm_num)

theorem c22000E_152_0 : rowsJD 152 153 0 272 ≤ 4137258200708527 :=
  rowsJD_le_of_splitJ 152 153 (by norm_num) (by norm_num) rows22000E_795 c22000E_152_1 (by norm_num)

theorem c22000E_153_6 : rowsJD 153 154 107 272 ≤ 2564481403485130 :=
  rowsJD_le_of_splitJ 153 154 (by norm_num) (by norm_num) rows22000E_809 rows22000E_810 (by norm_num)

theorem c22000E_153_5 : rowsJD 153 154 102 272 ≤ 2972067150728200 :=
  rowsJD_le_of_splitJ 153 154 (by norm_num) (by norm_num) rows22000E_808 c22000E_153_6 (by norm_num)

theorem c22000E_153_4 : rowsJD 153 154 96 272 ≤ 3444165805566804 :=
  rowsJD_le_of_splitJ 153 154 (by norm_num) (by norm_num) rows22000E_807 c22000E_153_5 (by norm_num)

theorem c22000E_153_3 : rowsJD 153 154 88 272 ≤ 3871517030470947 :=
  rowsJD_le_of_splitJ 153 154 (by norm_num) (by norm_num) rows22000E_806 c22000E_153_4 (by norm_num)

theorem c22000E_153_2 : rowsJD 153 154 58 272 ≤ 4183558202232688 :=
  rowsJD_le_of_splitJ 153 154 (by norm_num) (by norm_num) rows22000E_805 c22000E_153_3 (by norm_num)

theorem c22000E_153_1 : rowsJD 153 154 46 272 ≤ 4202062295984163 :=
  rowsJD_le_of_splitJ 153 154 (by norm_num) (by norm_num) rows22000E_804 c22000E_153_2 (by norm_num)

theorem c22000E_153_0 : rowsJD 153 154 0 272 ≤ 4238037086002237 :=
  rowsJD_le_of_splitJ 153 154 (by norm_num) (by norm_num) rows22000E_803 c22000E_153_1 (by norm_num)

theorem c22000E_154_6 : rowsJD 154 155 107 272 ≤ 2653146892884397 :=
  rowsJD_le_of_splitJ 154 155 (by norm_num) (by norm_num) rows22000E_817 rows22000E_818 (by norm_num)

theorem c22000E_154_5 : rowsJD 154 155 102 272 ≤ 3078542624893784 :=
  rowsJD_le_of_splitJ 154 155 (by norm_num) (by norm_num) rows22000E_816 c22000E_154_6 (by norm_num)

theorem c22000E_154_4 : rowsJD 154 155 96 272 ≤ 3560734114072477 :=
  rowsJD_le_of_splitJ 154 155 (by norm_num) (by norm_num) rows22000E_815 c22000E_154_5 (by norm_num)

theorem c22000E_154_3 : rowsJD 154 155 88 272 ≤ 3967375719420906 :=
  rowsJD_le_of_splitJ 154 155 (by norm_num) (by norm_num) rows22000E_814 c22000E_154_4 (by norm_num)

theorem c22000E_154_2 : rowsJD 154 155 58 272 ≤ 4311012103768794 :=
  rowsJD_le_of_splitJ 154 155 (by norm_num) (by norm_num) rows22000E_813 c22000E_154_3 (by norm_num)

theorem c22000E_154_1 : rowsJD 154 155 46 272 ≤ 4330727730326824 :=
  rowsJD_le_of_splitJ 154 155 (by norm_num) (by norm_num) rows22000E_812 c22000E_154_2 (by norm_num)

theorem c22000E_154_0 : rowsJD 154 155 0 272 ≤ 4364699375581863 :=
  rowsJD_le_of_splitJ 154 155 (by norm_num) (by norm_num) rows22000E_811 c22000E_154_1 (by norm_num)

theorem c22000E_155_6 : rowsJD 155 156 108 272 ≤ 2693925732380830 :=
  rowsJD_le_of_splitJ 155 156 (by norm_num) (by norm_num) rows22000E_825 rows22000E_826 (by norm_num)

theorem c22000E_155_5 : rowsJD 155 156 103 272 ≤ 3134497915263937 :=
  rowsJD_le_of_splitJ 155 156 (by norm_num) (by norm_num) rows22000E_824 c22000E_155_6 (by norm_num)

theorem c22000E_155_4 : rowsJD 155 156 97 272 ≤ 3640878429295474 :=
  rowsJD_le_of_splitJ 155 156 (by norm_num) (by norm_num) rows22000E_823 c22000E_155_5 (by norm_num)

theorem c22000E_155_3 : rowsJD 155 156 89 272 ≤ 4054494814922631 :=
  rowsJD_le_of_splitJ 155 156 (by norm_num) (by norm_num) rows22000E_822 c22000E_155_4 (by norm_num)

theorem c22000E_155_2 : rowsJD 155 156 77 272 ≤ 4464582480865156 :=
  rowsJD_le_of_splitJ 155 156 (by norm_num) (by norm_num) rows22000E_821 c22000E_155_3 (by norm_num)

theorem c22000E_155_1 : rowsJD 155 156 46 272 ≤ 4495216245691989 :=
  rowsJD_le_of_splitJ 155 156 (by norm_num) (by norm_num) rows22000E_820 c22000E_155_2 (by norm_num)

theorem c22000E_155_0 : rowsJD 155 156 0 272 ≤ 4527145141456550 :=
  rowsJD_le_of_splitJ 155 156 (by norm_num) (by norm_num) rows22000E_819 c22000E_155_1 (by norm_num)

theorem c22000E_156_6 : rowsJD 156 157 108 272 ≤ 2831325069877171 :=
  rowsJD_le_of_splitJ 156 157 (by norm_num) (by norm_num) rows22000E_833 rows22000E_834 (by norm_num)

theorem c22000E_156_5 : rowsJD 156 157 103 272 ≤ 3296185933293825 :=
  rowsJD_le_of_splitJ 156 157 (by norm_num) (by norm_num) rows22000E_832 c22000E_156_6 (by norm_num)

theorem c22000E_156_4 : rowsJD 156 157 97 272 ≤ 3800307216254340 :=
  rowsJD_le_of_splitJ 156 157 (by norm_num) (by norm_num) rows22000E_831 c22000E_156_5 (by norm_num)

theorem c22000E_156_3 : rowsJD 156 157 89 272 ≤ 4198757818675214 :=
  rowsJD_le_of_splitJ 156 157 (by norm_num) (by norm_num) rows22000E_830 c22000E_156_4 (by norm_num)

theorem c22000E_156_2 : rowsJD 156 157 77 272 ≤ 4637155162418717 :=
  rowsJD_le_of_splitJ 156 157 (by norm_num) (by norm_num) rows22000E_829 c22000E_156_3 (by norm_num)

theorem c22000E_156_1 : rowsJD 156 157 46 272 ≤ 4679099025113920 :=
  rowsJD_le_of_splitJ 156 157 (by norm_num) (by norm_num) rows22000E_828 c22000E_156_2 (by norm_num)

theorem c22000E_156_0 : rowsJD 156 157 0 272 ≤ 4709658050931733 :=
  rowsJD_le_of_splitJ 156 157 (by norm_num) (by norm_num) rows22000E_827 c22000E_156_1 (by norm_num)

theorem c22000E_157_6 : rowsJD 157 158 107 272 ≤ 3087041866697712 :=
  rowsJD_le_of_splitJ 157 158 (by norm_num) (by norm_num) rows22000E_841 rows22000E_842 (by norm_num)

theorem c22000E_157_5 : rowsJD 157 158 102 272 ≤ 3586386290674940 :=
  rowsJD_le_of_splitJ 157 158 (by norm_num) (by norm_num) rows22000E_840 c22000E_157_6 (by norm_num)

theorem c22000E_157_4 : rowsJD 157 158 96 272 ≤ 4050250530924413 :=
  rowsJD_le_of_splitJ 157 158 (by norm_num) (by norm_num) rows22000E_839 c22000E_157_5 (by norm_num)

theorem c22000E_157_3 : rowsJD 157 158 88 272 ≤ 4417672048959299 :=
  rowsJD_le_of_splitJ 157 158 (by norm_num) (by norm_num) rows22000E_838 c22000E_157_4 (by norm_num)

theorem c22000E_157_2 : rowsJD 157 158 76 272 ≤ 4866409016255388 :=
  rowsJD_le_of_splitJ 157 158 (by norm_num) (by norm_num) rows22000E_837 c22000E_157_3 (by norm_num)

theorem c22000E_157_1 : rowsJD 157 158 45 272 ≤ 4907088594035445 :=
  rowsJD_le_of_splitJ 157 158 (by norm_num) (by norm_num) rows22000E_836 c22000E_157_2 (by norm_num)

theorem c22000E_157_0 : rowsJD 157 158 0 272 ≤ 4935092592250484 :=
  rowsJD_le_of_splitJ 157 158 (by norm_num) (by norm_num) rows22000E_835 c22000E_157_1 (by norm_num)

theorem c22000E_158_6 : rowsJD 158 159 106 272 ≤ 3350549960273794 :=
  rowsJD_le_of_splitJ 158 159 (by norm_num) (by norm_num) rows22000E_849 rows22000E_850 (by norm_num)

theorem c22000E_158_5 : rowsJD 158 159 102 272 ≤ 3780129240441189 :=
  rowsJD_le_of_splitJ 158 159 (by norm_num) (by norm_num) rows22000E_848 c22000E_158_6 (by norm_num)

theorem c22000E_158_4 : rowsJD 158 159 96 272 ≤ 4242654731156793 :=
  rowsJD_le_of_splitJ 158 159 (by norm_num) (by norm_num) rows22000E_847 c22000E_158_5 (by norm_num)

theorem c22000E_158_3 : rowsJD 158 159 88 272 ≤ 4610497311423218 :=
  rowsJD_le_of_splitJ 158 159 (by norm_num) (by norm_num) rows22000E_846 c22000E_158_4 (by norm_num)

theorem c22000E_158_2 : rowsJD 158 159 76 272 ≤ 5083304804152098 :=
  rowsJD_le_of_splitJ 158 159 (by norm_num) (by norm_num) rows22000E_845 c22000E_158_3 (by norm_num)

theorem c22000E_158_1 : rowsJD 158 159 45 272 ≤ 5136664101383466 :=
  rowsJD_le_of_splitJ 158 159 (by norm_num) (by norm_num) rows22000E_844 c22000E_158_2 (by norm_num)

theorem c22000E_158_0 : rowsJD 158 159 0 272 ≤ 5163634621471257 :=
  rowsJD_le_of_splitJ 158 159 (by norm_num) (by norm_num) rows22000E_843 c22000E_158_1 (by norm_num)

theorem c22000E_159_6 : rowsJD 159 160 106 272 ≤ 3497761576896075 :=
  rowsJD_le_of_splitJ 159 160 (by norm_num) (by norm_num) rows22000E_857 rows22000E_858 (by norm_num)

theorem c22000E_159_5 : rowsJD 159 160 102 272 ≤ 3955648281472187 :=
  rowsJD_le_of_splitJ 159 160 (by norm_num) (by norm_num) rows22000E_856 c22000E_159_6 (by norm_num)

theorem c22000E_159_4 : rowsJD 159 160 97 272 ≤ 4360161342202627 :=
  rowsJD_le_of_splitJ 159 160 (by norm_num) (by norm_num) rows22000E_855 c22000E_159_5 (by norm_num)

theorem c22000E_159_3 : rowsJD 159 160 89 272 ≤ 4748729263894232 :=
  rowsJD_le_of_splitJ 159 160 (by norm_num) (by norm_num) rows22000E_854 c22000E_159_4 (by norm_num)

theorem c22000E_159_2 : rowsJD 159 160 77 272 ≤ 5255152104911585 :=
  rowsJD_le_of_splitJ 159 160 (by norm_num) (by norm_num) rows22000E_853 c22000E_159_3 (by norm_num)

theorem c22000E_159_1 : rowsJD 159 160 45 272 ≤ 5352298166315158 :=
  rowsJD_le_of_splitJ 159 160 (by norm_num) (by norm_num) rows22000E_852 c22000E_159_2 (by norm_num)

theorem c22000E_159_0 : rowsJD 159 160 0 272 ≤ 5378391913057998 :=
  rowsJD_le_of_splitJ 159 160 (by norm_num) (by norm_num) rows22000E_851 c22000E_159_1 (by norm_num)

theorem c22000E_160_5 : rowsJD 160 161 103 272 ≤ 3990765855774943 :=
  rowsJD_le_of_splitJ 160 161 (by norm_num) (by norm_num) rows22000E_864 rows22000E_865 (by norm_num)

theorem c22000E_160_4 : rowsJD 160 161 98 272 ≤ 4438147733779605 :=
  rowsJD_le_of_splitJ 160 161 (by norm_num) (by norm_num) rows22000E_863 c22000E_160_5 (by norm_num)

theorem c22000E_160_3 : rowsJD 160 161 90 272 ≤ 4855783967817174 :=
  rowsJD_le_of_splitJ 160 161 (by norm_num) (by norm_num) rows22000E_862 c22000E_160_4 (by norm_num)

theorem c22000E_160_2 : rowsJD 160 161 78 272 ≤ 5384504666470301 :=
  rowsJD_le_of_splitJ 160 161 (by norm_num) (by norm_num) rows22000E_861 c22000E_160_3 (by norm_num)

theorem c22000E_160_1 : rowsJD 160 161 45 272 ≤ 5540583275374744 :=
  rowsJD_le_of_splitJ 160 161 (by norm_num) (by norm_num) rows22000E_860 c22000E_160_2 (by norm_num)

theorem c22000E_160_0 : rowsJD 160 161 0 272 ≤ 5566416892202990 :=
  rowsJD_le_of_splitJ 160 161 (by norm_num) (by norm_num) rows22000E_859 c22000E_160_1 (by norm_num)

theorem c22000E_161_5 : rowsJD 161 162 102 272 ≤ 4170866714415841 :=
  rowsJD_le_of_splitJ 161 162 (by norm_num) (by norm_num) rows22000E_871 rows22000E_872 (by norm_num)

theorem c22000E_161_4 : rowsJD 161 162 97 272 ≤ 4578475837402479 :=
  rowsJD_le_of_splitJ 161 162 (by norm_num) (by norm_num) rows22000E_870 c22000E_161_5 (by norm_num)

theorem c22000E_161_3 : rowsJD 161 162 89 272 ≤ 4960340150894500 :=
  rowsJD_le_of_splitJ 161 162 (by norm_num) (by norm_num) rows22000E_869 c22000E_161_4 (by norm_num)

theorem c22000E_161_2 : rowsJD 161 162 76 272 ≤ 5526120102197200 :=
  rowsJD_le_of_splitJ 161 162 (by norm_num) (by norm_num) rows22000E_868 c22000E_161_3 (by norm_num)

theorem c22000E_161_1 : rowsJD 161 162 44 272 ≤ 5651685231936232 :=
  rowsJD_le_of_splitJ 161 162 (by norm_num) (by norm_num) rows22000E_867 c22000E_161_2 (by norm_num)

theorem c22000E_161_0 : rowsJD 161 162 0 272 ≤ 5675123522945788 :=
  rowsJD_le_of_splitJ 161 162 (by norm_num) (by norm_num) rows22000E_866 c22000E_161_1 (by norm_num)

theorem c22000E_162_5 : rowsJD 162 163 102 272 ≤ 4232101750411618 :=
  rowsJD_le_of_splitJ 162 163 (by norm_num) (by norm_num) rows22000E_878 rows22000E_879 (by norm_num)

theorem c22000E_162_4 : rowsJD 162 163 97 272 ≤ 4633547259540445 :=
  rowsJD_le_of_splitJ 162 163 (by norm_num) (by norm_num) rows22000E_877 c22000E_162_5 (by norm_num)

theorem c22000E_162_3 : rowsJD 162 163 89 272 ≤ 5012764740735904 :=
  rowsJD_le_of_splitJ 162 163 (by norm_num) (by norm_num) rows22000E_876 c22000E_162_4 (by norm_num)

theorem c22000E_162_2 : rowsJD 162 163 77 272 ≤ 5559204464529266 :=
  rowsJD_le_of_splitJ 162 163 (by norm_num) (by norm_num) rows22000E_875 c22000E_162_3 (by norm_num)

theorem c22000E_162_1 : rowsJD 162 163 44 272 ≤ 5754479242620029 :=
  rowsJD_le_of_splitJ 162 163 (by norm_num) (by norm_num) rows22000E_874 c22000E_162_2 (by norm_num)

theorem c22000E_162_0 : rowsJD 162 163 0 272 ≤ 5778311526166342 :=
  rowsJD_le_of_splitJ 162 163 (by norm_num) (by norm_num) rows22000E_873 c22000E_162_1 (by norm_num)

theorem c22000E_163_5 : rowsJD 163 164 102 272 ≤ 4290422355451238 :=
  rowsJD_le_of_splitJ 163 164 (by norm_num) (by norm_num) rows22000E_885 rows22000E_886 (by norm_num)

theorem c22000E_163_4 : rowsJD 163 164 97 272 ≤ 4681456064125838 :=
  rowsJD_le_of_splitJ 163 164 (by norm_num) (by norm_num) rows22000E_884 c22000E_163_5 (by norm_num)

theorem c22000E_163_3 : rowsJD 163 164 89 272 ≤ 5056447503463282 :=
  rowsJD_le_of_splitJ 163 164 (by norm_num) (by norm_num) rows22000E_883 c22000E_163_4 (by norm_num)

theorem c22000E_163_2 : rowsJD 163 164 77 272 ≤ 5623807892851162 :=
  rowsJD_le_of_splitJ 163 164 (by norm_num) (by norm_num) rows22000E_882 c22000E_163_3 (by norm_num)

theorem c22000E_163_1 : rowsJD 163 164 44 272 ≤ 5857938431779122 :=
  rowsJD_le_of_splitJ 163 164 (by norm_num) (by norm_num) rows22000E_881 c22000E_163_2 (by norm_num)

theorem c22000E_163_0 : rowsJD 163 164 0 272 ≤ 5881606952913144 :=
  rowsJD_le_of_splitJ 163 164 (by norm_num) (by norm_num) rows22000E_880 c22000E_163_1 (by norm_num)

theorem c22000E_164_4 : rowsJD 164 165 98 272 ≤ 4657208217362334 :=
  rowsJD_le_of_splitJ 164 165 (by norm_num) (by norm_num) rows22000E_891 rows22000E_892 (by norm_num)

theorem c22000E_164_3 : rowsJD 164 165 90 272 ≤ 5048328019373406 :=
  rowsJD_le_of_splitJ 164 165 (by norm_num) (by norm_num) rows22000E_890 c22000E_164_4 (by norm_num)

theorem c22000E_164_2 : rowsJD 164 165 78 272 ≤ 5630946756461913 :=
  rowsJD_le_of_splitJ 164 165 (by norm_num) (by norm_num) rows22000E_889 c22000E_164_3 (by norm_num)

theorem c22000E_164_1 : rowsJD 164 165 44 272 ≤ 5960590853862729 :=
  rowsJD_le_of_splitJ 164 165 (by norm_num) (by norm_num) rows22000E_888 c22000E_164_2 (by norm_num)

theorem c22000E_164_0 : rowsJD 164 165 0 272 ≤ 5984718162912297 :=
  rowsJD_le_of_splitJ 164 165 (by norm_num) (by norm_num) rows22000E_887 c22000E_164_1 (by norm_num)

theorem c22000E_165_4 : rowsJD 165 166 98 272 ≤ 4698670974996585 :=
  rowsJD_le_of_splitJ 165 166 (by norm_num) (by norm_num) rows22000E_897 rows22000E_898 (by norm_num)

theorem c22000E_165_3 : rowsJD 165 166 90 272 ≤ 5083438747028096 :=
  rowsJD_le_of_splitJ 165 166 (by norm_num) (by norm_num) rows22000E_896 c22000E_165_4 (by norm_num)

theorem c22000E_165_2 : rowsJD 165 166 78 272 ≤ 5704012139275774 :=
  rowsJD_le_of_splitJ 165 166 (by norm_num) (by norm_num) rows22000E_895 c22000E_165_3 (by norm_num)

theorem c22000E_165_1 : rowsJD 165 166 44 272 ≤ 6087975327368127 :=
  rowsJD_le_of_splitJ 165 166 (by norm_num) (by norm_num) rows22000E_894 c22000E_165_2 (by norm_num)

theorem c22000E_165_0 : rowsJD 165 166 0 272 ≤ 6112601885210489 :=
  rowsJD_le_of_splitJ 165 166 (by norm_num) (by norm_num) rows22000E_893 c22000E_165_1 (by norm_num)

theorem c22000E_166_4 : rowsJD 166 167 97 272 ≤ 4809027263686754 :=
  rowsJD_le_of_splitJ 166 167 (by norm_num) (by norm_num) rows22000E_903 rows22000E_904 (by norm_num)

theorem c22000E_166_3 : rowsJD 166 167 89 272 ≤ 5188977540211578 :=
  rowsJD_le_of_splitJ 166 167 (by norm_num) (by norm_num) rows22000E_902 c22000E_166_4 (by norm_num)

theorem c22000E_166_2 : rowsJD 166 167 77 272 ≤ 5865898003419387 :=
  rowsJD_le_of_splitJ 166 167 (by norm_num) (by norm_num) rows22000E_901 c22000E_166_3 (by norm_num)

theorem c22000E_166_1 : rowsJD 166 167 43 272 ≤ 6252563754163153 :=
  rowsJD_le_of_splitJ 166 167 (by norm_num) (by norm_num) rows22000E_900 c22000E_166_2 (by norm_num)

theorem c22000E_166_0 : rowsJD 166 167 0 272 ≤ 6276500612568160 :=
  rowsJD_le_of_splitJ 166 167 (by norm_num) (by norm_num) rows22000E_899 c22000E_166_1 (by norm_num)

theorem c22000E_167_4 : rowsJD 167 168 97 272 ≤ 4879429737658408 :=
  rowsJD_le_of_splitJ 167 168 (by norm_num) (by norm_num) rows22000E_909 rows22000E_910 (by norm_num)

theorem c22000E_167_3 : rowsJD 167 168 89 272 ≤ 5280612999259399 :=
  rowsJD_le_of_splitJ 167 168 (by norm_num) (by norm_num) rows22000E_908 c22000E_167_4 (by norm_num)

theorem c22000E_167_2 : rowsJD 167 168 78 272 ≤ 5939741829144267 :=
  rowsJD_le_of_splitJ 167 168 (by norm_num) (by norm_num) rows22000E_907 c22000E_167_3 (by norm_num)

theorem c22000E_167_1 : rowsJD 167 168 43 272 ≤ 6446179748994287 :=
  rowsJD_le_of_splitJ 167 168 (by norm_num) (by norm_num) rows22000E_906 c22000E_167_2 (by norm_num)

theorem c22000E_167_0 : rowsJD 167 168 0 272 ≤ 6470678443651109 :=
  rowsJD_le_of_splitJ 167 168 (by norm_num) (by norm_num) rows22000E_905 c22000E_167_1 (by norm_num)

theorem c22000E_168_4 : rowsJD 168 169 97 272 ≤ 4970524929495411 :=
  rowsJD_le_of_splitJ 168 169 (by norm_num) (by norm_num) rows22000E_915 rows22000E_916 (by norm_num)

theorem c22000E_168_3 : rowsJD 168 169 89 272 ≤ 5422100818311238 :=
  rowsJD_le_of_splitJ 168 169 (by norm_num) (by norm_num) rows22000E_914 c22000E_168_4 (by norm_num)

theorem c22000E_168_2 : rowsJD 168 169 78 272 ≤ 6123209982351839 :=
  rowsJD_le_of_splitJ 168 169 (by norm_num) (by norm_num) rows22000E_913 c22000E_168_3 (by norm_num)

theorem c22000E_168_1 : rowsJD 168 169 43 272 ≤ 6686469498798407 :=
  rowsJD_le_of_splitJ 168 169 (by norm_num) (by norm_num) rows22000E_912 c22000E_168_2 (by norm_num)

theorem c22000E_168_0 : rowsJD 168 169 0 272 ≤ 6712225322836373 :=
  rowsJD_le_of_splitJ 168 169 (by norm_num) (by norm_num) rows22000E_911 c22000E_168_1 (by norm_num)

theorem c22000E_169_4 : rowsJD 169 170 97 272 ≤ 5089558243541752 :=
  rowsJD_le_of_splitJ 169 170 (by norm_num) (by norm_num) rows22000E_921 rows22000E_922 (by norm_num)

theorem c22000E_169_3 : rowsJD 169 170 90 272 ≤ 5545276607378722 :=
  rowsJD_le_of_splitJ 169 170 (by norm_num) (by norm_num) rows22000E_920 c22000E_169_4 (by norm_num)

theorem c22000E_169_2 : rowsJD 169 170 79 272 ≤ 6260504774741571 :=
  rowsJD_le_of_splitJ 169 170 (by norm_num) (by norm_num) rows22000E_919 c22000E_169_3 (by norm_num)

theorem c22000E_169_1 : rowsJD 169 170 43 272 ≤ 6939283585905086 :=
  rowsJD_le_of_splitJ 169 170 (by norm_num) (by norm_num) rows22000E_918 c22000E_169_2 (by norm_num)

theorem c22000E_169_0 : rowsJD 169 170 0 272 ≤ 6966284247822183 :=
  rowsJD_le_of_splitJ 169 170 (by norm_num) (by norm_num) rows22000E_917 c22000E_169_1 (by norm_num)

theorem c22000E_170_3 : rowsJD 170 171 89 272 ≤ 5842675784910401 :=
  rowsJD_le_of_splitJ 170 171 (by norm_num) (by norm_num) rows22000E_926 rows22000E_927 (by norm_num)

theorem c22000E_170_2 : rowsJD 170 171 79 272 ≤ 6514692835194740 :=
  rowsJD_le_of_splitJ 170 171 (by norm_num) (by norm_num) rows22000E_925 c22000E_170_3 (by norm_num)

theorem c22000E_170_1 : rowsJD 170 171 43 272 ≤ 7232760942413848 :=
  rowsJD_le_of_splitJ 170 171 (by norm_num) (by norm_num) rows22000E_924 c22000E_170_2 (by norm_num)

theorem c22000E_170_0 : rowsJD 170 171 0 272 ≤ 7261919480013922 :=
  rowsJD_le_of_splitJ 170 171 (by norm_num) (by norm_num) rows22000E_923 c22000E_170_1 (by norm_num)

theorem c22000E_171_3 : rowsJD 171 172 89 272 ≤ 6066679997282608 :=
  rowsJD_le_of_splitJ 171 172 (by norm_num) (by norm_num) rows22000E_931 rows22000E_932 (by norm_num)

theorem c22000E_171_2 : rowsJD 171 172 79 272 ≤ 6759688110345884 :=
  rowsJD_le_of_splitJ 171 172 (by norm_num) (by norm_num) rows22000E_930 c22000E_171_3 (by norm_num)

theorem c22000E_171_1 : rowsJD 171 172 61 272 ≤ 7505408178044825 :=
  rowsJD_le_of_splitJ 171 172 (by norm_num) (by norm_num) rows22000E_929 c22000E_171_2 (by norm_num)

theorem c22000E_171_0 : rowsJD 171 172 0 272 ≤ 7535694023101195 :=
  rowsJD_le_of_splitJ 171 172 (by norm_num) (by norm_num) rows22000E_928 c22000E_171_1 (by norm_num)

theorem c22000E_172_3 : rowsJD 172 173 89 272 ≤ 6255598541157555 :=
  rowsJD_le_of_splitJ 172 173 (by norm_num) (by norm_num) rows22000E_936 rows22000E_937 (by norm_num)

theorem c22000E_172_2 : rowsJD 172 173 80 272 ≤ 6910965519424652 :=
  rowsJD_le_of_splitJ 172 173 (by norm_num) (by norm_num) rows22000E_935 c22000E_172_3 (by norm_num)

theorem c22000E_172_1 : rowsJD 172 173 62 272 ≤ 7716421342938437 :=
  rowsJD_le_of_splitJ 172 173 (by norm_num) (by norm_num) rows22000E_934 c22000E_172_2 (by norm_num)

theorem c22000E_172_0 : rowsJD 172 173 0 272 ≤ 7767139752255900 :=
  rowsJD_le_of_splitJ 172 173 (by norm_num) (by norm_num) rows22000E_933 c22000E_172_1 (by norm_num)

theorem c22000E_173_3 : rowsJD 173 174 89 272 ≤ 6419812251417853 :=
  rowsJD_le_of_splitJ 173 174 (by norm_num) (by norm_num) rows22000E_941 rows22000E_942 (by norm_num)

theorem c22000E_173_2 : rowsJD 173 174 80 272 ≤ 7101939502157692 :=
  rowsJD_le_of_splitJ 173 174 (by norm_num) (by norm_num) rows22000E_940 c22000E_173_3 (by norm_num)

theorem c22000E_173_1 : rowsJD 173 174 63 272 ≤ 7876791913655425 :=
  rowsJD_le_of_splitJ 173 174 (by norm_num) (by norm_num) rows22000E_939 c22000E_173_2 (by norm_num)

theorem c22000E_173_0 : rowsJD 173 174 0 272 ≤ 7964528543956649 :=
  rowsJD_le_of_splitJ 173 174 (by norm_num) (by norm_num) rows22000E_938 c22000E_173_1 (by norm_num)

theorem c22000E_174_3 : rowsJD 174 175 89 272 ≤ 6526491948988710 :=
  rowsJD_le_of_splitJ 174 175 (by norm_num) (by norm_num) rows22000E_946 rows22000E_947 (by norm_num)

theorem c22000E_174_2 : rowsJD 174 175 80 272 ≤ 7217654574595840 :=
  rowsJD_le_of_splitJ 174 175 (by norm_num) (by norm_num) rows22000E_945 c22000E_174_3 (by norm_num)

theorem c22000E_174_1 : rowsJD 174 175 64 272 ≤ 7918207845103921 :=
  rowsJD_le_of_splitJ 174 175 (by norm_num) (by norm_num) rows22000E_944 c22000E_174_2 (by norm_num)

theorem c22000E_174_0 : rowsJD 174 175 0 272 ≤ 8050537061967029 :=
  rowsJD_le_of_splitJ 174 175 (by norm_num) (by norm_num) rows22000E_943 c22000E_174_1 (by norm_num)

theorem c22000E_175_3 : rowsJD 175 176 88 272 ≤ 6614920710922669 :=
  rowsJD_le_of_splitJ 175 176 (by norm_num) (by norm_num) rows22000E_951 rows22000E_952 (by norm_num)

theorem c22000E_175_2 : rowsJD 175 176 80 272 ≤ 7216373906072843 :=
  rowsJD_le_of_splitJ 175 176 (by norm_num) (by norm_num) rows22000E_950 c22000E_175_3 (by norm_num)

theorem c22000E_175_1 : rowsJD 175 176 65 272 ≤ 7833984185848289 :=
  rowsJD_le_of_splitJ 175 176 (by norm_num) (by norm_num) rows22000E_949 c22000E_175_2 (by norm_num)

theorem c22000E_175_0 : rowsJD 175 176 0 272 ≤ 8005803487026076 :=
  rowsJD_le_of_splitJ 175 176 (by norm_num) (by norm_num) rows22000E_948 c22000E_175_1 (by norm_num)

theorem c22000E_176_3 : rowsJD 176 177 88 272 ≤ 6507325736574981 :=
  rowsJD_le_of_splitJ 176 177 (by norm_num) (by norm_num) rows22000E_956 rows22000E_957 (by norm_num)

theorem c22000E_176_2 : rowsJD 176 177 80 272 ≤ 7114802081254245 :=
  rowsJD_le_of_splitJ 176 177 (by norm_num) (by norm_num) rows22000E_955 c22000E_176_3 (by norm_num)

theorem c22000E_176_1 : rowsJD 176 177 65 272 ≤ 7683695090388728 :=
  rowsJD_le_of_splitJ 176 177 (by norm_num) (by norm_num) rows22000E_954 c22000E_176_2 (by norm_num)

theorem c22000E_176_0 : rowsJD 176 177 0 272 ≤ 7856291353803427 :=
  rowsJD_le_of_splitJ 176 177 (by norm_num) (by norm_num) rows22000E_953 c22000E_176_1 (by norm_num)

theorem c22000E_177_3 : rowsJD 177 178 88 272 ≤ 6461051340955222 :=
  rowsJD_le_of_splitJ 177 178 (by norm_num) (by norm_num) rows22000E_961 rows22000E_962 (by norm_num)

theorem c22000E_177_2 : rowsJD 177 178 80 272 ≤ 7065338020149594 :=
  rowsJD_le_of_splitJ 177 178 (by norm_num) (by norm_num) rows22000E_960 c22000E_177_3 (by norm_num)

theorem c22000E_177_1 : rowsJD 177 178 66 272 ≤ 7565750734952600 :=
  rowsJD_le_of_splitJ 177 178 (by norm_num) (by norm_num) rows22000E_959 c22000E_177_2 (by norm_num)

theorem c22000E_177_0 : rowsJD 177 178 0 272 ≤ 7740849770576777 :=
  rowsJD_le_of_splitJ 177 178 (by norm_num) (by norm_num) rows22000E_958 c22000E_177_1 (by norm_num)

theorem c22000E_178_3 : rowsJD 178 179 89 272 ≤ 6228987044314373 :=
  rowsJD_le_of_splitJ 178 179 (by norm_num) (by norm_num) rows22000E_966 rows22000E_967 (by norm_num)

theorem c22000E_178_2 : rowsJD 178 179 81 272 ≤ 6855328076803425 :=
  rowsJD_le_of_splitJ 178 179 (by norm_num) (by norm_num) rows22000E_965 c22000E_178_3 (by norm_num)

theorem c22000E_178_1 : rowsJD 178 179 67 272 ≤ 7354721895538359 :=
  rowsJD_le_of_splitJ 178 179 (by norm_num) (by norm_num) rows22000E_964 c22000E_178_2 (by norm_num)

theorem c22000E_178_0 : rowsJD 178 179 0 272 ≤ 7528940113961458 :=
  rowsJD_le_of_splitJ 178 179 (by norm_num) (by norm_num) rows22000E_963 c22000E_178_1 (by norm_num)

theorem c22000E_179_3 : rowsJD 179 180 88 272 ≤ 6266331657851428 :=
  rowsJD_le_of_splitJ 179 180 (by norm_num) (by norm_num) rows22000E_971 rows22000E_972 (by norm_num)

theorem c22000E_179_2 : rowsJD 179 180 81 272 ≤ 6785641468580865 :=
  rowsJD_le_of_splitJ 179 180 (by norm_num) (by norm_num) rows22000E_970 c22000E_179_3 (by norm_num)

theorem c22000E_179_1 : rowsJD 179 180 68 272 ≤ 7235860863670578 :=
  rowsJD_le_of_splitJ 179 180 (by norm_num) (by norm_num) rows22000E_969 c22000E_179_2 (by norm_num)

theorem c22000E_179_0 : rowsJD 179 180 0 272 ≤ 7399478185660550 :=
  rowsJD_le_of_splitJ 179 180 (by norm_num) (by norm_num) rows22000E_968 c22000E_179_1 (by norm_num)

theorem c22000E_180_3 : rowsJD 180 181 88 272 ≤ 6150826633404778 :=
  rowsJD_le_of_splitJ 180 181 (by norm_num) (by norm_num) rows22000E_976 rows22000E_977 (by norm_num)

theorem c22000E_180_2 : rowsJD 180 181 81 272 ≤ 6642264914438007 :=
  rowsJD_le_of_splitJ 180 181 (by norm_num) (by norm_num) rows22000E_975 c22000E_180_3 (by norm_num)

theorem c22000E_180_1 : rowsJD 180 181 69 272 ≤ 7050721794317096 :=
  rowsJD_le_of_splitJ 180 181 (by norm_num) (by norm_num) rows22000E_974 c22000E_180_2 (by norm_num)

theorem c22000E_180_0 : rowsJD 180 181 0 272 ≤ 7211758770000325 :=
  rowsJD_le_of_splitJ 180 181 (by norm_num) (by norm_num) rows22000E_973 c22000E_180_1 (by norm_num)

theorem c22000E_181_3 : rowsJD 181 182 88 272 ≤ 6156954265379332 :=
  rowsJD_le_of_splitJ 181 182 (by norm_num) (by norm_num) rows22000E_981 rows22000E_982 (by norm_num)

theorem c22000E_181_2 : rowsJD 181 182 81 272 ≤ 6636647191099734 :=
  rowsJD_le_of_splitJ 181 182 (by norm_num) (by norm_num) rows22000E_980 c22000E_181_3 (by norm_num)

theorem c22000E_181_1 : rowsJD 181 182 69 272 ≤ 7028350091789464 :=
  rowsJD_le_of_splitJ 181 182 (by norm_num) (by norm_num) rows22000E_979 c22000E_181_2 (by norm_num)

theorem c22000E_181_0 : rowsJD 181 182 0 272 ≤ 7180068053477602 :=
  rowsJD_le_of_splitJ 181 182 (by norm_num) (by norm_num) rows22000E_978 c22000E_181_1 (by norm_num)

theorem c22000E_182_3 : rowsJD 182 183 108 272 ≤ 5904676733118206 :=
  rowsJD_le_of_splitJ 182 183 (by norm_num) (by norm_num) rows22000E_986 rows22000E_987 (by norm_num)

theorem c22000E_182_2 : rowsJD 182 183 81 272 ≤ 6586929775849268 :=
  rowsJD_le_of_splitJ 182 183 (by norm_num) (by norm_num) rows22000E_985 c22000E_182_3 (by norm_num)

theorem c22000E_182_1 : rowsJD 182 183 70 272 ≤ 6950858971585563 :=
  rowsJD_le_of_splitJ 182 183 (by norm_num) (by norm_num) rows22000E_984 c22000E_182_2 (by norm_num)

theorem c22000E_182_0 : rowsJD 182 183 0 272 ≤ 7119630545575109 :=
  rowsJD_le_of_splitJ 182 183 (by norm_num) (by norm_num) rows22000E_983 c22000E_182_1 (by norm_num)

theorem c22000E_183_2 : rowsJD 183 184 81 272 ≤ 6634645391615840 :=
  rowsJD_le_of_splitJ 183 184 (by norm_num) (by norm_num) rows22000E_990 rows22000E_991 (by norm_num)

theorem c22000E_183_1 : rowsJD 183 184 70 272 ≤ 6995898572950635 :=
  rowsJD_le_of_splitJ 183 184 (by norm_num) (by norm_num) rows22000E_989 c22000E_183_2 (by norm_num)

theorem c22000E_183_0 : rowsJD 183 184 0 272 ≤ 7174427653797501 :=
  rowsJD_le_of_splitJ 183 184 (by norm_num) (by norm_num) rows22000E_988 c22000E_183_1 (by norm_num)

theorem c22000E_184_2 : rowsJD 184 185 81 272 ≤ 6596216800653629 :=
  rowsJD_le_of_splitJ 184 185 (by norm_num) (by norm_num) rows22000E_994 rows22000E_995 (by norm_num)

theorem c22000E_184_1 : rowsJD 184 185 70 272 ≤ 6970421522119955 :=
  rowsJD_le_of_splitJ 184 185 (by norm_num) (by norm_num) rows22000E_993 c22000E_184_2 (by norm_num)

theorem c22000E_184_0 : rowsJD 184 185 0 272 ≤ 7169011818707715 :=
  rowsJD_le_of_splitJ 184 185 (by norm_num) (by norm_num) rows22000E_992 c22000E_184_1 (by norm_num)

theorem c22000E_185_2 : rowsJD 185 186 81 272 ≤ 6633345379563980 :=
  rowsJD_le_of_splitJ 185 186 (by norm_num) (by norm_num) rows22000E_998 rows22000E_999 (by norm_num)

theorem c22000E_185_1 : rowsJD 185 186 71 272 ≤ 6989976433591354 :=
  rowsJD_le_of_splitJ 185 186 (by norm_num) (by norm_num) rows22000E_997 c22000E_185_2 (by norm_num)

theorem c22000E_185_0 : rowsJD 185 186 0 272 ≤ 7242343039996662 :=
  rowsJD_le_of_splitJ 185 186 (by norm_num) (by norm_num) rows22000E_996 c22000E_185_1 (by norm_num)

theorem c22000E_186_2 : rowsJD 186 187 81 272 ≤ 6589359041770964 :=
  rowsJD_le_of_splitJ 186 187 (by norm_num) (by norm_num) rows22000E_1002 rows22000E_1003 (by norm_num)

theorem c22000E_186_1 : rowsJD 186 187 71 272 ≤ 6961868440864037 :=
  rowsJD_le_of_splitJ 186 187 (by norm_num) (by norm_num) rows22000E_1001 c22000E_186_2 (by norm_num)

theorem c22000E_186_0 : rowsJD 186 187 0 272 ≤ 7254203755359775 :=
  rowsJD_le_of_splitJ 186 187 (by norm_num) (by norm_num) rows22000E_1000 c22000E_186_1 (by norm_num)

theorem c22000E_187_1 : rowsJD 187 188 71 272 ≤ 7044716251312302 :=
  rowsJD_le_of_splitJ 187 188 (by norm_num) (by norm_num) rows22000E_1005 rows22000E_1006 (by norm_num)

theorem c22000E_187_0 : rowsJD 187 188 0 272 ≤ 7376511697431750 :=
  rowsJD_le_of_splitJ 187 188 (by norm_num) (by norm_num) rows22000E_1004 c22000E_187_1 (by norm_num)

theorem c22000E_188_1 : rowsJD 188 189 71 272 ≤ 7051567542805815 :=
  rowsJD_le_of_splitJ 188 189 (by norm_num) (by norm_num) rows22000E_1008 rows22000E_1009 (by norm_num)

theorem c22000E_188_0 : rowsJD 188 189 0 272 ≤ 7418242847371443 :=
  rowsJD_le_of_splitJ 188 189 (by norm_num) (by norm_num) rows22000E_1007 c22000E_188_1 (by norm_num)

theorem c22000E_189_1 : rowsJD 189 190 70 272 ≤ 7210115479022396 :=
  rowsJD_le_of_splitJ 189 190 (by norm_num) (by norm_num) rows22000E_1011 rows22000E_1012 (by norm_num)

theorem c22000E_189_0 : rowsJD 189 190 0 272 ≤ 7572400874365130 :=
  rowsJD_le_of_splitJ 189 190 (by norm_num) (by norm_num) rows22000E_1010 c22000E_189_1 (by norm_num)

theorem c22000E_190_1 : rowsJD 190 191 70 272 ≤ 7219993580204318 :=
  rowsJD_le_of_splitJ 190 191 (by norm_num) (by norm_num) rows22000E_1014 rows22000E_1015 (by norm_num)

theorem c22000E_190_0 : rowsJD 190 191 0 272 ≤ 7616809209269133 :=
  rowsJD_le_of_splitJ 190 191 (by norm_num) (by norm_num) rows22000E_1013 c22000E_190_1 (by norm_num)

theorem c22000E_191_1 : rowsJD 191 192 69 272 ≤ 7360044868896780 :=
  rowsJD_le_of_splitJ 191 192 (by norm_num) (by norm_num) rows22000E_1017 rows22000E_1018 (by norm_num)

theorem c22000E_191_0 : rowsJD 191 192 0 272 ≤ 7746974225093839 :=
  rowsJD_le_of_splitJ 191 192 (by norm_num) (by norm_num) rows22000E_1016 c22000E_191_1 (by norm_num)

theorem c22000E_192_1 : rowsJD 192 193 69 272 ≤ 7357144892177063 :=
  rowsJD_le_of_splitJ 192 193 (by norm_num) (by norm_num) rows22000E_1020 rows22000E_1021 (by norm_num)

theorem c22000E_192_0 : rowsJD 192 193 0 272 ≤ 7776981254571814 :=
  rowsJD_le_of_splitJ 192 193 (by norm_num) (by norm_num) rows22000E_1019 c22000E_192_1 (by norm_num)

theorem c22000E_193_1 : rowsJD 193 194 68 272 ≤ 7477364318034923 :=
  rowsJD_le_of_splitJ 193 194 (by norm_num) (by norm_num) rows22000E_1023 rows22000E_1024 (by norm_num)

theorem c22000E_193_0 : rowsJD 193 194 0 272 ≤ 7889838605831781 :=
  rowsJD_le_of_splitJ 193 194 (by norm_num) (by norm_num) rows22000E_1022 c22000E_193_1 (by norm_num)

theorem c22000E_194_1 : rowsJD 194 195 67 272 ≤ 7510332724928057 :=
  rowsJD_le_of_splitJ 194 195 (by norm_num) (by norm_num) rows22000E_1026 rows22000E_1027 (by norm_num)

theorem c22000E_194_0 : rowsJD 194 195 0 272 ≤ 7914818918368257 :=
  rowsJD_le_of_splitJ 194 195 (by norm_num) (by norm_num) rows22000E_1025 c22000E_194_1 (by norm_num)

theorem c22000E_195_1 : rowsJD 195 196 66 272 ≤ 7635859473332008 :=
  rowsJD_le_of_splitJ 195 196 (by norm_num) (by norm_num) rows22000E_1029 rows22000E_1030 (by norm_num)

theorem c22000E_195_0 : rowsJD 195 196 0 272 ≤ 8030912236313699 :=
  rowsJD_le_of_splitJ 195 196 (by norm_num) (by norm_num) rows22000E_1028 c22000E_195_1 (by norm_num)

theorem c22000E_196_1 : rowsJD 196 197 65 272 ≤ 7671041553572649 :=
  rowsJD_le_of_splitJ 196 197 (by norm_num) (by norm_num) rows22000E_1032 rows22000E_1033 (by norm_num)

theorem c22000E_196_0 : rowsJD 196 197 0 272 ≤ 8057300494045860 :=
  rowsJD_le_of_splitJ 196 197 (by norm_num) (by norm_num) rows22000E_1031 c22000E_196_1 (by norm_num)

theorem c22000E_197_1 : rowsJD 197 198 65 272 ≤ 7777835887430828 :=
  rowsJD_le_of_splitJ 197 198 (by norm_num) (by norm_num) rows22000E_1035 rows22000E_1036 (by norm_num)

theorem c22000E_197_0 : rowsJD 197 198 0 272 ≤ 8236715651519987 :=
  rowsJD_le_of_splitJ 197 198 (by norm_num) (by norm_num) rows22000E_1034 c22000E_197_1 (by norm_num)

theorem c22000E_198_1 : rowsJD 198 199 64 272 ≤ 7827357771768941 :=
  rowsJD_le_of_splitJ 198 199 (by norm_num) (by norm_num) rows22000E_1038 rows22000E_1039 (by norm_num)

theorem c22000E_198_0 : rowsJD 198 199 0 272 ≤ 8287694001896685 :=
  rowsJD_le_of_splitJ 198 199 (by norm_num) (by norm_num) rows22000E_1037 c22000E_198_1 (by norm_num)

theorem c22000E_199_1 : rowsJD 199 200 63 272 ≤ 7967132570866296 :=
  rowsJD_le_of_splitJ 199 200 (by norm_num) (by norm_num) rows22000E_1041 rows22000E_1042 (by norm_num)

theorem c22000E_199_0 : rowsJD 199 200 0 272 ≤ 8440208323917314 :=
  rowsJD_le_of_splitJ 199 200 (by norm_num) (by norm_num) rows22000E_1040 c22000E_199_1 (by norm_num)

theorem c22000E_200_1 : rowsJD 200 201 62 272 ≤ 8013489145206286 :=
  rowsJD_le_of_splitJ 200 201 (by norm_num) (by norm_num) rows22000E_1044 rows22000E_1045 (by norm_num)

theorem c22000E_200_0 : rowsJD 200 201 0 272 ≤ 8500093739131629 :=
  rowsJD_le_of_splitJ 200 201 (by norm_num) (by norm_num) rows22000E_1043 c22000E_200_1 (by norm_num)

theorem c22000E_201_1 : rowsJD 201 202 62 272 ≤ 8099640678294434 :=
  rowsJD_le_of_splitJ 201 202 (by norm_num) (by norm_num) rows22000E_1047 rows22000E_1048 (by norm_num)

theorem c22000E_201_0 : rowsJD 201 202 0 272 ≤ 8651909577987097 :=
  rowsJD_le_of_splitJ 201 202 (by norm_num) (by norm_num) rows22000E_1046 c22000E_201_1 (by norm_num)

theorem c22000E_202_1 : rowsJD 202 203 61 272 ≤ 8121548341455876 :=
  rowsJD_le_of_splitJ 202 203 (by norm_num) (by norm_num) rows22000E_1050 rows22000E_1051 (by norm_num)

theorem c22000E_202_0 : rowsJD 202 203 0 272 ≤ 8645617768488765 :=
  rowsJD_le_of_splitJ 202 203 (by norm_num) (by norm_num) rows22000E_1049 c22000E_202_1 (by norm_num)

theorem c22000E_203_1 : rowsJD 203 204 61 272 ≤ 8193815604230095 :=
  rowsJD_le_of_splitJ 203 204 (by norm_num) (by norm_num) rows22000E_1053 rows22000E_1054 (by norm_num)

theorem c22000E_203_0 : rowsJD 203 204 0 272 ≤ 8741803863533836 :=
  rowsJD_le_of_splitJ 203 204 (by norm_num) (by norm_num) rows22000E_1052 c22000E_203_1 (by norm_num)

theorem c22000E_204_1 : rowsJD 204 205 60 272 ≤ 8228180885213662 :=
  rowsJD_le_of_splitJ 204 205 (by norm_num) (by norm_num) rows22000E_1056 rows22000E_1057 (by norm_num)

theorem c22000E_204_0 : rowsJD 204 205 0 272 ≤ 8738542369363864 :=
  rowsJD_le_of_splitJ 204 205 (by norm_num) (by norm_num) rows22000E_1055 c22000E_204_1 (by norm_num)

theorem c22000E_205_1 : rowsJD 205 206 60 272 ≤ 8317152460023071 :=
  rowsJD_le_of_splitJ 205 206 (by norm_num) (by norm_num) rows22000E_1059 rows22000E_1060 (by norm_num)

theorem c22000E_205_0 : rowsJD 205 206 0 272 ≤ 8883161264148081 :=
  rowsJD_le_of_splitJ 205 206 (by norm_num) (by norm_num) rows22000E_1058 c22000E_205_1 (by norm_num)

theorem c22000E_206_1 : rowsJD 206 207 59 272 ≤ 8334349578876889 :=
  rowsJD_le_of_splitJ 206 207 (by norm_num) (by norm_num) rows22000E_1062 rows22000E_1063 (by norm_num)

theorem c22000E_206_0 : rowsJD 206 207 0 272 ≤ 8871675716455308 :=
  rowsJD_le_of_splitJ 206 207 (by norm_num) (by norm_num) rows22000E_1061 c22000E_206_1 (by norm_num)

theorem c22000E_207_0 : rowsJD 207 208 0 272 ≤ 9035849239561374 :=
  rowsJD_le_of_splitJ 207 208 (by norm_num) (by norm_num) rows22000E_1064 rows22000E_1065 (by norm_num)

theorem c22000E_208_0 : rowsJD 208 209 0 272 ≤ 9119982276554617 :=
  rowsJD_le_of_splitJ 208 209 (by norm_num) (by norm_num) rows22000E_1066 rows22000E_1067 (by norm_num)

theorem c22000E_209_0 : rowsJD 209 210 0 272 ≤ 9235738109870440 :=
  rowsJD_le_of_splitJ 209 210 (by norm_num) (by norm_num) rows22000E_1068 rows22000E_1069 (by norm_num)

theorem c22000E_210_0 : rowsJD 210 211 0 272 ≤ 9224286551077607 :=
  rowsJD_le_of_splitJ 210 211 (by norm_num) (by norm_num) rows22000E_1070 rows22000E_1071 (by norm_num)

theorem c22000E_211_0 : rowsJD 211 212 0 272 ≤ 9340673972294126 :=
  rowsJD_le_of_splitJ 211 212 (by norm_num) (by norm_num) rows22000E_1072 rows22000E_1073 (by norm_num)

theorem c22000E_212_0 : rowsJD 212 213 0 272 ≤ 9363441754955040 :=
  rowsJD_le_of_splitJ 212 213 (by norm_num) (by norm_num) rows22000E_1074 rows22000E_1075 (by norm_num)

theorem c22000E_213_0 : rowsJD 213 214 0 272 ≤ 9616013594488062 :=
  rowsJD_le_of_splitJ 213 214 (by norm_num) (by norm_num) rows22000E_1076 rows22000E_1077 (by norm_num)

theorem c22000E_214_0 : rowsJD 214 215 0 272 ≤ 9693278941881259 :=
  rowsJD_le_of_splitJ 214 215 (by norm_num) (by norm_num) rows22000E_1078 rows22000E_1079 (by norm_num)

theorem c22000E_215_0 : rowsJD 215 216 0 272 ≤ 9895247732671748 :=
  rowsJD_le_of_splitJ 215 216 (by norm_num) (by norm_num) rows22000E_1080 rows22000E_1081 (by norm_num)

theorem c22000E_216_0 : rowsJD 216 217 0 272 ≤ 10002467858515235 :=
  rowsJD_le_of_splitJ 216 217 (by norm_num) (by norm_num) rows22000E_1082 rows22000E_1083 (by norm_num)

theorem c22000E_217_0 : rowsJD 217 218 0 272 ≤ 10190345680037324 :=
  rowsJD_le_of_splitJ 217 218 (by norm_num) (by norm_num) rows22000E_1084 rows22000E_1085 (by norm_num)

theorem c22000E_218_0 : rowsJD 218 219 0 272 ≤ 10200019997642177 :=
  rowsJD_le_of_splitJ 218 219 (by norm_num) (by norm_num) rows22000E_1086 rows22000E_1087 (by norm_num)

theorem c22000E_219_0 : rowsJD 219 220 0 272 ≤ 10311576916070422 :=
  rowsJD_le_of_splitJ 219 220 (by norm_num) (by norm_num) rows22000E_1088 rows22000E_1089 (by norm_num)

theorem c22000E_220_0 : rowsJD 220 221 0 272 ≤ 10333931527656003 :=
  rowsJD_le_of_splitJ 220 221 (by norm_num) (by norm_num) rows22000E_1090 rows22000E_1091 (by norm_num)

theorem c22000E_221_0 : rowsJD 221 222 0 272 ≤ 10537480176985678 :=
  rowsJD_le_of_splitJ 221 222 (by norm_num) (by norm_num) rows22000E_1092 rows22000E_1093 (by norm_num)

theorem c22000E_222_0 : rowsJD 222 223 0 272 ≤ 10623792570859743 :=
  rowsJD_le_of_splitJ 222 223 (by norm_num) (by norm_num) rows22000E_1094 rows22000E_1095 (by norm_num)

theorem c22000E_223_0 : rowsJD 223 224 0 272 ≤ 10804441317867543 :=
  rowsJD_le_of_splitJ 223 224 (by norm_num) (by norm_num) rows22000E_1096 rows22000E_1097 (by norm_num)

theorem c22000E_224_0 : rowsJD 224 225 0 272 ≤ 10889117567600252 :=
  rowsJD_le_of_splitJ 224 225 (by norm_num) (by norm_num) rows22000E_1098 rows22000E_1099 (by norm_num)

theorem c22000E_225_0 : rowsJD 225 226 0 272 ≤ 11053074820818074 :=
  rowsJD_le_of_splitJ 225 226 (by norm_num) (by norm_num) rows22000E_1100 rows22000E_1101 (by norm_num)

theorem c22000E_226_0 : rowsJD 226 227 0 272 ≤ 11109367044916465 :=
  rowsJD_le_of_splitJ 226 227 (by norm_num) (by norm_num) rows22000E_1102 rows22000E_1103 (by norm_num)

theorem c22000E_227_0 : rowsJD 227 228 0 272 ≤ 11266792748421193 :=
  rowsJD_le_of_splitJ 227 228 (by norm_num) (by norm_num) rows22000E_1104 rows22000E_1105 (by norm_num)

theorem c22000E_228_0 : rowsJD 228 229 0 272 ≤ 11192320255336575 :=
  rowsJD_le_of_splitJ 228 229 (by norm_num) (by norm_num) rows22000E_1106 rows22000E_1107 (by norm_num)

theorem c22000E_229_0 : rowsJD 229 230 0 272 ≤ 11241309524136955 :=
  rowsJD_le_of_splitJ 229 230 (by norm_num) (by norm_num) rows22000E_1108 rows22000E_1109 (by norm_num)

theorem c22000E_230_0 : rowsJD 230 231 0 272 ≤ 11167750802108576 :=
  rowsJD_le_of_splitJ 230 231 (by norm_num) (by norm_num) rows22000E_1110 rows22000E_1111 (by norm_num)

theorem c22000E_231_0 : rowsJD 231 232 0 272 ≤ 11190463118068389 :=
  rowsJD_le_of_splitJ 231 232 (by norm_num) (by norm_num) rows22000E_1112 rows22000E_1113 (by norm_num)

theorem c22000E_232_0 : rowsJD 232 233 0 272 ≤ 11125436101442118 :=
  rowsJD_le_of_splitJ 232 233 (by norm_num) (by norm_num) rows22000E_1114 rows22000E_1115 (by norm_num)

theorem c22000E_233_0 : rowsJD 233 234 0 272 ≤ 11134128422519225 :=
  rowsJD_le_of_splitJ 233 234 (by norm_num) (by norm_num) rows22000E_1116 rows22000E_1117 (by norm_num)

theorem t22000E_227 : rowsJD 270 272 0 272 ≤ 25165615423908768 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_1134 rows22000E_1135 (by norm_num)

theorem t22000E_226 : rowsJD 269 272 0 272 ≤ 38056558603279229 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_1133 t22000E_227 (by norm_num)

theorem t22000E_225 : rowsJD 268 272 0 272 ≤ 51169833303831122 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_1132 t22000E_226 (by norm_num)

theorem t22000E_224 : rowsJD 267 272 0 272 ≤ 64557716873513617 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_1131 t22000E_225 (by norm_num)

theorem t22000E_223 : rowsJD 266 272 0 272 ≤ 78059571789058277 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_1130 t22000E_224 (by norm_num)

theorem t22000E_222 : rowsJD 265 272 0 272 ≤ 91728283646194013 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_1129 t22000E_223 (by norm_num)

theorem t22000E_221 : rowsJD 264 272 0 272 ≤ 105411758051505133 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_1128 t22000E_222 (by norm_num)

theorem t22000E_220 : rowsJD 263 272 0 272 ≤ 119022304089589929 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_1127 t22000E_221 (by norm_num)

theorem t22000E_219 : rowsJD 262 272 0 272 ≤ 132505055205925732 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_1126 t22000E_220 (by norm_num)

theorem t22000E_218 : rowsJD 261 272 0 272 ≤ 146003603606312089 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_1125 t22000E_219 (by norm_num)

theorem t22000E_217 : rowsJD 260 272 0 272 ≤ 159423969144318034 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_1124 t22000E_218 (by norm_num)

theorem t22000E_216 : rowsJD 259 272 0 272 ≤ 172929355486720041 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_1123 t22000E_217 (by norm_num)

theorem t22000E_215 : rowsJD 258 272 0 272 ≤ 186403330353377202 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_1122 t22000E_216 (by norm_num)

theorem t22000E_214 : rowsJD 257 272 0 272 ≤ 199941064867798258 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_1121 t22000E_215 (by norm_num)

theorem t22000E_213 : rowsJD 256 272 0 272 ≤ 213421354854601821 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_1120 t22000E_214 (by norm_num)

theorem t22000E_212 : rowsJD 255 272 0 272 ≤ 226944228698357252 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_1119 t22000E_213 (by norm_num)

theorem t22000E_211 : rowsJD 234 272 0 272 ≤ 240411469486915481 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_1118 t22000E_212 (by norm_num)

theorem t22000E_210 : rowsJD 233 272 0 272 ≤ 251545597909434706 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_233_0 t22000E_211 (by norm_num)

theorem t22000E_209 : rowsJD 232 272 0 272 ≤ 262671034010876824 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_232_0 t22000E_210 (by norm_num)

theorem t22000E_208 : rowsJD 231 272 0 272 ≤ 273861497128945213 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_231_0 t22000E_209 (by norm_num)

theorem t22000E_207 : rowsJD 230 272 0 272 ≤ 285029247931053789 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_230_0 t22000E_208 (by norm_num)

theorem t22000E_206 : rowsJD 229 272 0 272 ≤ 296270557455190744 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_229_0 t22000E_207 (by norm_num)

theorem t22000E_205 : rowsJD 228 272 0 272 ≤ 307462877710527319 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_228_0 t22000E_206 (by norm_num)

theorem t22000E_204 : rowsJD 227 272 0 272 ≤ 318729670458948512 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_227_0 t22000E_205 (by norm_num)

theorem t22000E_203 : rowsJD 226 272 0 272 ≤ 329839037503864977 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_226_0 t22000E_204 (by norm_num)

theorem t22000E_202 : rowsJD 225 272 0 272 ≤ 340892112324683051 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_225_0 t22000E_203 (by norm_num)

theorem t22000E_201 : rowsJD 224 272 0 272 ≤ 351781229892283303 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_224_0 t22000E_202 (by norm_num)

theorem t22000E_200 : rowsJD 223 272 0 272 ≤ 362585671210150846 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_223_0 t22000E_201 (by norm_num)

theorem t22000E_199 : rowsJD 222 272 0 272 ≤ 373209463781010589 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_222_0 t22000E_200 (by norm_num)

theorem t22000E_198 : rowsJD 221 272 0 272 ≤ 383746943957996267 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_221_0 t22000E_199 (by norm_num)

theorem t22000E_197 : rowsJD 220 272 0 272 ≤ 394080875485652270 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_220_0 t22000E_198 (by norm_num)

theorem t22000E_196 : rowsJD 219 272 0 272 ≤ 404392452401722692 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_219_0 t22000E_197 (by norm_num)

theorem t22000E_195 : rowsJD 218 272 0 272 ≤ 414592472399364869 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_218_0 t22000E_196 (by norm_num)

theorem t22000E_194 : rowsJD 217 272 0 272 ≤ 424782818079402193 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_217_0 t22000E_195 (by norm_num)

theorem t22000E_193 : rowsJD 216 272 0 272 ≤ 434785285937917428 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_216_0 t22000E_194 (by norm_num)

theorem t22000E_192 : rowsJD 215 272 0 272 ≤ 444680533670589176 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_215_0 t22000E_193 (by norm_num)

theorem t22000E_191 : rowsJD 214 272 0 272 ≤ 454373812612470435 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_214_0 t22000E_192 (by norm_num)

theorem t22000E_190 : rowsJD 213 272 0 272 ≤ 463989826206958497 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_213_0 t22000E_191 (by norm_num)

theorem t22000E_189 : rowsJD 212 272 0 272 ≤ 473353267961913537 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_212_0 t22000E_190 (by norm_num)

theorem t22000E_188 : rowsJD 211 272 0 272 ≤ 482693941934207663 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_211_0 t22000E_189 (by norm_num)

theorem t22000E_187 : rowsJD 210 272 0 272 ≤ 491918228485285270 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_210_0 t22000E_188 (by norm_num)

theorem t22000E_186 : rowsJD 209 272 0 272 ≤ 501153966595155710 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_209_0 t22000E_187 (by norm_num)

theorem t22000E_185 : rowsJD 208 272 0 272 ≤ 510273948871710327 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_208_0 t22000E_186 (by norm_num)

theorem t22000E_184 : rowsJD 207 272 0 272 ≤ 519309798111271701 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_207_0 t22000E_185 (by norm_num)

theorem t22000E_183 : rowsJD 206 272 0 272 ≤ 528181473827727009 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_206_0 t22000E_184 (by norm_num)

theorem t22000E_182 : rowsJD 205 272 0 272 ≤ 537064635091875090 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_205_0 t22000E_183 (by norm_num)

theorem t22000E_181 : rowsJD 204 272 0 272 ≤ 545803177461238954 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_204_0 t22000E_182 (by norm_num)

theorem t22000E_180 : rowsJD 203 272 0 272 ≤ 554544981324772790 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_203_0 t22000E_181 (by norm_num)

theorem t22000E_179 : rowsJD 202 272 0 272 ≤ 563190599093261555 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_202_0 t22000E_180 (by norm_num)

theorem t22000E_178 : rowsJD 201 272 0 272 ≤ 571842508671248652 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_201_0 t22000E_179 (by norm_num)

theorem t22000E_177 : rowsJD 200 272 0 272 ≤ 580342602410380281 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_200_0 t22000E_178 (by norm_num)

theorem t22000E_176 : rowsJD 199 272 0 272 ≤ 588782810734297595 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_199_0 t22000E_177 (by norm_num)

theorem t22000E_175 : rowsJD 198 272 0 272 ≤ 597070504736194280 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_198_0 t22000E_176 (by norm_num)

theorem t22000E_174 : rowsJD 197 272 0 272 ≤ 605307220387714267 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_197_0 t22000E_175 (by norm_num)

theorem t22000E_173 : rowsJD 196 272 0 272 ≤ 613364520881760127 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_196_0 t22000E_174 (by norm_num)

theorem t22000E_172 : rowsJD 195 272 0 272 ≤ 621395433118073826 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_195_0 t22000E_173 (by norm_num)

theorem t22000E_171 : rowsJD 194 272 0 272 ≤ 629310252036442083 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_194_0 t22000E_172 (by norm_num)

theorem t22000E_170 : rowsJD 193 272 0 272 ≤ 637200090642273864 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_193_0 t22000E_171 (by norm_num)

theorem t22000E_169 : rowsJD 192 272 0 272 ≤ 644977071896845678 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_192_0 t22000E_170 (by norm_num)

theorem t22000E_168 : rowsJD 191 272 0 272 ≤ 652724046121939517 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_191_0 t22000E_169 (by norm_num)

theorem t22000E_167 : rowsJD 190 272 0 272 ≤ 660340855331208650 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_190_0 t22000E_168 (by norm_num)

theorem t22000E_166 : rowsJD 189 272 0 272 ≤ 667913256205573780 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_189_0 t22000E_167 (by norm_num)

theorem t22000E_165 : rowsJD 188 272 0 272 ≤ 675331499052945223 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_188_0 t22000E_166 (by norm_num)

theorem t22000E_164 : rowsJD 187 272 0 272 ≤ 682708010750376973 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_187_0 t22000E_165 (by norm_num)

theorem t22000E_163 : rowsJD 186 272 0 272 ≤ 689962214505736748 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_186_0 t22000E_164 (by norm_num)

theorem t22000E_162 : rowsJD 185 272 0 272 ≤ 697204557545733410 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_185_0 t22000E_163 (by norm_num)

theorem t22000E_161 : rowsJD 184 272 0 272 ≤ 704373569364441125 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_184_0 t22000E_162 (by norm_num)

theorem t22000E_160 : rowsJD 183 272 0 272 ≤ 711547997018238626 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_183_0 t22000E_161 (by norm_num)

theorem t22000E_159 : rowsJD 182 272 0 272 ≤ 718667627563813735 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_182_0 t22000E_160 (by norm_num)

theorem t22000E_158 : rowsJD 181 272 0 272 ≤ 725847695617291337 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_181_0 t22000E_159 (by norm_num)

theorem t22000E_157 : rowsJD 180 272 0 272 ≤ 733059454387291662 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_180_0 t22000E_158 (by norm_num)

theorem t22000E_156 : rowsJD 179 272 0 272 ≤ 740458932572952212 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_179_0 t22000E_157 (by norm_num)

theorem t22000E_155 : rowsJD 178 272 0 272 ≤ 747987872686913670 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_178_0 t22000E_156 (by norm_num)

theorem t22000E_154 : rowsJD 177 272 0 272 ≤ 755728722457490447 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_177_0 t22000E_155 (by norm_num)

theorem t22000E_153 : rowsJD 176 272 0 272 ≤ 763585013811293874 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_176_0 t22000E_154 (by norm_num)

theorem t22000E_152 : rowsJD 175 272 0 272 ≤ 771590817298319950 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_175_0 t22000E_153 (by norm_num)

theorem t22000E_151 : rowsJD 174 272 0 272 ≤ 779641354360286979 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_174_0 t22000E_152 (by norm_num)

theorem t22000E_150 : rowsJD 173 272 0 272 ≤ 787605882904243628 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_173_0 t22000E_151 (by norm_num)

theorem t22000E_149 : rowsJD 172 272 0 272 ≤ 795373022656499528 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_172_0 t22000E_150 (by norm_num)

theorem t22000E_148 : rowsJD 171 272 0 272 ≤ 802908716679600723 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_171_0 t22000E_149 (by norm_num)

theorem t22000E_147 : rowsJD 170 272 0 272 ≤ 810170636159614645 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_170_0 t22000E_148 (by norm_num)

theorem t22000E_146 : rowsJD 169 272 0 272 ≤ 817136920407436828 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_169_0 t22000E_147 (by norm_num)

theorem t22000E_145 : rowsJD 168 272 0 272 ≤ 823849145730273201 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_168_0 t22000E_146 (by norm_num)

theorem t22000E_144 : rowsJD 167 272 0 272 ≤ 830319824173924310 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_167_0 t22000E_145 (by norm_num)

theorem t22000E_143 : rowsJD 166 272 0 272 ≤ 836596324786492470 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_166_0 t22000E_144 (by norm_num)

theorem t22000E_142 : rowsJD 165 272 0 272 ≤ 842708926671702959 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_165_0 t22000E_143 (by norm_num)

theorem t22000E_141 : rowsJD 164 272 0 272 ≤ 848693644834615256 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_164_0 t22000E_142 (by norm_num)

theorem t22000E_140 : rowsJD 163 272 0 272 ≤ 854575251787528400 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_163_0 t22000E_141 (by norm_num)

theorem t22000E_139 : rowsJD 162 272 0 272 ≤ 860353563313694742 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_162_0 t22000E_140 (by norm_num)

theorem t22000E_138 : rowsJD 161 272 0 272 ≤ 866028686836640530 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_161_0 t22000E_139 (by norm_num)

theorem t22000E_137 : rowsJD 160 272 0 272 ≤ 871595103728843520 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_160_0 t22000E_138 (by norm_num)

theorem t22000E_136 : rowsJD 159 272 0 272 ≤ 876973495641901518 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_159_0 t22000E_137 (by norm_num)

theorem t22000E_135 : rowsJD 158 272 0 272 ≤ 882137130263372775 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_158_0 t22000E_136 (by norm_num)

theorem t22000E_134 : rowsJD 157 272 0 272 ≤ 887072222855623259 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_157_0 t22000E_135 (by norm_num)

theorem t22000E_133 : rowsJD 156 272 0 272 ≤ 891781880906554992 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_156_0 t22000E_134 (by norm_num)

theorem t22000E_132 : rowsJD 155 272 0 272 ≤ 896309026048011542 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_155_0 t22000E_133 (by norm_num)

theorem t22000E_131 : rowsJD 154 272 0 272 ≤ 900673725423593405 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_154_0 t22000E_132 (by norm_num)

theorem t22000E_130 : rowsJD 153 272 0 272 ≤ 904911762509595642 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_153_0 t22000E_131 (by norm_num)

theorem t22000E_129 : rowsJD 152 272 0 272 ≤ 909049020710304169 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_152_0 t22000E_130 (by norm_num)

theorem t22000E_128 : rowsJD 151 272 0 272 ≤ 913042405043453455 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_151_0 t22000E_129 (by norm_num)

theorem t22000E_127 : rowsJD 150 272 0 272 ≤ 916905433212873358 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_150_0 t22000E_128 (by norm_num)

theorem t22000E_126 : rowsJD 149 272 0 272 ≤ 920638085403269913 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_149_0 t22000E_127 (by norm_num)

theorem t22000E_125 : rowsJD 148 272 0 272 ≤ 924228650819306615 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_148_0 t22000E_126 (by norm_num)

theorem t22000E_124 : rowsJD 147 272 0 272 ≤ 927708343392524889 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_147_0 t22000E_125 (by norm_num)

theorem t22000E_123 : rowsJD 146 272 0 272 ≤ 931033272844920083 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_146_0 t22000E_124 (by norm_num)

theorem t22000E_122 : rowsJD 145 272 0 272 ≤ 934162370397150046 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_145_0 t22000E_123 (by norm_num)

theorem t22000E_121 : rowsJD 144 272 0 272 ≤ 937064941801763748 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_144_0 t22000E_122 (by norm_num)

theorem t22000E_120 : rowsJD 143 272 0 272 ≤ 939806736990124780 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_143_0 t22000E_121 (by norm_num)

theorem t22000E_119 : rowsJD 142 272 0 272 ≤ 942481010791390313 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_142_0 t22000E_120 (by norm_num)

theorem t22000E_118 : rowsJD 141 272 0 272 ≤ 945089065274990812 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_141_0 t22000E_119 (by norm_num)

theorem t22000E_117 : rowsJD 140 272 0 272 ≤ 947670900377309426 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_140_0 t22000E_118 (by norm_num)

theorem t22000E_116 : rowsJD 139 272 0 272 ≤ 950319073270906905 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_139_0 t22000E_117 (by norm_num)

theorem t22000E_115 : rowsJD 138 272 0 272 ≤ 953080631296620932 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_138_0 t22000E_116 (by norm_num)

theorem t22000E_114 : rowsJD 137 272 0 272 ≤ 956006970582103947 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_137_0 t22000E_115 (by norm_num)

theorem t22000E_113 : rowsJD 136 272 0 272 ≤ 959141131145447274 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_136_0 t22000E_114 (by norm_num)

theorem t22000E_112 : rowsJD 135 272 0 272 ≤ 962466419184835592 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_135_0 t22000E_113 (by norm_num)

theorem t22000E_111 : rowsJD 134 272 0 272 ≤ 965854513688945178 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_134_0 t22000E_112 (by norm_num)

theorem t22000E_110 : rowsJD 133 272 0 272 ≤ 969174970920243257 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_133_0 t22000E_111 (by norm_num)

theorem t22000E_109 : rowsJD 132 272 0 272 ≤ 972411361054938815 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_132_0 t22000E_110 (by norm_num)

theorem t22000E_108 : rowsJD 131 272 0 272 ≤ 975554108049379718 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_131_0 t22000E_109 (by norm_num)

theorem t22000E_107 : rowsJD 130 272 0 272 ≤ 978591196685476274 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_130_0 t22000E_108 (by norm_num)

theorem t22000E_106 : rowsJD 129 272 0 272 ≤ 981509473111070278 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_129_0 t22000E_107 (by norm_num)

theorem t22000E_105 : rowsJD 128 272 0 272 ≤ 984303697013272129 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_128_0 t22000E_106 (by norm_num)

theorem t22000E_104 : rowsJD 127 272 0 272 ≤ 986962920177990774 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_127_0 t22000E_105 (by norm_num)

theorem t22000E_103 : rowsJD 126 272 0 272 ≤ 989496053939232969 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_126_0 t22000E_104 (by norm_num)

theorem t22000E_102 : rowsJD 125 272 0 272 ≤ 991928136082617433 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_125_0 t22000E_103 (by norm_num)

theorem t22000E_101 : rowsJD 124 272 0 272 ≤ 994276266165357796 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_124_0 t22000E_102 (by norm_num)

theorem t22000E_100 : rowsJD 123 272 0 272 ≤ 996531691899297480 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_123_0 t22000E_101 (by norm_num)

theorem t22000E_99 : rowsJD 122 272 0 272 ≤ 998686699783926333 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_122_0 t22000E_100 (by norm_num)

theorem t22000E_98 : rowsJD 121 272 0 272 ≤ 1000725376684493532 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_121_0 t22000E_99 (by norm_num)

theorem t22000E_97 : rowsJD 120 272 0 272 ≤ 1002632619136032156 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_120_0 t22000E_98 (by norm_num)

theorem t22000E_96 : rowsJD 119 272 0 272 ≤ 1004381355300324788 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_119_0 t22000E_97 (by norm_num)

theorem t22000E_95 : rowsJD 118 272 0 272 ≤ 1005943456758622890 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_118_0 t22000E_96 (by norm_num)

theorem t22000E_94 : rowsJD 117 272 0 272 ≤ 1007253700729846348 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_117_0 t22000E_95 (by norm_num)

theorem t22000E_93 : rowsJD 116 272 0 272 ≤ 1008272482943193547 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_116_0 t22000E_94 (by norm_num)

theorem t22000E_92 : rowsJD 115 272 0 272 ≤ 1009152873180840837 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_115_0 t22000E_93 (by norm_num)

theorem t22000E_91 : rowsJD 114 272 0 272 ≤ 1010032855877811895 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_114_0 t22000E_92 (by norm_num)

theorem t22000E_90 : rowsJD 113 272 0 272 ≤ 1010913034431437602 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_113_0 t22000E_91 (by norm_num)

theorem t22000E_89 : rowsJD 112 272 0 272 ≤ 1011810739968337672 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_112_0 t22000E_90 (by norm_num)

theorem t22000E_88 : rowsJD 111 272 0 272 ≤ 1012720206957623939 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_111_0 t22000E_89 (by norm_num)

theorem t22000E_87 : rowsJD 110 272 0 272 ≤ 1013656800104940343 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_110_0 t22000E_88 (by norm_num)

theorem t22000E_86 : rowsJD 109 272 0 272 ≤ 1014642820146948727 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_109_0 t22000E_87 (by norm_num)

theorem t22000E_85 : rowsJD 108 272 0 272 ≤ 1015700142592071881 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_108_0 t22000E_86 (by norm_num)

theorem t22000E_84 : rowsJD 107 272 0 272 ≤ 1016857074644156507 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_107_0 t22000E_85 (by norm_num)

theorem t22000E_83 : rowsJD 106 272 0 272 ≤ 1018064548723224223 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_106_0 t22000E_84 (by norm_num)

theorem t22000E_82 : rowsJD 105 272 0 272 ≤ 1019245708370793712 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_105_0 t22000E_83 (by norm_num)

theorem t22000E_81 : rowsJD 104 272 0 272 ≤ 1020401822157221446 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_104_0 t22000E_82 (by norm_num)

theorem t22000E_80 : rowsJD 103 272 0 272 ≤ 1021523516915523310 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_103_0 t22000E_81 (by norm_num)

theorem t22000E_79 : rowsJD 102 272 0 272 ≤ 1022609211648206515 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_102_0 t22000E_80 (by norm_num)

theorem t22000E_78 : rowsJD 101 272 0 272 ≤ 1023646935241506669 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_101_0 t22000E_79 (by norm_num)

theorem t22000E_77 : rowsJD 100 272 0 272 ≤ 1024637256785706513 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_100_0 t22000E_78 (by norm_num)

theorem t22000E_76 : rowsJD 99 272 0 272 ≤ 1025579562464737079 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_99_0 t22000E_77 (by norm_num)

theorem t22000E_75 : rowsJD 98 272 0 272 ≤ 1026475598372535728 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_98_0 t22000E_76 (by norm_num)

theorem t22000E_74 : rowsJD 97 272 0 272 ≤ 1027336357493844536 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_97_0 t22000E_75 (by norm_num)

theorem t22000E_73 : rowsJD 96 272 0 272 ≤ 1028170498969222253 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_96_0 t22000E_74 (by norm_num)

theorem t22000E_72 : rowsJD 95 272 0 272 ≤ 1028978055879578410 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_95_0 t22000E_73 (by norm_num)

theorem t22000E_71 : rowsJD 94 272 0 272 ≤ 1029764196463977575 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_94_0 t22000E_72 (by norm_num)

theorem t22000E_70 : rowsJD 93 272 0 272 ≤ 1030529471831865459 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_93_0 t22000E_71 (by norm_num)

theorem t22000E_69 : rowsJD 92 272 0 272 ≤ 1031278682411987654 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_92_0 t22000E_70 (by norm_num)

theorem t22000E_68 : rowsJD 91 272 0 272 ≤ 1032010650520699351 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_91_0 t22000E_69 (by norm_num)

theorem t22000E_67 : rowsJD 90 272 0 272 ≤ 1032728393646716047 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_90_0 t22000E_68 (by norm_num)

theorem t22000E_66 : rowsJD 89 272 0 272 ≤ 1033436884725666867 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_89_0 t22000E_67 (by norm_num)

theorem t22000E_65 : rowsJD 88 272 0 272 ≤ 1034157373895686788 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_88_0 t22000E_66 (by norm_num)

theorem t22000E_64 : rowsJD 87 272 0 272 ≤ 1034894171275194704 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_87_0 t22000E_65 (by norm_num)

theorem t22000E_63 : rowsJD 86 272 0 272 ≤ 1035653660500346946 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_86_0 t22000E_64 (by norm_num)

theorem t22000E_62 : rowsJD 85 272 0 272 ≤ 1036433276178913555 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_85_0 t22000E_63 (by norm_num)

theorem t22000E_61 : rowsJD 84 272 0 272 ≤ 1037233104973327449 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_84_0 t22000E_62 (by norm_num)

theorem t22000E_60 : rowsJD 83 272 0 272 ≤ 1038040942644809576 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_83_0 t22000E_61 (by norm_num)

theorem t22000E_59 : rowsJD 82 272 0 272 ≤ 1038849912974671166 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_82_0 t22000E_60 (by norm_num)

theorem t22000E_58 : rowsJD 81 272 0 272 ≤ 1039651565467866732 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_81_0 t22000E_59 (by norm_num)

theorem t22000E_57 : rowsJD 80 272 0 272 ≤ 1040450206168591149 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_80_0 t22000E_58 (by norm_num)

theorem t22000E_56 : rowsJD 79 272 0 272 ≤ 1041238240262269831 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_79_0 t22000E_57 (by norm_num)

theorem t22000E_55 : rowsJD 78 272 0 272 ≤ 1042019859391942322 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_78_0 t22000E_56 (by norm_num)

theorem t22000E_54 : rowsJD 77 272 0 272 ≤ 1042794098546145875 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_77_0 t22000E_55 (by norm_num)

theorem t22000E_53 : rowsJD 76 272 0 272 ≤ 1043564127636519422 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_76_0 t22000E_54 (by norm_num)

theorem t22000E_52 : rowsJD 75 272 0 272 ≤ 1044327662133618509 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_75_0 t22000E_53 (by norm_num)

theorem t22000E_51 : rowsJD 74 272 0 272 ≤ 1045086443255784353 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_74_0 t22000E_52 (by norm_num)

theorem t22000E_50 : rowsJD 73 272 0 272 ≤ 1045838424958431822 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_73_0 t22000E_51 (by norm_num)

theorem t22000E_49 : rowsJD 72 272 0 272 ≤ 1046584863885161138 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_72_0 t22000E_50 (by norm_num)

theorem t22000E_48 : rowsJD 71 272 0 272 ≤ 1047325216995892726 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_71_0 t22000E_49 (by norm_num)

theorem t22000E_47 : rowsJD 70 272 0 272 ≤ 1048068178355631952 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_70_0 t22000E_48 (by norm_num)

theorem t22000E_46 : rowsJD 69 272 0 272 ≤ 1048817879876652323 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_69_0 t22000E_47 (by norm_num)

theorem t22000E_45 : rowsJD 68 272 0 272 ≤ 1049576582588479117 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_68_0 t22000E_46 (by norm_num)

theorem t22000E_44 : rowsJD 67 272 0 272 ≤ 1050344265942565745 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_67_0 t22000E_45 (by norm_num)

theorem t22000E_43 : rowsJD 66 272 0 272 ≤ 1051122320979934706 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_66_0 t22000E_44 (by norm_num)

theorem t22000E_42 : rowsJD 65 272 0 272 ≤ 1051907827443866020 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_65_0 t22000E_43 (by norm_num)

theorem t22000E_41 : rowsJD 64 272 0 272 ≤ 1052698861769655947 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_64_0 t22000E_42 (by norm_num)

theorem t22000E_40 : rowsJD 63 272 0 272 ≤ 1053490610636892729 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_63_0 t22000E_41 (by norm_num)

theorem t22000E_39 : rowsJD 62 272 0 272 ≤ 1054283537286364024 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_62_0 t22000E_40 (by norm_num)

theorem t22000E_38 : rowsJD 61 272 0 272 ≤ 1055079887494807314 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_61_0 t22000E_39 (by norm_num)

theorem t22000E_37 : rowsJD 60 272 0 272 ≤ 1055881069296122664 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_60_0 t22000E_38 (by norm_num)

theorem t22000E_36 : rowsJD 59 272 0 272 ≤ 1056686792397197062 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_59_0 t22000E_37 (by norm_num)

theorem t22000E_35 : rowsJD 58 272 0 272 ≤ 1057498125833972206 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_58_0 t22000E_36 (by norm_num)

theorem t22000E_34 : rowsJD 57 272 0 272 ≤ 1058313678999347151 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_57_0 t22000E_35 (by norm_num)

theorem t22000E_33 : rowsJD 56 272 0 272 ≤ 1059131581155199472 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_56_0 t22000E_34 (by norm_num)

theorem t22000E_32 : rowsJD 55 272 0 272 ≤ 1059949908310142474 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_55_0 t22000E_33 (by norm_num)

theorem t22000E_31 : rowsJD 54 272 0 272 ≤ 1060766130588376845 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_54_0 t22000E_32 (by norm_num)

theorem t22000E_30 : rowsJD 53 272 0 272 ≤ 1061574115258290124 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_53_0 t22000E_31 (by norm_num)

theorem t22000E_29 : rowsJD 52 272 0 272 ≤ 1062370582242204249 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_52_0 t22000E_30 (by norm_num)

theorem t22000E_28 : rowsJD 51 272 0 272 ≤ 1063152220641287694 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_51_0 t22000E_29 (by norm_num)

theorem t22000E_27 : rowsJD 50 272 0 272 ≤ 1063916214356885711 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_50_0 t22000E_28 (by norm_num)

theorem t22000E_26 : rowsJD 49 272 0 272 ≤ 1064659448035570037 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_49_0 t22000E_27 (by norm_num)

theorem t22000E_25 : rowsJD 48 272 0 272 ≤ 1065379256242583420 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_48_0 t22000E_26 (by norm_num)

theorem t22000E_24 : rowsJD 47 272 0 272 ≤ 1066073383340957485 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_47_0 t22000E_25 (by norm_num)

theorem t22000E_23 : rowsJD 46 272 0 272 ≤ 1066739400371548900 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_46_0 t22000E_24 (by norm_num)

theorem t22000E_22 : rowsJD 45 272 0 272 ≤ 1067373923769679414 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_45_0 t22000E_23 (by norm_num)

theorem t22000E_21 : rowsJD 44 272 0 272 ≤ 1067974954342863221 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_44_0 t22000E_22 (by norm_num)

theorem t22000E_20 : rowsJD 43 272 0 272 ≤ 1068543988458174169 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_43_0 t22000E_21 (by norm_num)

theorem t22000E_19 : rowsJD 42 272 0 272 ≤ 1069083543996694863 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_42_0 t22000E_20 (by norm_num)

theorem t22000E_18 : rowsJD 41 272 0 272 ≤ 1069593116458381207 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_41_0 t22000E_19 (by norm_num)

theorem t22000E_17 : rowsJD 40 272 0 272 ≤ 1070072593928978966 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_40_0 t22000E_18 (by norm_num)

theorem t22000E_16 : rowsJD 39 272 0 272 ≤ 1070526187011900450 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_39_0 t22000E_17 (by norm_num)

theorem t22000E_15 : rowsJD 38 272 0 272 ≤ 1070958449190819612 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_38_0 t22000E_16 (by norm_num)

theorem t22000E_14 : rowsJD 37 272 0 272 ≤ 1071370831557408701 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) c22000E_37_0 t22000E_15 (by norm_num)

theorem t22000E_13 : rowsJD 36 272 0 272 ≤ 1071763223363479321 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_13 t22000E_14 (by norm_num)

theorem t22000E_12 : rowsJD 35 272 0 272 ≤ 1072135198135058783 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_12 t22000E_13 (by norm_num)

theorem t22000E_11 : rowsJD 34 272 0 272 ≤ 1072485636525763729 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_11 t22000E_12 (by norm_num)

theorem t22000E_10 : rowsJD 33 272 0 272 ≤ 1072813805641518236 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_10 t22000E_11 (by norm_num)

theorem t22000E_9 : rowsJD 32 272 0 272 ≤ 1073119280525086804 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_9 t22000E_10 (by norm_num)

theorem t22000E_8 : rowsJD 31 272 0 272 ≤ 1073401782673583537 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_8 t22000E_9 (by norm_num)

theorem t22000E_7 : rowsJD 30 272 0 272 ≤ 1073661698197976383 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_7 t22000E_8 (by norm_num)

theorem t22000E_6 : rowsJD 29 272 0 272 ≤ 1073900355398579979 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_6 t22000E_7 (by norm_num)

theorem t22000E_5 : rowsJD 28 272 0 272 ≤ 1074118987892294850 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_5 t22000E_6 (by norm_num)

theorem t22000E_4 : rowsJD 26 272 0 272 ≤ 1074500500108929033 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_4 t22000E_5 (by norm_num)

theorem t22000E_3 : rowsJD 24 272 0 272 ≤ 1074814118444354153 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_3 t22000E_4 (by norm_num)

theorem t22000E_2 : rowsJD 21 272 0 272 ≤ 1075173593149941824 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_2 t22000E_3 (by norm_num)

theorem t22000E_1 : rowsJD 17 272 0 272 ≤ 1075483808483152479 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_1 t22000E_2 (by norm_num)

theorem t22000E_0 : rowsJD 0 272 0 272 ≤ 1075756859466551505 :=
  rowsJD_le_of_splitI 0 272 (by norm_num) (by norm_num) rows22000E_0 t22000E_1 (by norm_num)

/-- **The certificate to depth 8 on `grid22000E`**: the loss's bound is less than `K`, the 1136 parts checked by the
kernel. -/
theorem totalD_lt_22000E : totalD < K := by
  rw [totalD_eq_rowsJD]
  exact lt_of_le_of_lt t22000E_0 (by decide +kernel)

end

end SieveDeep

#print axioms SieveDeep.totalD_lt_22000E
