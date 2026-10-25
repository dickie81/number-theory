/-
# The refined certificate of the sieve route's loss at `L = 89/40` with `n = 340`: `total2 < K`

On `SieveGrid22250R.grid22250R` (`U1 = ⌈(41479/100000)DEN⌉`, `U2 = ⌊(47555/100000)DEN⌋`, `n = 340`),
`SieveCert.total2` is less than `K` (it is below `0.99602K`, rounded up; the certificate of `SieveCertDefs.lean` on
the same grid totals `1.11742K`): `total2` is `rows2 0 n` (`SieveCert2.total2_eq_rows2_full`), and its bound is
assembled one step at a time from the 4715 parts' bounds (`rows22250R_0` … `rows22250R_4714`, each by `decide
+kernel` in one of the 351 part files): a heavy row's bound from its column pieces' (`rowsJ2_le_of_split`,
`rows2_le_of_rowsJ2`), then the 237 ranges of rows from the last to the first (`rows2_le_of_split`), every bound a
literal and every step a theorem of its own (`c22250R_…`, `hr22250R_…`, `t22250R_…`); the bounds, `⌈1.001 × part⌉`
computed exactly in integers, sum to `1149475836901239458`, less than `K` by `decide +kernel` (`total2_lt_22250R`).

The file imports `SieveCert2.lean` and `SieveCert22250RP1.lean` … `SieveCert22250RP351.lean`.
-/
import SieveCert2
import SieveCert22250RP1
import SieveCert22250RP2
import SieveCert22250RP3
import SieveCert22250RP4
import SieveCert22250RP5
import SieveCert22250RP6
import SieveCert22250RP7
import SieveCert22250RP8
import SieveCert22250RP9
import SieveCert22250RP10
import SieveCert22250RP11
import SieveCert22250RP12
import SieveCert22250RP13
import SieveCert22250RP14
import SieveCert22250RP15
import SieveCert22250RP16
import SieveCert22250RP17
import SieveCert22250RP18
import SieveCert22250RP19
import SieveCert22250RP20
import SieveCert22250RP21
import SieveCert22250RP22
import SieveCert22250RP23
import SieveCert22250RP24
import SieveCert22250RP25
import SieveCert22250RP26
import SieveCert22250RP27
import SieveCert22250RP28
import SieveCert22250RP29
import SieveCert22250RP30
import SieveCert22250RP31
import SieveCert22250RP32
import SieveCert22250RP33
import SieveCert22250RP34
import SieveCert22250RP35
import SieveCert22250RP36
import SieveCert22250RP37
import SieveCert22250RP38
import SieveCert22250RP39
import SieveCert22250RP40
import SieveCert22250RP41
import SieveCert22250RP42
import SieveCert22250RP43
import SieveCert22250RP44
import SieveCert22250RP45
import SieveCert22250RP46
import SieveCert22250RP47
import SieveCert22250RP48
import SieveCert22250RP49
import SieveCert22250RP50
import SieveCert22250RP51
import SieveCert22250RP52
import SieveCert22250RP53
import SieveCert22250RP54
import SieveCert22250RP55
import SieveCert22250RP56
import SieveCert22250RP57
import SieveCert22250RP58
import SieveCert22250RP59
import SieveCert22250RP60
import SieveCert22250RP61
import SieveCert22250RP62
import SieveCert22250RP63
import SieveCert22250RP64
import SieveCert22250RP65
import SieveCert22250RP66
import SieveCert22250RP67
import SieveCert22250RP68
import SieveCert22250RP69
import SieveCert22250RP70
import SieveCert22250RP71
import SieveCert22250RP72
import SieveCert22250RP73
import SieveCert22250RP74
import SieveCert22250RP75
import SieveCert22250RP76
import SieveCert22250RP77
import SieveCert22250RP78
import SieveCert22250RP79
import SieveCert22250RP80
import SieveCert22250RP81
import SieveCert22250RP82
import SieveCert22250RP83
import SieveCert22250RP84
import SieveCert22250RP85
import SieveCert22250RP86
import SieveCert22250RP87
import SieveCert22250RP88
import SieveCert22250RP89
import SieveCert22250RP90
import SieveCert22250RP91
import SieveCert22250RP92
import SieveCert22250RP93
import SieveCert22250RP94
import SieveCert22250RP95
import SieveCert22250RP96
import SieveCert22250RP97
import SieveCert22250RP98
import SieveCert22250RP99
import SieveCert22250RP100
import SieveCert22250RP101
import SieveCert22250RP102
import SieveCert22250RP103
import SieveCert22250RP104
import SieveCert22250RP105
import SieveCert22250RP106
import SieveCert22250RP107
import SieveCert22250RP108
import SieveCert22250RP109
import SieveCert22250RP110
import SieveCert22250RP111
import SieveCert22250RP112
import SieveCert22250RP113
import SieveCert22250RP114
import SieveCert22250RP115
import SieveCert22250RP116
import SieveCert22250RP117
import SieveCert22250RP118
import SieveCert22250RP119
import SieveCert22250RP120
import SieveCert22250RP121
import SieveCert22250RP122
import SieveCert22250RP123
import SieveCert22250RP124
import SieveCert22250RP125
import SieveCert22250RP126
import SieveCert22250RP127
import SieveCert22250RP128
import SieveCert22250RP129
import SieveCert22250RP130
import SieveCert22250RP131
import SieveCert22250RP132
import SieveCert22250RP133
import SieveCert22250RP134
import SieveCert22250RP135
import SieveCert22250RP136
import SieveCert22250RP137
import SieveCert22250RP138
import SieveCert22250RP139
import SieveCert22250RP140
import SieveCert22250RP141
import SieveCert22250RP142
import SieveCert22250RP143
import SieveCert22250RP144
import SieveCert22250RP145
import SieveCert22250RP146
import SieveCert22250RP147
import SieveCert22250RP148
import SieveCert22250RP149
import SieveCert22250RP150
import SieveCert22250RP151
import SieveCert22250RP152
import SieveCert22250RP153
import SieveCert22250RP154
import SieveCert22250RP155
import SieveCert22250RP156
import SieveCert22250RP157
import SieveCert22250RP158
import SieveCert22250RP159
import SieveCert22250RP160
import SieveCert22250RP161
import SieveCert22250RP162
import SieveCert22250RP163
import SieveCert22250RP164
import SieveCert22250RP165
import SieveCert22250RP166
import SieveCert22250RP167
import SieveCert22250RP168
import SieveCert22250RP169
import SieveCert22250RP170
import SieveCert22250RP171
import SieveCert22250RP172
import SieveCert22250RP173
import SieveCert22250RP174
import SieveCert22250RP175
import SieveCert22250RP176
import SieveCert22250RP177
import SieveCert22250RP178
import SieveCert22250RP179
import SieveCert22250RP180
import SieveCert22250RP181
import SieveCert22250RP182
import SieveCert22250RP183
import SieveCert22250RP184
import SieveCert22250RP185
import SieveCert22250RP186
import SieveCert22250RP187
import SieveCert22250RP188
import SieveCert22250RP189
import SieveCert22250RP190
import SieveCert22250RP191
import SieveCert22250RP192
import SieveCert22250RP193
import SieveCert22250RP194
import SieveCert22250RP195
import SieveCert22250RP196
import SieveCert22250RP197
import SieveCert22250RP198
import SieveCert22250RP199
import SieveCert22250RP200
import SieveCert22250RP201
import SieveCert22250RP202
import SieveCert22250RP203
import SieveCert22250RP204
import SieveCert22250RP205
import SieveCert22250RP206
import SieveCert22250RP207
import SieveCert22250RP208
import SieveCert22250RP209
import SieveCert22250RP210
import SieveCert22250RP211
import SieveCert22250RP212
import SieveCert22250RP213
import SieveCert22250RP214
import SieveCert22250RP215
import SieveCert22250RP216
import SieveCert22250RP217
import SieveCert22250RP218
import SieveCert22250RP219
import SieveCert22250RP220
import SieveCert22250RP221
import SieveCert22250RP222
import SieveCert22250RP223
import SieveCert22250RP224
import SieveCert22250RP225
import SieveCert22250RP226
import SieveCert22250RP227
import SieveCert22250RP228
import SieveCert22250RP229
import SieveCert22250RP230
import SieveCert22250RP231
import SieveCert22250RP232
import SieveCert22250RP233
import SieveCert22250RP234
import SieveCert22250RP235
import SieveCert22250RP236
import SieveCert22250RP237
import SieveCert22250RP238
import SieveCert22250RP239
import SieveCert22250RP240
import SieveCert22250RP241
import SieveCert22250RP242
import SieveCert22250RP243
import SieveCert22250RP244
import SieveCert22250RP245
import SieveCert22250RP246
import SieveCert22250RP247
import SieveCert22250RP248
import SieveCert22250RP249
import SieveCert22250RP250
import SieveCert22250RP251
import SieveCert22250RP252
import SieveCert22250RP253
import SieveCert22250RP254
import SieveCert22250RP255
import SieveCert22250RP256
import SieveCert22250RP257
import SieveCert22250RP258
import SieveCert22250RP259
import SieveCert22250RP260
import SieveCert22250RP261
import SieveCert22250RP262
import SieveCert22250RP263
import SieveCert22250RP264
import SieveCert22250RP265
import SieveCert22250RP266
import SieveCert22250RP267
import SieveCert22250RP268
import SieveCert22250RP269
import SieveCert22250RP270
import SieveCert22250RP271
import SieveCert22250RP272
import SieveCert22250RP273
import SieveCert22250RP274
import SieveCert22250RP275
import SieveCert22250RP276
import SieveCert22250RP277
import SieveCert22250RP278
import SieveCert22250RP279
import SieveCert22250RP280
import SieveCert22250RP281
import SieveCert22250RP282
import SieveCert22250RP283
import SieveCert22250RP284
import SieveCert22250RP285
import SieveCert22250RP286
import SieveCert22250RP287
import SieveCert22250RP288
import SieveCert22250RP289
import SieveCert22250RP290
import SieveCert22250RP291
import SieveCert22250RP292
import SieveCert22250RP293
import SieveCert22250RP294
import SieveCert22250RP295
import SieveCert22250RP296
import SieveCert22250RP297
import SieveCert22250RP298
import SieveCert22250RP299
import SieveCert22250RP300
import SieveCert22250RP301
import SieveCert22250RP302
import SieveCert22250RP303
import SieveCert22250RP304
import SieveCert22250RP305
import SieveCert22250RP306
import SieveCert22250RP307
import SieveCert22250RP308
import SieveCert22250RP309
import SieveCert22250RP310
import SieveCert22250RP311
import SieveCert22250RP312
import SieveCert22250RP313
import SieveCert22250RP314
import SieveCert22250RP315
import SieveCert22250RP316
import SieveCert22250RP317
import SieveCert22250RP318
import SieveCert22250RP319
import SieveCert22250RP320
import SieveCert22250RP321
import SieveCert22250RP322
import SieveCert22250RP323
import SieveCert22250RP324
import SieveCert22250RP325
import SieveCert22250RP326
import SieveCert22250RP327
import SieveCert22250RP328
import SieveCert22250RP329
import SieveCert22250RP330
import SieveCert22250RP331
import SieveCert22250RP332
import SieveCert22250RP333
import SieveCert22250RP334
import SieveCert22250RP335
import SieveCert22250RP336
import SieveCert22250RP337
import SieveCert22250RP338
import SieveCert22250RP339
import SieveCert22250RP340
import SieveCert22250RP341
import SieveCert22250RP342
import SieveCert22250RP343
import SieveCert22250RP344
import SieveCert22250RP345
import SieveCert22250RP346
import SieveCert22250RP347
import SieveCert22250RP348
import SieveCert22250RP349
import SieveCert22250RP350
import SieveCert22250RP351

namespace SieveCert

section

attribute [local instance] grid22250R

/-! The chain of bounds: `c22250R_{i}_{m}` for the heavy row `i` from its `m`-th column piece on, `hr22250R_{i}` for
the heavy row `i`, `t22250R_{m}` for the rows from the `m`-th range on; each a theorem of its own, its name distinct
from the other certificates' chains in the same namespace. -/

theorem c22250R_14_0 : rowsJ2 14 15 0 340 ≤ 4462387305321 :=
  rowsJ2_le_of_split 14 15 (by norm_num) (by norm_num) rows22250R_4 rows22250R_5 (by norm_num)

theorem hr22250R_14 : rows2 14 15 ≤ 4462387305321 := rows2_le_of_rowsJ2 14 15 c22250R_14_0

theorem c22250R_15_0 : rowsJ2 15 16 0 340 ≤ 4353679682364 :=
  rowsJ2_le_of_split 15 16 (by norm_num) (by norm_num) rows22250R_6 rows22250R_7 (by norm_num)

theorem hr22250R_15 : rows2 15 16 ≤ 4353679682364 := rows2_le_of_rowsJ2 15 16 c22250R_15_0

theorem c22250R_16_0 : rowsJ2 16 17 0 340 ≤ 4317783535766 :=
  rowsJ2_le_of_split 16 17 (by norm_num) (by norm_num) rows22250R_8 rows22250R_9 (by norm_num)

theorem hr22250R_16 : rows2 16 17 ≤ 4317783535766 := rows2_le_of_rowsJ2 16 17 c22250R_16_0

theorem c22250R_17_1 : rowsJ2 17 18 14 340 ≤ 1386145288233 :=
  rowsJ2_le_of_split 17 18 (by norm_num) (by norm_num) rows22250R_11 rows22250R_12 (by norm_num)

theorem c22250R_17_0 : rowsJ2 17 18 0 340 ≤ 4505674062354 :=
  rowsJ2_le_of_split 17 18 (by norm_num) (by norm_num) rows22250R_10 c22250R_17_1 (by norm_num)

theorem hr22250R_17 : rows2 17 18 ≤ 4505674062354 := rows2_le_of_rowsJ2 17 18 c22250R_17_0

theorem c22250R_18_1 : rowsJ2 18 19 14 340 ≤ 2223798448557 :=
  rowsJ2_le_of_split 18 19 (by norm_num) (by norm_num) rows22250R_14 rows22250R_15 (by norm_num)

theorem c22250R_18_0 : rowsJ2 18 19 0 340 ≤ 5039950823844 :=
  rowsJ2_le_of_split 18 19 (by norm_num) (by norm_num) rows22250R_13 c22250R_18_1 (by norm_num)

theorem hr22250R_18 : rows2 18 19 ≤ 5039950823844 := rows2_le_of_rowsJ2 18 19 c22250R_18_0

theorem c22250R_19_2 : rowsJ2 19 20 17 340 ≤ 2623035713143 :=
  rowsJ2_le_of_split 19 20 (by norm_num) (by norm_num) rows22250R_18 rows22250R_19 (by norm_num)

theorem c22250R_19_1 : rowsJ2 19 20 14 340 ≤ 3434305912063 :=
  rowsJ2_le_of_split 19 20 (by norm_num) (by norm_num) rows22250R_17 c22250R_19_2 (by norm_num)

theorem c22250R_19_0 : rowsJ2 19 20 0 340 ≤ 5962785084407 :=
  rowsJ2_le_of_split 19 20 (by norm_num) (by norm_num) rows22250R_16 c22250R_19_1 (by norm_num)

theorem hr22250R_19 : rows2 19 20 ≤ 5962785084407 := rows2_le_of_rowsJ2 19 20 c22250R_19_0

theorem c22250R_20_3 : rowsJ2 20 21 19 340 ≤ 2689093444156 :=
  rowsJ2_le_of_split 20 21 (by norm_num) (by norm_num) rows22250R_23 rows22250R_24 (by norm_num)

theorem c22250R_20_2 : rowsJ2 20 21 17 340 ≤ 4226693688948 :=
  rowsJ2_le_of_split 20 21 (by norm_num) (by norm_num) rows22250R_22 c22250R_20_3 (by norm_num)

theorem c22250R_20_1 : rowsJ2 20 21 14 340 ≤ 5066873745464 :=
  rowsJ2_le_of_split 20 21 (by norm_num) (by norm_num) rows22250R_21 c22250R_20_2 (by norm_num)

theorem c22250R_20_0 : rowsJ2 20 21 0 340 ≤ 7326271695000 :=
  rowsJ2_le_of_split 20 21 (by norm_num) (by norm_num) rows22250R_20 c22250R_20_1 (by norm_num)

theorem hr22250R_20 : rows2 20 21 ≤ 7326271695000 := rows2_le_of_rowsJ2 20 21 c22250R_20_0

theorem c22250R_21_4 : rowsJ2 21 22 20 340 ≤ 3242635436556 :=
  rowsJ2_le_of_split 21 22 (by norm_num) (by norm_num) rows22250R_29 rows22250R_30 (by norm_num)

theorem c22250R_21_3 : rowsJ2 21 22 19 340 ≤ 4491206064307 :=
  rowsJ2_le_of_split 21 22 (by norm_num) (by norm_num) rows22250R_28 c22250R_21_4 (by norm_num)

theorem c22250R_21_2 : rowsJ2 21 22 17 340 ≤ 6117633616904 :=
  rowsJ2_le_of_split 21 22 (by norm_num) (by norm_num) rows22250R_27 c22250R_21_3 (by norm_num)

theorem c22250R_21_1 : rowsJ2 21 22 14 340 ≤ 6994550545620 :=
  rowsJ2_le_of_split 21 22 (by norm_num) (by norm_num) rows22250R_26 c22250R_21_2 (by norm_num)

theorem c22250R_21_0 : rowsJ2 21 22 0 340 ≤ 8999504036168 :=
  rowsJ2_le_of_split 21 22 (by norm_num) (by norm_num) rows22250R_25 c22250R_21_1 (by norm_num)

theorem hr22250R_21 : rows2 21 22 ≤ 8999504036168 := rows2_le_of_rowsJ2 21 22 c22250R_21_0

theorem c22250R_22_5 : rowsJ2 22 23 21 340 ≤ 3610842532634 :=
  rowsJ2_le_of_split 22 23 (by norm_num) (by norm_num) rows22250R_36 rows22250R_37 (by norm_num)

theorem c22250R_22_4 : rowsJ2 22 23 20 340 ≤ 5135080359688 :=
  rowsJ2_le_of_split 22 23 (by norm_num) (by norm_num) rows22250R_35 c22250R_22_5 (by norm_num)

theorem c22250R_22_3 : rowsJ2 22 23 19 340 ≤ 6419721287307 :=
  rowsJ2_le_of_split 22 23 (by norm_num) (by norm_num) rows22250R_34 c22250R_22_4 (by norm_num)

theorem c22250R_22_2 : rowsJ2 22 23 17 340 ≤ 8149094546939 :=
  rowsJ2_le_of_split 22 23 (by norm_num) (by norm_num) rows22250R_33 c22250R_22_3 (by norm_num)

theorem c22250R_22_1 : rowsJ2 22 23 14 340 ≤ 9084897667313 :=
  rowsJ2_le_of_split 22 23 (by norm_num) (by norm_num) rows22250R_32 c22250R_22_2 (by norm_num)

theorem c22250R_22_0 : rowsJ2 22 23 0 340 ≤ 10857430694856 :=
  rowsJ2_le_of_split 22 23 (by norm_num) (by norm_num) rows22250R_31 c22250R_22_1 (by norm_num)

theorem hr22250R_22 : rows2 22 23 ≤ 10857430694856 := rows2_le_of_rowsJ2 22 23 c22250R_22_0

theorem c22250R_23_6 : rowsJ2 23 24 22 340 ≤ 3784215030493 :=
  rowsJ2_le_of_split 23 24 (by norm_num) (by norm_num) rows22250R_44 rows22250R_45 (by norm_num)

theorem c22250R_23_5 : rowsJ2 23 24 21 340 ≤ 5498511283659 :=
  rowsJ2_le_of_split 23 24 (by norm_num) (by norm_num) rows22250R_43 c22250R_23_6 (by norm_num)

theorem c22250R_23_4 : rowsJ2 23 24 20 340 ≤ 7029954961528 :=
  rowsJ2_le_of_split 23 24 (by norm_num) (by norm_num) rows22250R_42 c22250R_23_5 (by norm_num)

theorem c22250R_23_3 : rowsJ2 23 24 19 340 ≤ 8343146801980 :=
  rowsJ2_le_of_split 23 24 (by norm_num) (by norm_num) rows22250R_41 c22250R_23_4 (by norm_num)

theorem c22250R_23_2 : rowsJ2 23 24 17 340 ≤ 10176759541292 :=
  rowsJ2_le_of_split 23 24 (by norm_num) (by norm_num) rows22250R_40 c22250R_23_3 (by norm_num)

theorem c22250R_23_1 : rowsJ2 23 24 14 340 ≤ 11184261894669 :=
  rowsJ2_le_of_split 23 24 (by norm_num) (by norm_num) rows22250R_39 c22250R_23_2 (by norm_num)

theorem c22250R_23_0 : rowsJ2 23 24 0 340 ≤ 12742492749389 :=
  rowsJ2_le_of_split 23 24 (by norm_num) (by norm_num) rows22250R_38 c22250R_23_1 (by norm_num)

theorem hr22250R_23 : rows2 23 24 ≤ 12742492749389 := rows2_le_of_rowsJ2 23 24 c22250R_23_0

theorem c22250R_24_7 : rowsJ2 24 25 23 340 ≤ 3752227539062 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22250R_53 rows22250R_54 (by norm_num)

theorem c22250R_24_6 : rowsJ2 24 25 22 340 ≤ 5562746527427 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22250R_52 c22250R_24_7 (by norm_num)

theorem c22250R_24_5 : rowsJ2 24 25 21 340 ≤ 7264378734688 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22250R_51 c22250R_24_6 (by norm_num)

theorem c22250R_24_4 : rowsJ2 24 25 20 340 ≤ 8796642477170 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22250R_50 c22250R_24_5 (by norm_num)

theorem c22250R_24_3 : rowsJ2 24 25 19 340 ≤ 10127050584727 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22250R_49 c22250R_24_4 (by norm_num)

theorem c22250R_24_2 : rowsJ2 24 25 17 340 ≤ 12049504690682 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22250R_48 c22250R_24_3 (by norm_num)

theorem c22250R_24_1 : rowsJ2 24 25 14 340 ≤ 13160153794567 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22250R_47 c22250R_24_2 (by norm_num)

theorem c22250R_24_0 : rowsJ2 24 25 0 340 ≤ 14525525020672 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22250R_46 c22250R_24_1 (by norm_num)

theorem hr22250R_24 : rows2 24 25 ≤ 14525525020672 := rows2_le_of_rowsJ2 24 25 c22250R_24_0

theorem c22250R_25_8 : rowsJ2 25 26 24 340 ≤ 3632275731887 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22250R_63 rows22250R_64 (by norm_num)

theorem c22250R_25_7 : rowsJ2 25 26 23 340 ≤ 5429446755422 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22250R_62 c22250R_25_8 (by norm_num)

theorem c22250R_25_6 : rowsJ2 25 26 22 340 ≤ 7192261514341 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22250R_61 c22250R_25_7 (by norm_num)

theorem c22250R_25_5 : rowsJ2 25 26 21 340 ≤ 8867314856651 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22250R_60 c22250R_25_6 (by norm_num)

theorem c22250R_25_4 : rowsJ2 25 26 20 340 ≤ 10400004946237 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22250R_59 c22250R_25_5 (by norm_num)

theorem c22250R_25_3 : rowsJ2 25 26 19 340 ≤ 11741048793191 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22250R_58 c22250R_25_4 (by norm_num)

theorem c22250R_25_2 : rowsJ2 25 26 17 340 ≤ 13741795773115 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22250R_57 c22250R_25_3 (by norm_num)

theorem c22250R_25_1 : rowsJ2 25 26 14 340 ≤ 14959985892101 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22250R_56 c22250R_25_2 (by norm_num)

theorem c22250R_25_0 : rowsJ2 25 26 0 340 ≤ 16157524365574 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22250R_55 c22250R_25_1 (by norm_num)

theorem hr22250R_25 : rows2 25 26 ≤ 16157524365574 := rows2_le_of_rowsJ2 25 26 c22250R_25_0

theorem c22250R_26_9 : rowsJ2 26 27 25 340 ≤ 3413367271939 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22250R_74 rows22250R_75 (by norm_num)

theorem c22250R_26_8 : rowsJ2 26 27 24 340 ≤ 5161698318047 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22250R_73 c22250R_26_9 (by norm_num)

theorem c22250R_26_7 : rowsJ2 26 27 23 340 ≤ 6899178171182 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22250R_72 c22250R_26_8 (by norm_num)

theorem c22250R_26_6 : rowsJ2 26 27 22 340 ≤ 8600737692594 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22250R_71 c22250R_26_7 (by norm_num)

theorem c22250R_26_5 : rowsJ2 26 27 21 340 ≤ 10244839668298 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22250R_70 c22250R_26_6 (by norm_num)

theorem c22250R_26_4 : rowsJ2 26 27 20 340 ≤ 11768115669224 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22250R_69 c22250R_26_5 (by norm_num)

theorem c22250R_26_3 : rowsJ2 26 27 19 340 ≤ 13119220364284 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22250R_68 c22250R_26_4 (by norm_num)

theorem c22250R_26_2 : rowsJ2 26 27 17 340 ≤ 15179075471594 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22250R_67 c22250R_26_3 (by norm_num)

theorem c22250R_26_1 : rowsJ2 26 27 14 340 ≤ 16521961090503 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22250R_66 c22250R_26_2 (by norm_num)

theorem c22250R_26_0 : rowsJ2 26 27 0 340 ≤ 17572953960202 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22250R_65 c22250R_26_1 (by norm_num)

theorem hr22250R_26 : rows2 26 27 ≤ 17572953960202 := rows2_le_of_rowsJ2 26 27 c22250R_26_0

theorem c22250R_27_10 : rowsJ2 27 28 26 340 ≤ 3093353980902 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_86 rows22250R_87 (by norm_num)

theorem c22250R_27_9 : rowsJ2 27 28 25 340 ≤ 4740785437539 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_85 c22250R_27_10 (by norm_num)

theorem c22250R_27_8 : rowsJ2 27 28 24 340 ≤ 6422297774846 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_84 c22250R_27_9 (by norm_num)

theorem c22250R_27_7 : rowsJ2 27 28 23 340 ≤ 8095620841202 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_83 c22250R_27_8 (by norm_num)

theorem c22250R_27_6 : rowsJ2 27 28 22 340 ≤ 9744719383340 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_82 c22250R_27_7 (by norm_num)

theorem c22250R_27_5 : rowsJ2 27 28 21 340 ≤ 11344073176208 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_81 c22250R_27_6 (by norm_num)

theorem c22250R_27_4 : rowsJ2 27 28 20 340 ≤ 12853313745644 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_80 c22250R_27_5 (by norm_num)

theorem c22250R_27_3 : rowsJ2 27 28 19 340 ≤ 14208001020733 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_79 c22250R_27_4 (by norm_num)

theorem c22250R_27_2 : rowsJ2 27 28 17 340 ≤ 16318581309938 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_78 c22250R_27_3 (by norm_num)

theorem c22250R_27_1 : rowsJ2 27 28 14 340 ≤ 17778650347386 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_77 c22250R_27_2 (by norm_num)

theorem c22250R_27_0 : rowsJ2 27 28 0 340 ≤ 18708120201779 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_76 c22250R_27_1 (by norm_num)

theorem hr22250R_27 : rows2 27 28 ≤ 18708120201779 := rows2_le_of_rowsJ2 27 28 c22250R_27_0

theorem c22250R_28_10 : rowsJ2 28 29 27 340 ≤ 2737501809459 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_98 rows22250R_99 (by norm_num)

theorem c22250R_28_9 : rowsJ2 28 29 26 340 ≤ 4226518402618 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_97 c22250R_28_10 (by norm_num)

theorem c22250R_28_8 : rowsJ2 28 29 25 340 ≤ 5784447722386 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_96 c22250R_28_9 (by norm_num)

theorem c22250R_28_7 : rowsJ2 28 29 24 340 ≤ 7390137602213 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_95 c22250R_28_8 (by norm_num)

theorem c22250R_28_6 : rowsJ2 28 29 23 340 ≤ 9008106893252 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_94 c22250R_28_7 (by norm_num)

theorem c22250R_28_5 : rowsJ2 28 29 22 340 ≤ 10600140754176 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_93 c22250R_28_6 (by norm_num)

theorem c22250R_28_4 : rowsJ2 28 29 21 340 ≤ 12154307350462 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_92 c22250R_28_5 (by norm_num)

theorem c22250R_28_3 : rowsJ2 28 29 19 340 ≤ 14993224141506 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_91 c22250R_28_4 (by norm_num)

theorem c22250R_28_2 : rowsJ2 28 29 17 340 ≤ 17139846140586 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_90 c22250R_28_3 (by norm_num)

theorem c22250R_28_1 : rowsJ2 28 29 14 340 ≤ 18722567666912 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_89 c22250R_28_2 (by norm_num)

theorem c22250R_28_0 : rowsJ2 28 29 0 340 ≤ 19559467641177 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_88 c22250R_28_1 (by norm_num)

theorem hr22250R_28 : rows2 28 29 ≤ 19559467641177 := rows2_le_of_rowsJ2 28 29 c22250R_28_0

theorem c22250R_29_11 : rowsJ2 29 30 28 340 ≤ 2368337946660 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_111 rows22250R_112 (by norm_num)

theorem c22250R_29_10 : rowsJ2 29 30 27 340 ≤ 3682460916532 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_110 c22250R_29_11 (by norm_num)

theorem c22250R_29_9 : rowsJ2 29 30 26 340 ≤ 5079710046734 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_109 c22250R_29_10 (by norm_num)

theorem c22250R_29_8 : rowsJ2 29 30 25 340 ≤ 6545914322138 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_108 c22250R_29_9 (by norm_num)

theorem c22250R_29_7 : rowsJ2 29 30 24 340 ≤ 8073219872102 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_107 c22250R_29_8 (by norm_num)

theorem c22250R_29_6 : rowsJ2 29 30 23 340 ≤ 9626681307826 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_106 c22250R_29_7 (by norm_num)

theorem c22250R_29_5 : rowsJ2 29 30 22 340 ≤ 11170335719274 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_105 c22250R_29_6 (by norm_num)

theorem c22250R_29_4 : rowsJ2 29 30 21 340 ≤ 12674574637309 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_104 c22250R_29_5 (by norm_num)

theorem c22250R_29_3 : rowsJ2 29 30 19 340 ≤ 15473531401557 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_103 c22250R_29_4 (by norm_num)

theorem c22250R_29_2 : rowsJ2 29 30 17 340 ≤ 17655213352718 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_102 c22250R_29_3 (by norm_num)

theorem c22250R_29_1 : rowsJ2 29 30 14 340 ≤ 19345834910307 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_101 c22250R_29_2 (by norm_num)

theorem c22250R_29_0 : rowsJ2 29 30 0 340 ≤ 20115421849959 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_100 c22250R_29_1 (by norm_num)

theorem hr22250R_29 : rows2 29 30 ≤ 20115421849959 := rows2_le_of_rowsJ2 29 30 c22250R_29_0

theorem c22250R_30_11 : rowsJ2 30 31 29 340 ≤ 2035400181839 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_124 rows22250R_125 (by norm_num)

theorem c22250R_30_10 : rowsJ2 30 31 28 340 ≤ 3164386838066 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_123 c22250R_30_11 (by norm_num)

theorem c22250R_30_9 : rowsJ2 30 31 27 340 ≤ 4385070440506 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_122 c22250R_30_10 (by norm_num)

theorem c22250R_30_8 : rowsJ2 30 31 26 340 ≤ 5688204805045 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_121 c22250R_30_9 (by norm_num)

theorem c22250R_30_7 : rowsJ2 30 31 25 340 ≤ 7066835669527 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_120 c22250R_30_8 (by norm_num)

theorem c22250R_30_6 : rowsJ2 30 31 24 340 ≤ 8506673749669 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_119 c22250R_30_7 (by norm_num)

theorem c22250R_30_5 : rowsJ2 30 31 23 340 ≤ 9992929981234 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_118 c22250R_30_6 (by norm_num)

theorem c22250R_30_4 : rowsJ2 30 31 21 340 ≤ 12946351856617 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_117 c22250R_30_5 (by norm_num)

theorem c22250R_30_3 : rowsJ2 30 31 19 340 ≤ 15690478614324 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_116 c22250R_30_4 (by norm_num)

theorem c22250R_30_2 : rowsJ2 30 31 17 340 ≤ 17899820821471 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_115 c22250R_30_3 (by norm_num)

theorem c22250R_30_1 : rowsJ2 30 31 14 340 ≤ 19694547601257 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_114 c22250R_30_2 (by norm_num)

theorem c22250R_30_0 : rowsJ2 30 31 0 340 ≤ 20418124572240 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_113 c22250R_30_1 (by norm_num)

theorem hr22250R_30 : rows2 30 31 ≤ 20418124572240 := rows2_le_of_rowsJ2 30 31 c22250R_30_0

theorem c22250R_31_11 : rowsJ2 31 32 30 340 ≤ 1791695178307 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_137 rows22250R_138 (by norm_num)

theorem c22250R_31_10 : rowsJ2 31 32 29 340 ≤ 2753898552105 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_136 c22250R_31_11 (by norm_num)

theorem c22250R_31_9 : rowsJ2 31 32 28 340 ≤ 3793681447155 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_135 c22250R_31_10 (by norm_num)

theorem c22250R_31_8 : rowsJ2 31 32 27 340 ≤ 4918426946319 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_134 c22250R_31_9 (by norm_num)

theorem c22250R_31_7 : rowsJ2 31 32 26 340 ≤ 6131470532928 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_133 c22250R_31_8 (by norm_num)

theorem c22250R_31_6 : rowsJ2 31 32 25 340 ≤ 7420109938889 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_132 c22250R_31_7 (by norm_num)

theorem c22250R_31_5 : rowsJ2 31 32 23 340 ≤ 10186397572591 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_131 c22250R_31_6 (by norm_num)

theorem c22250R_31_4 : rowsJ2 31 32 21 340 ≤ 13037655161021 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_130 c22250R_31_5 (by norm_num)

theorem c22250R_31_3 : rowsJ2 31 32 19 340 ≤ 15721192852275 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_129 c22250R_31_4 (by norm_num)

theorem c22250R_31_2 : rowsJ2 31 32 17 340 ≤ 17950381671833 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_128 c22250R_31_3 (by norm_num)

theorem c22250R_31_1 : rowsJ2 31 32 14 340 ≤ 19841184825282 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_127 c22250R_31_2 (by norm_num)

theorem c22250R_31_0 : rowsJ2 31 32 0 340 ≤ 20544213459365 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_126 c22250R_31_1 (by norm_num)

theorem hr22250R_31 : rows2 31 32 ≤ 20544213459365 := rows2_le_of_rowsJ2 31 32 c22250R_31_0

theorem c22250R_32_12 : rowsJ2 32 33 31 340 ≤ 1667121526365 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_151 rows22250R_152 (by norm_num)

theorem c22250R_32_11 : rowsJ2 32 33 30 340 ≤ 2507120161422 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_150 c22250R_32_12 (by norm_num)

theorem c22250R_32_10 : rowsJ2 32 33 29 340 ≤ 3395173885144 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_149 c22250R_32_11 (by norm_num)

theorem c22250R_32_9 : rowsJ2 32 33 28 340 ≤ 4345349425583 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_148 c22250R_32_10 (by norm_num)

theorem c22250R_32_8 : rowsJ2 32 33 27 340 ≤ 5378754662406 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_147 c22250R_32_9 (by norm_num)

theorem c22250R_32_7 : rowsJ2 32 33 26 340 ≤ 6499157096260 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_146 c22250R_32_8 (by norm_num)

theorem c22250R_32_6 : rowsJ2 32 33 25 340 ≤ 7701769271631 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_145 c22250R_32_7 (by norm_num)

theorem c22250R_32_5 : rowsJ2 32 33 23 340 ≤ 10302985230166 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_144 c22250R_32_6 (by norm_num)

theorem c22250R_32_4 : rowsJ2 32 33 21 340 ≤ 13044341530376 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_143 c22250R_32_5 (by norm_num)

theorem c22250R_32_3 : rowsJ2 32 33 19 340 ≤ 15661518492380 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_142 c22250R_32_4 (by norm_num)

theorem c22250R_32_2 : rowsJ2 32 33 17 340 ≤ 17899233360467 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_141 c22250R_32_3 (by norm_num)

theorem c22250R_32_1 : rowsJ2 32 33 14 340 ≤ 19878746815808 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_140 c22250R_32_2 (by norm_num)

theorem c22250R_32_0 : rowsJ2 32 33 0 340 ≤ 20582366498735 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_139 c22250R_32_1 (by norm_num)

theorem hr22250R_32 : rows2 32 33 ≤ 20582366498735 := rows2_le_of_rowsJ2 32 33 c22250R_32_0

theorem c22250R_33_13 : rowsJ2 33 34 32 340 ≤ 1683109004608 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_166 rows22250R_167 (by norm_num)

theorem c22250R_33_12 : rowsJ2 33 34 31 340 ≤ 2453780285419 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_165 c22250R_33_13 (by norm_num)

theorem c22250R_33_11 : rowsJ2 33 34 30 340 ≤ 3236830135243 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_164 c22250R_33_12 (by norm_num)

theorem c22250R_33_10 : rowsJ2 33 34 29 340 ≤ 4050918595393 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_163 c22250R_33_11 (by norm_num)

theorem c22250R_33_9 : rowsJ2 33 34 28 340 ≤ 4923937197607 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_162 c22250R_33_10 (by norm_num)

theorem c22250R_33_8 : rowsJ2 33 34 27 340 ≤ 5867142862410 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_161 c22250R_33_9 (by norm_num)

theorem c22250R_33_7 : rowsJ2 33 34 26 340 ≤ 6899461266680 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_160 c22250R_33_8 (by norm_num)

theorem c22250R_33_6 : rowsJ2 33 34 25 340 ≤ 8013435384975 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_159 c22250R_33_7 (by norm_num)

theorem c22250R_33_5 : rowsJ2 33 34 23 340 ≤ 10450928086560 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_158 c22250R_33_6 (by norm_num)

theorem c22250R_33_4 : rowsJ2 33 34 21 340 ≤ 13070002519457 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_157 c22250R_33_5 (by norm_num)

theorem c22250R_33_3 : rowsJ2 33 34 19 340 ≤ 15617222998527 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_156 c22250R_33_4 (by norm_num)

theorem c22250R_33_2 : rowsJ2 33 34 17 340 ≤ 17851430925857 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_155 c22250R_33_3 (by norm_num)

theorem c22250R_33_1 : rowsJ2 33 34 14 340 ≤ 19913944829691 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_154 c22250R_33_2 (by norm_num)

theorem c22250R_33_0 : rowsJ2 33 34 0 340 ≤ 20635327306374 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_153 c22250R_33_1 (by norm_num)

theorem hr22250R_33 : rows2 33 34 ≤ 20635327306374 := rows2_le_of_rowsJ2 33 34 c22250R_33_0

theorem c22250R_34_14 : rowsJ2 34 35 33 340 ≤ 1713933162717 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_182 rows22250R_183 (by norm_num)

theorem c22250R_34_13 : rowsJ2 34 35 32 340 ≤ 2479570794092 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_181 c22250R_34_14 (by norm_num)

theorem c22250R_34_12 : rowsJ2 34 35 31 340 ≤ 3208086281909 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_180 c22250R_34_13 (by norm_num)

theorem c22250R_34_11 : rowsJ2 34 35 30 340 ≤ 3932465423848 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_179 c22250R_34_12 (by norm_num)

theorem c22250R_34_10 : rowsJ2 34 35 29 340 ≤ 4685714497318 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_178 c22250R_34_11 (by norm_num)

theorem c22250R_34_9 : rowsJ2 34 35 28 340 ≤ 5481766937605 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_177 c22250R_34_10 (by norm_num)

theorem c22250R_34_8 : rowsJ2 34 35 27 340 ≤ 6347210204717 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_176 c22250R_34_9 (by norm_num)

theorem c22250R_34_7 : rowsJ2 34 35 26 340 ≤ 7288683511635 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_175 c22250R_34_8 (by norm_num)

theorem c22250R_34_6 : rowsJ2 34 35 25 340 ≤ 8317803424168 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_174 c22250R_34_7 (by norm_num)

theorem c22250R_34_5 : rowsJ2 34 35 23 340 ≤ 10592753432651 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_173 c22250R_34_6 (by norm_num)

theorem c22250R_34_4 : rowsJ2 34 35 21 340 ≤ 13077096996850 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_172 c22250R_34_5 (by norm_num)

theorem c22250R_34_3 : rowsJ2 34 35 19 340 ≤ 15550739231012 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_171 c22250R_34_4 (by norm_num)

theorem c22250R_34_2 : rowsJ2 34 35 17 340 ≤ 17765854595797 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_170 c22250R_34_3 (by norm_num)

theorem c22250R_34_1 : rowsJ2 34 35 14 340 ≤ 19908825857670 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_169 c22250R_34_2 (by norm_num)

theorem c22250R_34_0 : rowsJ2 34 35 0 340 ≤ 20668856474032 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_168 c22250R_34_1 (by norm_num)

theorem hr22250R_34 : rows2 34 35 ≤ 20668856474032 := rows2_le_of_rowsJ2 34 35 c22250R_34_0

theorem c22250R_35_15 : rowsJ2 35 36 34 340 ≤ 1631642781926 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_199 rows22250R_200 (by norm_num)

theorem c22250R_35_14 : rowsJ2 35 36 33 340 ≤ 2430460417642 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_198 c22250R_35_15 (by norm_num)

theorem c22250R_35_13 : rowsJ2 35 36 32 340 ≤ 3173987414966 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_197 c22250R_35_14 (by norm_num)

theorem c22250R_35_12 : rowsJ2 35 36 31 340 ≤ 3858235642563 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_196 c22250R_35_13 (by norm_num)

theorem c22250R_35_11 : rowsJ2 35 36 30 340 ≤ 4534806990567 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_195 c22250R_35_12 (by norm_num)

theorem c22250R_35_10 : rowsJ2 35 36 29 340 ≤ 5225512818412 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_194 c22250R_35_11 (by norm_num)

theorem c22250R_35_9 : rowsJ2 35 36 28 340 ≤ 5959412626688 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_193 c22250R_35_10 (by norm_num)

theorem c22250R_35_8 : rowsJ2 35 36 27 340 ≤ 6747263247768 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_192 c22250R_35_9 (by norm_num)

theorem c22250R_35_7 : rowsJ2 35 36 26 340 ≤ 7610275290093 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_191 c22250R_35_8 (by norm_num)

theorem c22250R_35_6 : rowsJ2 35 36 25 340 ≤ 8551737134467 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_190 c22250R_35_7 (by norm_num)

theorem c22250R_35_5 : rowsJ2 35 36 23 340 ≤ 10665150351358 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_189 c22250R_35_6 (by norm_num)

theorem c22250R_35_4 : rowsJ2 35 36 21 340 ≤ 13009000583530 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_188 c22250R_35_5 (by norm_num)

theorem c22250R_35_3 : rowsJ2 35 36 19 340 ≤ 15400796342926 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_187 c22250R_35_4 (by norm_num)

theorem c22250R_35_2 : rowsJ2 35 36 17 340 ≤ 17583487354235 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_186 c22250R_35_3 (by norm_num)

theorem c22250R_35_1 : rowsJ2 35 36 14 340 ≤ 19808151137694 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_185 c22250R_35_2 (by norm_num)

theorem c22250R_35_0 : rowsJ2 35 36 0 340 ≤ 20612844995763 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_184 c22250R_35_1 (by norm_num)

theorem hr22250R_35 : rows2 35 36 ≤ 20612844995763 := rows2_le_of_rowsJ2 35 36 c22250R_35_0

theorem c22250R_36_16 : rowsJ2 36 37 35 340 ≤ 1462305958522 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_217 rows22250R_218 (by norm_num)

theorem c22250R_36_15 : rowsJ2 36 37 34 340 ≤ 2230786829897 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_216 c22250R_36_16 (by norm_num)

theorem c22250R_36_14 : rowsJ2 36 37 33 340 ≤ 2986087452722 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_215 c22250R_36_15 (by norm_num)

theorem c22250R_36_13 : rowsJ2 36 37 32 340 ≤ 3702386290992 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_214 c22250R_36_14 (by norm_num)

theorem c22250R_36_12 : rowsJ2 36 37 31 340 ≤ 4355091788821 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_213 c22250R_36_13 (by norm_num)

theorem c22250R_36_11 : rowsJ2 36 37 30 340 ≤ 4981781861297 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_212 c22250R_36_12 (by norm_num)

theorem c22250R_36_10 : rowsJ2 36 37 29 340 ≤ 5620834373244 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_211 c22250R_36_11 (by norm_num)

theorem c22250R_36_9 : rowsJ2 36 37 28 340 ≤ 6290866151086 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_210 c22250R_36_10 (by norm_num)

theorem c22250R_36_8 : rowsJ2 36 37 27 340 ≤ 7013432403452 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_209 c22250R_36_9 (by norm_num)

theorem c22250R_36_7 : rowsJ2 36 37 26 340 ≤ 7798133906472 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_208 c22250R_36_8 (by norm_num)

theorem c22250R_36_6 : rowsJ2 36 37 25 340 ≤ 8660431795326 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_207 c22250R_36_7 (by norm_num)

theorem c22250R_36_5 : rowsJ2 36 37 23 340 ≤ 10613147187902 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_206 c22250R_36_6 (by norm_num)

theorem c22250R_36_4 : rowsJ2 36 37 21 340 ≤ 12810620668459 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_205 c22250R_36_5 (by norm_num)

theorem c22250R_36_3 : rowsJ2 36 37 19 340 ≤ 15112261050348 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_204 c22250R_36_4 (by norm_num)

theorem c22250R_36_2 : rowsJ2 36 37 17 340 ≤ 17249231444832 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_203 c22250R_36_3 (by norm_num)

theorem c22250R_36_1 : rowsJ2 36 37 14 340 ≤ 19546960217165 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_202 c22250R_36_2 (by norm_num)

theorem c22250R_36_0 : rowsJ2 36 37 0 340 ≤ 20412935079865 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_201 c22250R_36_1 (by norm_num)

theorem hr22250R_36 : rows2 36 37 ≤ 20412935079865 := rows2_le_of_rowsJ2 36 37 c22250R_36_0

theorem c22250R_37_16 : rowsJ2 37 38 36 340 ≤ 1237755552368 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_235 rows22250R_236 (by norm_num)

theorem c22250R_37_15 : rowsJ2 37 38 35 340 ≤ 1925627823704 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_234 c22250R_37_16 (by norm_num)

theorem c22250R_37_14 : rowsJ2 37 38 34 340 ≤ 2637843563117 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_233 c22250R_37_15 (by norm_num)

theorem c22250R_37_13 : rowsJ2 37 38 33 340 ≤ 3352600253237 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_232 c22250R_37_14 (by norm_num)

theorem c22250R_37_12 : rowsJ2 37 38 32 340 ≤ 4034144118852 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_231 c22250R_37_13 (by norm_num)

theorem c22250R_37_11 : rowsJ2 37 38 31 340 ≤ 4653033522430 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_230 c22250R_37_12 (by norm_num)

theorem c22250R_37_10 : rowsJ2 37 38 30 340 ≤ 5242614018736 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_229 c22250R_37_11 (by norm_num)

theorem c22250R_37_9 : rowsJ2 37 38 29 340 ≤ 5829767728060 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_228 c22250R_37_10 (by norm_num)

theorem c22250R_37_8 : rowsJ2 37 38 28 340 ≤ 6444112311369 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_227 c22250R_37_9 (by norm_num)

theorem c22250R_37_7 : rowsJ2 37 38 27 340 ≤ 7101360779325 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_226 c22250R_37_8 (by norm_num)

theorem c22250R_37_6 : rowsJ2 37 38 26 340 ≤ 7820061248213 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_225 c22250R_37_7 (by norm_num)

theorem c22250R_37_5 : rowsJ2 37 38 24 340 ≤ 9467358425624 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_224 c22250R_37_6 (by norm_num)

theorem c22250R_37_4 : rowsJ2 37 38 22 340 ≤ 11400931929716 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_223 c22250R_37_5 (by norm_num)

theorem c22250R_37_3 : rowsJ2 37 38 20 340 ≤ 13548208220947 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_222 c22250R_37_4 (by norm_num)

theorem c22250R_37_2 : rowsJ2 37 38 17 340 ≤ 16738450390020 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_221 c22250R_37_3 (by norm_num)

theorem c22250R_37_1 : rowsJ2 37 38 14 340 ≤ 19092587898644 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_220 c22250R_37_2 (by norm_num)

theorem c22250R_37_0 : rowsJ2 37 38 0 340 ≤ 20036978685494 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_219 c22250R_37_1 (by norm_num)

theorem hr22250R_37 : rows2 37 38 ≤ 20036978685494 := rows2_le_of_rowsJ2 37 38 c22250R_37_0

theorem c22250R_38_17 : rowsJ2 38 39 37 340 ≤ 908723694180 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_254 rows22250R_255 (by norm_num)

theorem c22250R_38_16 : rowsJ2 38 39 36 340 ≤ 1441560326230 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_253 c22250R_38_17 (by norm_num)

theorem c22250R_38_15 : rowsJ2 38 39 35 340 ≤ 2016676123934 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_252 c22250R_38_16 (by norm_num)

theorem c22250R_38_14 : rowsJ2 38 39 34 340 ≤ 2628949449553 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_251 c22250R_38_15 (by norm_num)

theorem c22250R_38_13 : rowsJ2 38 39 33 340 ≤ 3253418548057 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_250 c22250R_38_14 (by norm_num)

theorem c22250R_38_12 : rowsJ2 38 39 32 340 ≤ 3870140985592 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_249 c22250R_38_13 (by norm_num)

theorem c22250R_38_11 : rowsJ2 38 39 31 340 ≤ 4440573989709 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_248 c22250R_38_12 (by norm_num)

theorem c22250R_38_10 : rowsJ2 38 39 30 340 ≤ 4976200196538 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_247 c22250R_38_11 (by norm_num)

theorem c22250R_38_9 : rowsJ2 38 39 29 340 ≤ 5509571906561 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_246 c22250R_38_10 (by norm_num)

theorem c22250R_38_8 : rowsJ2 38 39 28 340 ≤ 6063999209645 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_245 c22250R_38_9 (by norm_num)

theorem c22250R_38_7 : rowsJ2 38 39 27 340 ≤ 6660947518345 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_244 c22250R_38_8 (by norm_num)

theorem c22250R_38_6 : rowsJ2 38 39 26 340 ≤ 7312820997144 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_243 c22250R_38_7 (by norm_num)

theorem c22250R_38_5 : rowsJ2 38 39 24 340 ≤ 8813543483119 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_242 c22250R_38_6 (by norm_num)

theorem c22250R_38_4 : rowsJ2 38 39 22 340 ≤ 10599047682755 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_241 c22250R_38_5 (by norm_num)

theorem c22250R_38_3 : rowsJ2 38 39 20 340 ≤ 12608768811628 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_240 c22250R_38_4 (by norm_num)

theorem c22250R_38_2 : rowsJ2 38 39 17 340 ≤ 15697436189694 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_239 c22250R_38_3 (by norm_num)

theorem c22250R_38_1 : rowsJ2 38 39 14 340 ≤ 18084426778250 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_238 c22250R_38_2 (by norm_num)

theorem c22250R_38_0 : rowsJ2 38 39 0 340 ≤ 19124040132171 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_237 c22250R_38_1 (by norm_num)

theorem hr22250R_38 : rows2 38 39 ≤ 19124040132171 := rows2_le_of_rowsJ2 38 39 c22250R_38_0

theorem c22250R_39_18 : rowsJ2 39 40 38 340 ≤ 611203358976 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_274 rows22250R_275 (by norm_num)

theorem c22250R_39_17 : rowsJ2 39 40 37 340 ≤ 987186656675 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_273 c22250R_39_18 (by norm_num)

theorem c22250R_39_16 : rowsJ2 39 40 36 340 ≤ 1411045705120 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_272 c22250R_39_17 (by norm_num)

theorem c22250R_39_15 : rowsJ2 39 40 35 340 ≤ 1880529955536 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_271 c22250R_39_16 (by norm_num)

theorem c22250R_39_14 : rowsJ2 39 40 34 340 ≤ 2390482640863 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_270 c22250R_39_15 (by norm_num)

theorem c22250R_39_13 : rowsJ2 39 40 33 340 ≤ 2925557530770 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_269 c22250R_39_14 (by norm_num)

theorem c22250R_39_12 : rowsJ2 39 40 32 340 ≤ 3468654002626 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_268 c22250R_39_13 (by norm_num)

theorem c22250R_39_11 : rowsJ2 39 40 31 340 ≤ 3991077504807 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_267 c22250R_39_12 (by norm_num)

theorem c22250R_39_10 : rowsJ2 39 40 30 340 ≤ 4479250019194 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_266 c22250R_39_11 (by norm_num)

theorem c22250R_39_9 : rowsJ2 39 40 29 340 ≤ 4959336684037 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_265 c22250R_39_10 (by norm_num)

theorem c22250R_39_8 : rowsJ2 39 40 28 340 ≤ 5460370027737 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_264 c22250R_39_9 (by norm_num)

theorem c22250R_39_7 : rowsJ2 39 40 27 340 ≤ 5997596237536 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_263 c22250R_39_8 (by norm_num)

theorem c22250R_39_6 : rowsJ2 39 40 26 340 ≤ 6589221472997 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_262 c22250R_39_7 (by norm_num)

theorem c22250R_39_5 : rowsJ2 39 40 25 340 ≤ 7238888644982 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_261 c22250R_39_6 (by norm_num)

theorem c22250R_39_4 : rowsJ2 39 40 23 340 ≤ 8741768155949 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_260 c22250R_39_5 (by norm_num)

theorem c22250R_39_3 : rowsJ2 39 40 20 340 ≤ 11470344036338 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_259 c22250R_39_4 (by norm_num)

theorem c22250R_39_2 : rowsJ2 39 40 17 340 ≤ 14438736404783 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_258 c22250R_39_3 (by norm_num)

theorem c22250R_39_1 : rowsJ2 39 40 14 340 ≤ 16839849379814 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_257 c22250R_39_2 (by norm_num)

theorem c22250R_39_0 : rowsJ2 39 40 0 340 ≤ 17985535191727 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_256 c22250R_39_1 (by norm_num)

theorem hr22250R_39 : rows2 39 40 ≤ 17985535191727 := rows2_le_of_rowsJ2 39 40 c22250R_39_0

theorem c22250R_40_19 : rowsJ2 40 41 39 340 ≤ 409612555176 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_295 rows22250R_296 (by norm_num)

theorem c22250R_40_18 : rowsJ2 40 41 38 340 ≤ 672433055147 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_294 c22250R_40_19 (by norm_num)

theorem c22250R_40_17 : rowsJ2 40 41 37 340 ≤ 973112781573 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_293 c22250R_40_18 (by norm_num)

theorem c22250R_40_16 : rowsJ2 40 41 36 340 ≤ 1321157348052 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_292 c22250R_40_17 (by norm_num)

theorem c22250R_40_15 : rowsJ2 40 41 35 340 ≤ 1709135074023 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_291 c22250R_40_16 (by norm_num)

theorem c22250R_40_14 : rowsJ2 40 41 34 340 ≤ 2140750262187 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_290 c22250R_40_15 (by norm_num)

theorem c22250R_40_13 : rowsJ2 40 41 33 340 ≤ 2599139338663 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_289 c22250R_40_14 (by norm_num)

theorem c22250R_40_12 : rowsJ2 40 41 32 340 ≤ 3077500423563 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_288 c22250R_40_13 (by norm_num)

theorem c22250R_40_11 : rowsJ2 40 41 31 340 ≤ 3546992092061 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_287 c22250R_40_12 (by norm_num)

theorem c22250R_40_10 : rowsJ2 40 41 30 340 ≤ 3988120913854 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_286 c22250R_40_11 (by norm_num)

theorem c22250R_40_9 : rowsJ2 40 41 29 340 ≤ 4421401267823 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_285 c22250R_40_10 (by norm_num)

theorem c22250R_40_8 : rowsJ2 40 41 28 340 ≤ 4869513054449 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_284 c22250R_40_9 (by norm_num)

theorem c22250R_40_7 : rowsJ2 40 41 27 340 ≤ 5353529551512 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_283 c22250R_40_8 (by norm_num)

theorem c22250R_40_6 : rowsJ2 40 41 26 340 ≤ 5885465619438 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_282 c22250R_40_7 (by norm_num)

theorem c22250R_40_5 : rowsJ2 40 41 25 340 ≤ 6474879335721 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_281 c22250R_40_6 (by norm_num)

theorem c22250R_40_4 : rowsJ2 40 41 23 340 ≤ 7843281195936 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_280 c22250R_40_5 (by norm_num)

theorem c22250R_40_3 : rowsJ2 40 41 20 340 ≤ 10368089449745 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_279 c22250R_40_4 (by norm_num)

theorem c22250R_40_2 : rowsJ2 40 41 17 340 ≤ 13203990624209 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_278 c22250R_40_3 (by norm_num)

theorem c22250R_40_1 : rowsJ2 40 41 14 340 ≤ 15593887570044 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_277 c22250R_40_2 (by norm_num)

theorem c22250R_40_0 : rowsJ2 40 41 0 340 ≤ 16863089041726 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_276 c22250R_40_1 (by norm_num)

theorem hr22250R_40 : rows2 40 41 ≤ 16863089041726 := rows2_le_of_rowsJ2 40 41 c22250R_40_0

theorem c22250R_41_19 : rowsJ2 41 42 40 340 ≤ 248652684276 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_316 rows22250R_317 (by norm_num)

theorem c22250R_41_18 : rowsJ2 41 42 39 340 ≤ 416148279790 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_315 c22250R_41_19 (by norm_num)

theorem c22250R_41_17 : rowsJ2 41 42 38 340 ≤ 617730384957 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_314 c22250R_41_18 (by norm_num)

theorem c22250R_41_16 : rowsJ2 41 42 37 340 ≤ 854465497418 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_313 c22250R_41_17 (by norm_num)

theorem c22250R_41_15 : rowsJ2 41 42 36 340 ≤ 1128332255673 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_312 c22250R_41_16 (by norm_num)

theorem c22250R_41_14 : rowsJ2 41 42 35 340 ≤ 1443959731844 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_311 c22250R_41_15 (by norm_num)

theorem c22250R_41_13 : rowsJ2 41 42 34 340 ≤ 1797532288304 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_310 c22250R_41_14 (by norm_num)

theorem c22250R_41_12 : rowsJ2 41 42 33 340 ≤ 2184769199496 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_309 c22250R_41_13 (by norm_num)

theorem c22250R_41_11 : rowsJ2 41 42 32 340 ≤ 2593666683423 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_308 c22250R_41_12 (by norm_num)

theorem c22250R_41_10 : rowsJ2 41 42 31 340 ≤ 3010679402238 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_307 c22250R_41_11 (by norm_num)

theorem c22250R_41_9 : rowsJ2 41 42 30 340 ≤ 3411221115576 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_306 c22250R_41_10 (by norm_num)

theorem c22250R_41_8 : rowsJ2 41 42 29 340 ≤ 3798076944987 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_305 c22250R_41_9 (by norm_num)

theorem c22250R_41_7 : rowsJ2 41 42 28 340 ≤ 4199733286773 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_304 c22250R_41_8 (by norm_num)

theorem c22250R_41_6 : rowsJ2 41 42 27 340 ≤ 4630992844292 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_303 c22250R_41_7 (by norm_num)

theorem c22250R_41_5 : rowsJ2 41 42 26 340 ≤ 5109746985409 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_302 c22250R_41_6 (by norm_num)

theorem c22250R_41_4 : rowsJ2 41 42 24 340 ≤ 6228966422673 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_301 c22250R_41_5 (by norm_num)

theorem c22250R_41_3 : rowsJ2 41 42 21 340 ≤ 8380314456935 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_300 c22250R_41_4 (by norm_num)

theorem c22250R_41_2 : rowsJ2 41 42 18 340 ≤ 10994245110953 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_299 c22250R_41_3 (by norm_num)

theorem c22250R_41_1 : rowsJ2 41 42 14 340 ≤ 14266063639660 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_298 c22250R_41_2 (by norm_num)

theorem c22250R_41_0 : rowsJ2 41 42 0 340 ≤ 15658182405522 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_297 c22250R_41_1 (by norm_num)

theorem hr22250R_41 : rows2 41 42 ≤ 15658182405522 := rows2_le_of_rowsJ2 41 42 c22250R_41_0

theorem c22250R_42_20 : rowsJ2 42 43 41 340 ≤ 128797483553 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_338 rows22250R_339 (by norm_num)

theorem c22250R_42_19 : rowsJ2 42 43 40 340 ≤ 223718574721 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_337 c22250R_42_20 (by norm_num)

theorem c22250R_42_18 : rowsJ2 42 43 39 340 ≤ 341479208378 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_336 c22250R_42_19 (by norm_num)

theorem c22250R_42_17 : rowsJ2 42 43 38 340 ≤ 488977055533 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_335 c22250R_42_18 (by norm_num)

theorem c22250R_42_16 : rowsJ2 42 43 37 340 ≤ 665576465118 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_334 c22250R_42_17 (by norm_num)

theorem c22250R_42_15 : rowsJ2 42 43 36 340 ≤ 876598528923 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_333 c22250R_42_16 (by norm_num)

theorem c22250R_42_14 : rowsJ2 42 43 35 340 ≤ 1121460188560 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_332 c22250R_42_15 (by norm_num)

theorem c22250R_42_13 : rowsJ2 42 43 34 340 ≤ 1406098356677 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_331 c22250R_42_14 (by norm_num)

theorem c22250R_42_12 : rowsJ2 42 43 33 340 ≤ 1722386843471 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_330 c22250R_42_13 (by norm_num)

theorem c22250R_42_11 : rowsJ2 42 43 32 340 ≤ 2067266627757 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_329 c22250R_42_12 (by norm_num)

theorem c22250R_42_10 : rowsJ2 42 43 31 340 ≤ 2426921987037 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_328 c22250R_42_11 (by norm_num)

theorem c22250R_42_9 : rowsJ2 42 43 30 340 ≤ 2787184071008 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_327 c22250R_42_10 (by norm_num)

theorem c22250R_42_8 : rowsJ2 42 43 29 340 ≤ 3134055597646 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_326 c22250R_42_9 (by norm_num)

theorem c22250R_42_7 : rowsJ2 42 43 28 340 ≤ 3489617128803 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_325 c22250R_42_8 (by norm_num)

theorem c22250R_42_6 : rowsJ2 42 43 27 340 ≤ 3874579837151 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_324 c22250R_42_7 (by norm_num)

theorem c22250R_42_5 : rowsJ2 42 43 26 340 ≤ 4300588878312 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_323 c22250R_42_6 (by norm_num)

theorem c22250R_42_4 : rowsJ2 42 43 24 340 ≤ 5306821326136 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_322 c22250R_42_5 (by norm_num)

theorem c22250R_42_3 : rowsJ2 42 43 21 340 ≤ 7270794560893 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_321 c22250R_42_4 (by norm_num)

theorem c22250R_42_2 : rowsJ2 42 43 18 340 ≤ 9704589276727 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_320 c22250R_42_3 (by norm_num)

theorem c22250R_42_1 : rowsJ2 42 43 14 340 ≤ 12897447560131 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_319 c22250R_42_2 (by norm_num)

theorem c22250R_42_0 : rowsJ2 42 43 0 340 ≤ 14411893870366 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_318 c22250R_42_1 (by norm_num)

theorem hr22250R_42 : rows2 42 43 ≤ 14411893870366 := rows2_le_of_rowsJ2 42 43 c22250R_42_0

theorem c22250R_43_21 : rowsJ2 43 44 42 340 ≤ 49850023261 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_361 rows22250R_362 (by norm_num)

theorem c22250R_43_20 : rowsJ2 43 44 41 340 ≤ 90587749262 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_360 c22250R_43_21 (by norm_num)

theorem c22250R_43_19 : rowsJ2 43 44 40 340 ≤ 147146986688 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_359 c22250R_43_20 (by norm_num)

theorem c22250R_43_18 : rowsJ2 43 44 39 340 ≤ 222229513536 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_358 c22250R_43_19 (by norm_num)

theorem c22250R_43_17 : rowsJ2 43 44 38 340 ≤ 320210409361 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_357 c22250R_43_18 (by norm_num)

theorem c22250R_43_16 : rowsJ2 43 44 37 340 ≤ 442993948356 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_356 c22250R_43_17 (by norm_num)

theorem c22250R_43_15 : rowsJ2 43 44 36 340 ≤ 594954119881 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_355 c22250R_43_16 (by norm_num)

theorem c22250R_43_14 : rowsJ2 43 44 35 340 ≤ 778070227467 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_354 c22250R_43_15 (by norm_num)

theorem c22250R_43_13 : rowsJ2 43 44 34 340 ≤ 995308736257 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_353 c22250R_43_14 (by norm_num)

theorem c22250R_43_12 : rowsJ2 43 44 33 340 ≤ 1246083125154 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_352 c22250R_43_13 (by norm_num)

theorem c22250R_43_11 : rowsJ2 43 44 32 340 ≤ 1527061419602 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_351 c22250R_43_12 (by norm_num)

theorem c22250R_43_10 : rowsJ2 43 44 31 340 ≤ 1829811987172 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_350 c22250R_43_11 (by norm_num)

theorem c22250R_43_9 : rowsJ2 43 44 30 340 ≤ 2144770257319 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_349 c22250R_43_10 (by norm_num)

theorem c22250R_43_8 : rowsJ2 43 44 29 340 ≤ 2451940294981 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_348 c22250R_43_9 (by norm_num)

theorem c22250R_43_7 : rowsJ2 43 44 28 340 ≤ 2767839515323 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_347 c22250R_43_8 (by norm_num)

theorem c22250R_43_6 : rowsJ2 43 44 27 340 ≤ 3106849357665 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_346 c22250R_43_7 (by norm_num)

theorem c22250R_43_5 : rowsJ2 43 44 26 340 ≤ 3486572798897 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_345 c22250R_43_6 (by norm_num)

theorem c22250R_43_4 : rowsJ2 43 44 24 340 ≤ 4386746905394 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_344 c22250R_43_5 (by norm_num)

theorem c22250R_43_3 : rowsJ2 43 44 21 340 ≤ 6167072935217 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_343 c22250R_43_4 (by norm_num)

theorem c22250R_43_2 : rowsJ2 43 44 18 340 ≤ 8432702968078 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_342 c22250R_43_3 (by norm_num)

theorem c22250R_43_1 : rowsJ2 43 44 14 340 ≤ 11528013370403 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_341 c22250R_43_2 (by norm_num)

theorem c22250R_43_0 : rowsJ2 43 44 0 340 ≤ 13153372501326 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_340 c22250R_43_1 (by norm_num)

theorem hr22250R_43 : rows2 43 44 ≤ 13153372501326 := rows2_le_of_rowsJ2 43 44 c22250R_43_0

theorem c22250R_44_22 : rowsJ2 44 45 43 340 ≤ 107390919685 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_385 rows22250R_386 (by norm_num)

theorem c22250R_44_21 : rowsJ2 44 45 42 340 ≤ 126334838920 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_384 c22250R_44_22 (by norm_num)

theorem c22250R_44_20 : rowsJ2 44 45 41 340 ≤ 152511268821 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_383 c22250R_44_21 (by norm_num)

theorem c22250R_44_19 : rowsJ2 44 45 40 340 ≤ 190133839308 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_382 c22250R_44_20 (by norm_num)

theorem c22250R_44_18 : rowsJ2 44 45 39 340 ≤ 242064337114 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_381 c22250R_44_19 (by norm_num)

theorem c22250R_44_17 : rowsJ2 44 45 38 340 ≤ 312548835774 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_380 c22250R_44_18 (by norm_num)

theorem c22250R_44_16 : rowsJ2 44 45 37 340 ≤ 403593949805 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_379 c22250R_44_17 (by norm_num)

theorem c22250R_44_15 : rowsJ2 44 45 36 340 ≤ 519491597270 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_378 c22250R_44_16 (by norm_num)

theorem c22250R_44_14 : rowsJ2 44 45 35 340 ≤ 662259776405 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_377 c22250R_44_15 (by norm_num)

theorem c22250R_44_13 : rowsJ2 44 45 34 340 ≤ 836256736371 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_376 c22250R_44_14 (by norm_num)

theorem c22250R_44_12 : rowsJ2 44 45 33 340 ≤ 1038442497999 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_375 c22250R_44_13 (by norm_num)

theorem c22250R_44_11 : rowsJ2 44 45 32 340 ≤ 1272109573584 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_374 c22250R_44_12 (by norm_num)

theorem c22250R_44_10 : rowsJ2 44 45 31 340 ≤ 1527663767996 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_373 c22250R_44_11 (by norm_num)

theorem c22250R_44_9 : rowsJ2 44 45 30 340 ≤ 1801202534420 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_372 c22250R_44_10 (by norm_num)

theorem c22250R_44_8 : rowsJ2 44 45 29 340 ≤ 2075095967585 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_371 c22250R_44_9 (by norm_num)

theorem c22250R_44_7 : rowsJ2 44 45 28 340 ≤ 2351597529888 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_370 c22250R_44_8 (by norm_num)

theorem c22250R_44_6 : rowsJ2 44 45 27 340 ≤ 2651085479687 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_369 c22250R_44_7 (by norm_num)

theorem c22250R_44_5 : rowsJ2 44 45 26 340 ≤ 2984854009111 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_368 c22250R_44_6 (by norm_num)

theorem c22250R_44_4 : rowsJ2 44 45 24 340 ≤ 3785840163913 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_367 c22250R_44_5 (by norm_num)

theorem c22250R_44_3 : rowsJ2 44 45 21 340 ≤ 5392136416170 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_366 c22250R_44_4 (by norm_num)

theorem c22250R_44_2 : rowsJ2 44 45 18 340 ≤ 7490493056886 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_365 c22250R_44_3 (by norm_num)

theorem c22250R_44_1 : rowsJ2 44 45 14 340 ≤ 10473771911845 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_364 c22250R_44_2 (by norm_num)

theorem c22250R_44_0 : rowsJ2 44 45 0 340 ≤ 12205514852689 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_363 c22250R_44_1 (by norm_num)

theorem hr22250R_44 : rows2 44 45 ≤ 12205514852689 := rows2_le_of_rowsJ2 44 45 c22250R_44_0

theorem c22250R_45_23 : rowsJ2 45 46 44 340 ≤ 407265647272 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_410 rows22250R_411 (by norm_num)

theorem c22250R_45_22 : rowsJ2 45 46 43 340 ≤ 417412746075 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_409 c22250R_45_23 (by norm_num)

theorem c22250R_45_21 : rowsJ2 45 46 42 340 ≤ 430437628016 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_408 c22250R_45_22 (by norm_num)

theorem c22250R_45_20 : rowsJ2 45 46 41 340 ≤ 446282988402 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_407 c22250R_45_21 (by norm_num)

theorem c22250R_45_19 : rowsJ2 45 46 40 340 ≤ 469375925577 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_406 c22250R_45_20 (by norm_num)

theorem c22250R_45_18 : rowsJ2 45 46 39 340 ≤ 502415236229 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_405 c22250R_45_19 (by norm_num)

theorem c22250R_45_17 : rowsJ2 45 46 38 340 ≤ 549789510536 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_404 c22250R_45_18 (by norm_num)

theorem c22250R_45_16 : rowsJ2 45 46 37 340 ≤ 613401371476 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_403 c22250R_45_17 (by norm_num)

theorem c22250R_45_15 : rowsJ2 45 46 36 340 ≤ 697618255321 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_402 c22250R_45_16 (by norm_num)

theorem c22250R_45_14 : rowsJ2 45 46 35 340 ≤ 804400925967 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_401 c22250R_45_15 (by norm_num)

theorem c22250R_45_13 : rowsJ2 45 46 34 340 ≤ 938119495072 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_400 c22250R_45_14 (by norm_num)

theorem c22250R_45_12 : rowsJ2 45 46 33 340 ≤ 1098604768017 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_399 c22250R_45_13 (by norm_num)

theorem c22250R_45_11 : rowsJ2 45 46 32 340 ≤ 1285230386015 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_398 c22250R_45_12 (by norm_num)

theorem c22250R_45_10 : rowsJ2 45 46 31 340 ≤ 1497784429454 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_397 c22250R_45_11 (by norm_num)

theorem c22250R_45_9 : rowsJ2 45 46 30 340 ≤ 1728467910768 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_396 c22250R_45_10 (by norm_num)

theorem c22250R_45_8 : rowsJ2 45 46 29 340 ≤ 1969283824439 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_395 c22250R_45_9 (by norm_num)

theorem c22250R_45_7 : rowsJ2 45 46 28 340 ≤ 2212809398444 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_394 c22250R_45_8 (by norm_num)

theorem c22250R_45_6 : rowsJ2 45 46 27 340 ≤ 2473026074759 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_393 c22250R_45_7 (by norm_num)

theorem c22250R_45_5 : rowsJ2 45 46 26 340 ≤ 2767274258967 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_392 c22250R_45_6 (by norm_num)

theorem c22250R_45_4 : rowsJ2 45 46 24 340 ≤ 3475858325788 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_391 c22250R_45_5 (by norm_num)

theorem c22250R_45_3 : rowsJ2 45 46 22 340 ≤ 4380449534160 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_390 c22250R_45_4 (by norm_num)

theorem c22250R_45_2 : rowsJ2 45 46 18 340 ≤ 6853381482633 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_389 c22250R_45_3 (by norm_num)

theorem c22250R_45_1 : rowsJ2 45 46 14 340 ≤ 9712286351388 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_388 c22250R_45_2 (by norm_num)

theorem c22250R_45_0 : rowsJ2 45 46 0 340 ≤ 11539069705274 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_387 c22250R_45_1 (by norm_num)

theorem hr22250R_45 : rows2 45 46 ≤ 11539069705274 := rows2_le_of_rowsJ2 45 46 c22250R_45_0

theorem c22250R_46_25 : rowsJ2 46 47 45 340 ≤ 1243647693554 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_437 rows22250R_438 (by norm_num)

theorem c22250R_46_24 : rowsJ2 46 47 44 340 ≤ 1327290151639 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_436 c22250R_46_25 (by norm_num)

theorem c22250R_46_23 : rowsJ2 46 47 43 340 ≤ 1333015670189 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_435 c22250R_46_24 (by norm_num)

theorem c22250R_46_22 : rowsJ2 46 47 42 340 ≤ 1341601002860 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_434 c22250R_46_23 (by norm_num)

theorem c22250R_46_21 : rowsJ2 46 47 41 340 ≤ 1351560054457 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_433 c22250R_46_22 (by norm_num)

theorem c22250R_46_20 : rowsJ2 46 47 40 340 ≤ 1364351919706 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_432 c22250R_46_21 (by norm_num)

theorem c22250R_46_19 : rowsJ2 46 47 39 340 ≤ 1382904670880 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_431 c22250R_46_20 (by norm_num)

theorem c22250R_46_18 : rowsJ2 46 47 38 340 ≤ 1411426580983 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_430 c22250R_46_19 (by norm_num)

theorem c22250R_46_17 : rowsJ2 46 47 37 340 ≤ 1451987458232 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_429 c22250R_46_18 (by norm_num)

theorem c22250R_46_16 : rowsJ2 46 47 36 340 ≤ 1508824309259 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_428 c22250R_46_17 (by norm_num)

theorem c22250R_46_15 : rowsJ2 46 47 35 340 ≤ 1583997866950 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_427 c22250R_46_16 (by norm_num)

theorem c22250R_46_14 : rowsJ2 46 47 34 340 ≤ 1681794631337 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_426 c22250R_46_15 (by norm_num)

theorem c22250R_46_13 : rowsJ2 46 47 33 340 ≤ 1803523451011 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_425 c22250R_46_14 (by norm_num)

theorem c22250R_46_12 : rowsJ2 46 47 32 340 ≤ 1949981613432 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_424 c22250R_46_13 (by norm_num)

theorem c22250R_46_11 : rowsJ2 46 47 31 340 ≤ 2119756913990 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_423 c22250R_46_12 (by norm_num)

theorem c22250R_46_10 : rowsJ2 46 47 30 340 ≤ 2311738805935 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_422 c22250R_46_11 (by norm_num)

theorem c22250R_46_9 : rowsJ2 46 47 29 340 ≤ 2517951802259 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_421 c22250R_46_10 (by norm_num)

theorem c22250R_46_8 : rowsJ2 46 47 28 340 ≤ 2728684960883 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_420 c22250R_46_9 (by norm_num)

theorem c22250R_46_7 : rowsJ2 46 47 27 340 ≤ 2956054658798 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_419 c22250R_46_8 (by norm_num)

theorem c22250R_46_6 : rowsJ2 46 47 26 340 ≤ 3211022150674 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_418 c22250R_46_7 (by norm_num)

theorem c22250R_46_5 : rowsJ2 46 47 25 340 ≤ 3502843635721 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_417 c22250R_46_6 (by norm_num)

theorem c22250R_46_4 : rowsJ2 46 47 24 340 ≤ 3833952331401 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_416 c22250R_46_5 (by norm_num)

theorem c22250R_46_3 : rowsJ2 46 47 22 340 ≤ 4638925748651 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_415 c22250R_46_4 (by norm_num)

theorem c22250R_46_2 : rowsJ2 46 47 19 340 ≤ 6253620213244 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_414 c22250R_46_3 (by norm_num)

theorem c22250R_46_1 : rowsJ2 46 47 15 340 ≤ 8959279530957 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_413 c22250R_46_2 (by norm_num)

theorem c22250R_46_0 : rowsJ2 46 47 0 340 ≤ 11535529685237 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_412 c22250R_46_1 (by norm_num)

theorem hr22250R_46 : rows2 46 47 ≤ 11535529685237 := rows2_le_of_rowsJ2 46 47 c22250R_46_0

theorem c22250R_47_26 : rowsJ2 47 48 46 340 ≤ 2743486131482 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_465 rows22250R_466 (by norm_num)

theorem c22250R_47_25 : rowsJ2 47 48 45 340 ≤ 3052164718861 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_464 c22250R_47_26 (by norm_num)

theorem c22250R_47_24 : rowsJ2 47 48 44 340 ≤ 3132021873756 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_463 c22250R_47_25 (by norm_num)

theorem c22250R_47_23 : rowsJ2 47 48 43 340 ≤ 3134800656913 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_462 c22250R_47_24 (by norm_num)

theorem c22250R_47_22 : rowsJ2 47 48 42 340 ≤ 3138980117644 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_461 c22250R_47_23 (by norm_num)

theorem c22250R_47_21 : rowsJ2 47 48 41 340 ≤ 3144531115916 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_460 c22250R_47_22 (by norm_num)

theorem c22250R_47_20 : rowsJ2 47 48 40 340 ≤ 3151466765868 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_459 c22250R_47_21 (by norm_num)

theorem c22250R_47_19 : rowsJ2 47 48 39 340 ≤ 3159760669637 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_458 c22250R_47_20 (by norm_num)

theorem c22250R_47_18 : rowsJ2 47 48 38 340 ≤ 3173833699147 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_457 c22250R_47_19 (by norm_num)

theorem c22250R_47_17 : rowsJ2 47 48 37 340 ≤ 3195599193104 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_456 c22250R_47_18 (by norm_num)

theorem c22250R_47_16 : rowsJ2 47 48 36 340 ≤ 3229435734278 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_455 c22250R_47_17 (by norm_num)

theorem c22250R_47_15 : rowsJ2 47 48 35 340 ≤ 3277297304681 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_454 c22250R_47_16 (by norm_num)

theorem c22250R_47_14 : rowsJ2 47 48 34 340 ≤ 3343544751774 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_453 c22250R_47_15 (by norm_num)

theorem c22250R_47_13 : rowsJ2 47 48 33 340 ≤ 3429434989455 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_452 c22250R_47_14 (by norm_num)

theorem c22250R_47_12 : rowsJ2 47 48 32 340 ≤ 3538651983041 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_451 c22250R_47_13 (by norm_num)

theorem c22250R_47_11 : rowsJ2 47 48 31 340 ≤ 3669794685607 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_450 c22250R_47_12 (by norm_num)

theorem c22250R_47_10 : rowsJ2 47 48 30 340 ≤ 3823249700600 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_449 c22250R_47_11 (by norm_num)

theorem c22250R_47_9 : rowsJ2 47 48 29 340 ≤ 3995053996383 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_448 c22250R_47_10 (by norm_num)

theorem c22250R_47_8 : rowsJ2 47 48 28 340 ≤ 4179427831800 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_447 c22250R_47_9 (by norm_num)

theorem c22250R_47_7 : rowsJ2 47 48 27 340 ≤ 4374122407365 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_446 c22250R_47_8 (by norm_num)

theorem c22250R_47_6 : rowsJ2 47 48 26 340 ≤ 4596240974869 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_445 c22250R_47_7 (by norm_num)

theorem c22250R_47_5 : rowsJ2 47 48 25 340 ≤ 4848729231289 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_444 c22250R_47_6 (by norm_num)

theorem c22250R_47_4 : rowsJ2 47 48 24 340 ≤ 5140197302227 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_443 c22250R_47_5 (by norm_num)

theorem c22250R_47_3 : rowsJ2 47 48 22 340 ≤ 5852335179836 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_442 c22250R_47_4 (by norm_num)

theorem c22250R_47_2 : rowsJ2 47 48 19 340 ≤ 7303468191923 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_441 c22250R_47_3 (by norm_num)

theorem c22250R_47_1 : rowsJ2 47 48 15 340 ≤ 9835789965565 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_440 c22250R_47_2 (by norm_num)

theorem c22250R_47_0 : rowsJ2 47 48 0 340 ≤ 12477111314181 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_439 c22250R_47_1 (by norm_num)

theorem hr22250R_47 : rows2 47 48 ≤ 12477111314181 := rows2_le_of_rowsJ2 47 48 c22250R_47_0

theorem c22250R_48_26 : rowsJ2 48 49 47 340 ≤ 4473284989516 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_493 rows22250R_494 (by norm_num)

theorem c22250R_48_25 : rowsJ2 48 49 46 340 ≤ 5382447121033 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_492 c22250R_48_26 (by norm_num)

theorem c22250R_48_24 : rowsJ2 48 49 45 340 ≤ 5687192636896 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_491 c22250R_48_25 (by norm_num)

theorem c22250R_48_23 : rowsJ2 48 49 44 340 ≤ 5765527206422 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_490 c22250R_48_24 (by norm_num)

theorem c22250R_48_22 : rowsJ2 48 49 43 340 ≤ 5766917189968 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_489 c22250R_48_23 (by norm_num)

theorem c22250R_48_21 : rowsJ2 48 49 42 340 ≤ 5769697615254 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_488 c22250R_48_22 (by norm_num)

theorem c22250R_48_20 : rowsJ2 48 49 41 340 ≤ 5773164029677 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_487 c22250R_48_21 (by norm_num)

theorem c22250R_48_19 : rowsJ2 48 49 40 340 ≤ 5778006100865 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_486 c22250R_48_20 (by norm_num)

theorem c22250R_48_18 : rowsJ2 48 49 39 340 ≤ 5783525766478 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_485 c22250R_48_19 (by norm_num)

theorem c22250R_48_17 : rowsJ2 48 49 38 340 ≤ 5790410108365 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_484 c22250R_48_18 (by norm_num)

theorem c22250R_48_16 : rowsJ2 48 49 37 340 ≤ 5802378141012 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_483 c22250R_48_17 (by norm_num)

theorem c22250R_48_15 : rowsJ2 48 49 36 340 ≤ 5822056039914 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_482 c22250R_48_16 (by norm_num)

theorem c22250R_48_14 : rowsJ2 48 49 35 340 ≤ 5853126682623 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_481 c22250R_48_15 (by norm_num)

theorem c22250R_48_13 : rowsJ2 48 49 34 340 ≤ 5898255631694 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_480 c22250R_48_14 (by norm_num)

theorem c22250R_48_12 : rowsJ2 48 49 33 340 ≤ 5960365197890 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_479 c22250R_48_13 (by norm_num)

theorem c22250R_48_11 : rowsJ2 48 49 32 340 ≤ 6042171817524 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_478 c22250R_48_12 (by norm_num)

theorem c22250R_48_10 : rowsJ2 48 49 31 340 ≤ 6144566112150 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_477 c22250R_48_11 (by norm_num)

theorem c22250R_48_9 : rowsJ2 48 49 30 340 ≤ 6268270253051 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_476 c22250R_48_10 (by norm_num)

theorem c22250R_48_8 : rowsJ2 48 49 29 340 ≤ 6409779667107 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_475 c22250R_48_9 (by norm_num)

theorem c22250R_48_7 : rowsJ2 48 49 28 340 ≤ 6567910923902 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_474 c22250R_48_8 (by norm_num)

theorem c22250R_48_6 : rowsJ2 48 49 27 340 ≤ 6736369966414 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_473 c22250R_48_7 (by norm_num)

theorem c22250R_48_5 : rowsJ2 48 49 26 340 ≤ 6925802561100 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_472 c22250R_48_6 (by norm_num)

theorem c22250R_48_4 : rowsJ2 48 49 25 340 ≤ 7145399656685 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_471 c22250R_48_5 (by norm_num)

theorem c22250R_48_3 : rowsJ2 48 49 23 340 ≤ 7689966578159 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_470 c22250R_48_4 (by norm_num)

theorem c22250R_48_2 : rowsJ2 48 49 20 340 ≤ 8834879841558 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_469 c22250R_48_3 (by norm_num)

theorem c22250R_48_1 : rowsJ2 48 49 15 340 ≤ 11675332430856 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_468 c22250R_48_2 (by norm_num)

theorem c22250R_48_0 : rowsJ2 48 49 0 340 ≤ 14364757222597 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_467 c22250R_48_1 (by norm_num)

theorem hr22250R_48 : rows2 48 49 ≤ 14364757222597 := rows2_le_of_rowsJ2 48 49 c22250R_48_0

theorem c22250R_49_27 : rowsJ2 49 50 48 340 ≤ 6251100153482 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_522 rows22250R_523 (by norm_num)

theorem c22250R_49_26 : rowsJ2 49 50 47 340 ≤ 8037754593808 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_521 c22250R_49_27 (by norm_num)

theorem c22250R_49_25 : rowsJ2 49 50 46 340 ≤ 8937449456653 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_520 c22250R_49_26 (by norm_num)

theorem c22250R_49_24 : rowsJ2 49 50 45 340 ≤ 9239021602689 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_519 c22250R_49_25 (by norm_num)

theorem c22250R_49_23 : rowsJ2 49 50 44 340 ≤ 9315855224522 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_518 c22250R_49_24 (by norm_num)

theorem c22250R_49_22 : rowsJ2 49 50 43 340 ≤ 9316548071275 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_517 c22250R_49_23 (by norm_num)

theorem c22250R_49_21 : rowsJ2 49 50 42 340 ≤ 9317939030254 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_516 c22250R_49_22 (by norm_num)

theorem c22250R_49_20 : rowsJ2 49 50 41 340 ≤ 9320013170264 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_515 c22250R_49_21 (by norm_num)

theorem c22250R_49_19 : rowsJ2 49 50 40 340 ≤ 9322776708627 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_514 c22250R_49_20 (by norm_num)

theorem c22250R_49_18 : rowsJ2 49 50 39 340 ≤ 9326216099229 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_513 c22250R_49_19 (by norm_num)

theorem c22250R_49_17 : rowsJ2 49 50 38 340 ≤ 9330338499293 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_512 c22250R_49_18 (by norm_num)

theorem c22250R_49_16 : rowsJ2 49 50 37 340 ≤ 9335131708978 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_511 c22250R_49_17 (by norm_num)

theorem c22250R_49_15 : rowsJ2 49 50 36 340 ≤ 9345021870150 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_510 c22250R_49_16 (by norm_num)

theorem c22250R_49_14 : rowsJ2 49 50 35 340 ≤ 9361943602685 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_509 c22250R_49_15 (by norm_num)

theorem c22250R_49_13 : rowsJ2 49 50 34 340 ≤ 9390286021401 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_508 c22250R_49_14 (by norm_num)

theorem c22250R_49_12 : rowsJ2 49 50 33 340 ≤ 9431287580987 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_507 c22250R_49_13 (by norm_num)

theorem c22250R_49_11 : rowsJ2 49 50 32 340 ≤ 9489317236378 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_506 c22250R_49_12 (by norm_num)

theorem c22250R_49_10 : rowsJ2 49 50 31 340 ≤ 9564992645349 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_505 c22250R_49_11 (by norm_num)

theorem c22250R_49_9 : rowsJ2 49 50 30 340 ≤ 9660639435473 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_504 c22250R_49_10 (by norm_num)

theorem c22250R_49_8 : rowsJ2 49 50 29 340 ≤ 9775024657276 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_503 c22250R_49_9 (by norm_num)

theorem c22250R_49_7 : rowsJ2 49 50 28 340 ≤ 9905499094523 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_502 c22250R_49_8 (by norm_num)

theorem c22250R_49_6 : rowsJ2 49 50 27 340 ≤ 10047829700032 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_501 c22250R_49_7 (by norm_num)

theorem c22250R_49_5 : rowsJ2 49 50 26 340 ≤ 10211027019265 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_500 c22250R_49_6 (by norm_num)

theorem c22250R_49_4 : rowsJ2 49 50 25 340 ≤ 10397887829546 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_499 c22250R_49_5 (by norm_num)

theorem c22250R_49_3 : rowsJ2 49 50 23 340 ≤ 10869955029059 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_498 c22250R_49_4 (by norm_num)

theorem c22250R_49_2 : rowsJ2 49 50 20 340 ≤ 11881590525294 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_497 c22250R_49_3 (by norm_num)

theorem c22250R_49_1 : rowsJ2 49 50 15 340 ≤ 14488822528005 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_496 c22250R_49_2 (by norm_num)

theorem c22250R_49_0 : rowsJ2 49 50 0 340 ≤ 17215007125548 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_495 c22250R_49_1 (by norm_num)

theorem hr22250R_49 : rows2 49 50 ≤ 17215007125548 := rows2_le_of_rowsJ2 49 50 c22250R_49_0

theorem c22250R_50_28 : rowsJ2 50 51 49 340 ≤ 8374814772565 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_552 rows22250R_553 (by norm_num)

theorem c22250R_50_27 : rowsJ2 50 51 48 340 ≤ 10987656213687 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_551 c22250R_50_28 (by norm_num)

theorem c22250R_50_26 : rowsJ2 50 51 47 340 ≤ 12755897638263 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_550 c22250R_50_27 (by norm_num)

theorem c22250R_50_25 : rowsJ2 50 51 46 340 ≤ 13646320369179 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_549 c22250R_50_26 (by norm_num)

theorem c22250R_50_24 : rowsJ2 50 51 45 340 ≤ 13944784554017 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_548 c22250R_50_25 (by norm_num)

theorem c22250R_50_23 : rowsJ2 50 51 44 340 ≤ 14020826339077 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_547 c22250R_50_24 (by norm_num)

theorem c22250R_50_22 : rowsJ2 50 51 43 340 ≤ 14020826339077 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_546 c22250R_50_23 (by norm_num)

theorem c22250R_50_21 : rowsJ2 50 51 42 340 ≤ 14021519747231 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_545 c22250R_50_22 (by norm_num)

theorem c22250R_50_20 : rowsJ2 50 51 41 340 ≤ 14022210724005 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_544 c22250R_50_21 (by norm_num)

theorem c22250R_50_19 : rowsJ2 50 51 40 340 ≤ 14023588158387 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_543 c22250R_50_20 (by norm_num)

theorem c22250R_50_18 : rowsJ2 50 51 39 340 ≤ 14024961562142 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_542 c22250R_50_19 (by norm_num)

theorem c22250R_50_17 : rowsJ2 50 51 38 340 ≤ 14027015982787 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_541 c22250R_50_18 (by norm_num)

theorem c22250R_50_16 : rowsJ2 50 51 37 340 ≤ 14029065581122 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_540 c22250R_50_17 (by norm_num)

theorem c22250R_50_15 : rowsJ2 50 51 36 340 ≤ 14031792242143 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_539 c22250R_50_16 (by norm_num)

theorem c22250R_50_14 : rowsJ2 50 51 35 340 ≤ 14038939898653 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_538 c22250R_50_15 (by norm_num)

theorem c22250R_50_13 : rowsJ2 50 51 34 340 ≤ 14053138483153 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_537 c22250R_50_14 (by norm_num)

theorem c22250R_50_12 : rowsJ2 50 51 33 340 ≤ 14077367273984 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_536 c22250R_50_13 (by norm_num)

theorem c22250R_50_11 : rowsJ2 50 51 32 340 ≤ 14114292276363 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_535 c22250R_50_12 (by norm_num)

theorem c22250R_50_10 : rowsJ2 50 51 31 340 ≤ 14166879217438 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_534 c22250R_50_11 (by norm_num)

theorem c22250R_50_9 : rowsJ2 50 51 30 340 ≤ 14236490947524 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_533 c22250R_50_10 (by norm_num)

theorem c22250R_50_8 : rowsJ2 50 51 29 340 ≤ 14325423536075 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_532 c22250R_50_9 (by norm_num)

theorem c22250R_50_7 : rowsJ2 50 51 28 340 ≤ 14431392928231 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_531 c22250R_50_8 (by norm_num)

theorem c22250R_50_6 : rowsJ2 50 51 27 340 ≤ 14551767974707 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_530 c22250R_50_7 (by norm_num)

theorem c22250R_50_5 : rowsJ2 50 51 26 340 ≤ 14688830052405 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_529 c22250R_50_6 (by norm_num)

theorem c22250R_50_4 : rowsJ2 50 51 25 340 ≤ 14849419108893 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_528 c22250R_50_5 (by norm_num)

theorem c22250R_50_3 : rowsJ2 50 51 23 340 ≤ 15255604469884 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_527 c22250R_50_4 (by norm_num)

theorem c22250R_50_2 : rowsJ2 50 51 20 340 ≤ 16140923888288 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_526 c22250R_50_3 (by norm_num)

theorem c22250R_50_1 : rowsJ2 50 51 15 340 ≤ 18519146416055 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_525 c22250R_50_2 (by norm_num)

theorem c22250R_50_0 : rowsJ2 50 51 0 340 ≤ 21266131940301 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_524 c22250R_50_1 (by norm_num)

theorem hr22250R_50 : rows2 50 51 ≤ 21266131940301 := rows2_le_of_rowsJ2 50 51 c22250R_50_0

theorem c22250R_51_29 : rowsJ2 51 52 50 340 ≤ 10978201930315 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_583 rows22250R_584 (by norm_num)

theorem c22250R_51_28 : rowsJ2 51 52 49 340 ≤ 14515581908237 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_582 c22250R_51_29 (by norm_num)

theorem c22250R_51_27 : rowsJ2 51 52 48 340 ≤ 17101770444814 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_581 c22250R_51_28 (by norm_num)

theorem c22250R_51_26 : rowsJ2 51 52 47 340 ≤ 18851974506249 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_580 c22250R_51_27 (by norm_num)

theorem c22250R_51_25 : rowsJ2 51 52 46 340 ≤ 19733314270370 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_579 c22250R_51_26 (by norm_num)

theorem c22250R_51_24 : rowsJ2 51 52 45 340 ≤ 20028733900991 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_578 c22250R_51_25 (by norm_num)

theorem c22250R_51_23 : rowsJ2 51 52 44 340 ≤ 20104000003912 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_577 c22250R_51_24 (by norm_num)

theorem c22250R_51_22 : rowsJ2 51 52 43 340 ≤ 20104000003912 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_576 c22250R_51_23 (by norm_num)

theorem c22250R_51_21 : rowsJ2 51 52 42 340 ≤ 20104000003912 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_575 c22250R_51_22 (by norm_num)

theorem c22250R_51_20 : rowsJ2 51 52 41 340 ≤ 20104000003912 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_574 c22250R_51_21 (by norm_num)

theorem c22250R_51_19 : rowsJ2 51 52 40 340 ≤ 20104000003912 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_573 c22250R_51_20 (by norm_num)

theorem c22250R_51_18 : rowsJ2 51 52 39 340 ≤ 20104000003912 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_572 c22250R_51_19 (by norm_num)

theorem c22250R_51_17 : rowsJ2 51 52 38 340 ≤ 20104000003912 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_571 c22250R_51_18 (by norm_num)

theorem c22250R_51_16 : rowsJ2 51 52 37 340 ≤ 20104000003912 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_570 c22250R_51_17 (by norm_num)

theorem c22250R_51_15 : rowsJ2 51 52 36 340 ≤ 20104000003912 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_569 c22250R_51_16 (by norm_num)

theorem c22250R_51_14 : rowsJ2 51 52 35 340 ≤ 20104000003912 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_568 c22250R_51_15 (by norm_num)

theorem c22250R_51_13 : rowsJ2 51 52 34 340 ≤ 20108434734132 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_567 c22250R_51_14 (by norm_num)

theorem c22250R_51_12 : rowsJ2 51 52 33 340 ≤ 20118534618589 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_566 c22250R_51_13 (by norm_num)

theorem c22250R_51_11 : rowsJ2 51 52 32 340 ≤ 20138694760478 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_565 c22250R_51_12 (by norm_num)

theorem c22250R_51_10 : rowsJ2 51 52 31 340 ≤ 20170187735022 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_564 c22250R_51_11 (by norm_num)

theorem c22250R_51_9 : rowsJ2 51 52 30 340 ≤ 20217393136473 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_563 c22250R_51_10 (by norm_num)

theorem c22250R_51_8 : rowsJ2 51 52 29 340 ≤ 20280968030076 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_562 c22250R_51_9 (by norm_num)

theorem c22250R_51_7 : rowsJ2 51 52 28 340 ≤ 20364083361243 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_561 c22250R_51_8 (by norm_num)

theorem c22250R_51_6 : rowsJ2 51 52 27 340 ≤ 20462568125003 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_560 c22250R_51_7 (by norm_num)

theorem c22250R_51_5 : rowsJ2 51 52 26 340 ≤ 20577674667285 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_559 c22250R_51_6 (by norm_num)

theorem c22250R_51_4 : rowsJ2 51 52 25 340 ≤ 20712085671726 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_558 c22250R_51_5 (by norm_num)

theorem c22250R_51_3 : rowsJ2 51 52 23 340 ≤ 21059010535716 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_557 c22250R_51_4 (by norm_num)

theorem c22250R_51_2 : rowsJ2 51 52 20 340 ≤ 21831208492528 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_556 c22250R_51_3 (by norm_num)

theorem c22250R_51_1 : rowsJ2 51 52 15 340 ≤ 23982286069634 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_555 c22250R_51_2 (by norm_num)

theorem c22250R_51_0 : rowsJ2 51 52 0 340 ≤ 26735433325355 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_554 c22250R_51_1 (by norm_num)

theorem hr22250R_51 : rows2 51 52 ≤ 26735433325355 := rows2_le_of_rowsJ2 51 52 c22250R_51_0

theorem c22250R_52_30 : rowsJ2 52 53 51 340 ≤ 13727552893957 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_615 rows22250R_616 (by norm_num)

theorem c22250R_52_29 : rowsJ2 52 53 50 340 ≤ 18431573943227 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_614 c22250R_52_30 (by norm_num)

theorem c22250R_52_28 : rowsJ2 52 53 49 340 ≤ 21933234408791 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_613 c22250R_52_29 (by norm_num)

theorem c22250R_52_27 : rowsJ2 52 53 48 340 ≤ 24493308308555 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_612 c22250R_52_28 (by norm_num)

theorem c22250R_52_26 : rowsJ2 52 53 47 340 ≤ 26225839279741 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_611 c22250R_52_27 (by norm_num)

theorem c22250R_52_25 : rowsJ2 52 53 46 340 ≤ 27098279511782 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_610 c22250R_52_26 (by norm_num)

theorem c22250R_52_24 : rowsJ2 52 53 45 340 ≤ 27390716074366 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_609 c22250R_52_25 (by norm_num)

theorem c22250R_52_23 : rowsJ2 52 53 44 340 ≤ 27465222160407 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_608 c22250R_52_24 (by norm_num)

theorem c22250R_52_22 : rowsJ2 52 53 43 340 ≤ 27465222160407 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_607 c22250R_52_23 (by norm_num)

theorem c22250R_52_21 : rowsJ2 52 53 42 340 ≤ 27465222160407 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_606 c22250R_52_22 (by norm_num)

theorem c22250R_52_20 : rowsJ2 52 53 41 340 ≤ 27465222160407 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_605 c22250R_52_21 (by norm_num)

theorem c22250R_52_19 : rowsJ2 52 53 40 340 ≤ 27465222160407 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_604 c22250R_52_20 (by norm_num)

theorem c22250R_52_18 : rowsJ2 52 53 39 340 ≤ 27465222160407 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_603 c22250R_52_19 (by norm_num)

theorem c22250R_52_17 : rowsJ2 52 53 38 340 ≤ 27465222160407 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_602 c22250R_52_18 (by norm_num)

theorem c22250R_52_16 : rowsJ2 52 53 37 340 ≤ 27465222160407 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_601 c22250R_52_17 (by norm_num)

theorem c22250R_52_15 : rowsJ2 52 53 36 340 ≤ 27465222160407 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_600 c22250R_52_16 (by norm_num)

theorem c22250R_52_14 : rowsJ2 52 53 35 340 ≤ 27465222160407 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_599 c22250R_52_15 (by norm_num)

theorem c22250R_52_13 : rowsJ2 52 53 34 340 ≤ 27465222160407 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_598 c22250R_52_14 (by norm_num)

theorem c22250R_52_12 : rowsJ2 52 53 33 340 ≤ 27469666962241 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_597 c22250R_52_13 (by norm_num)

theorem c22250R_52_11 : rowsJ2 52 53 32 340 ≤ 27479791364981 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_596 c22250R_52_12 (by norm_num)

theorem c22250R_52_10 : rowsJ2 52 53 31 340 ≤ 27500003683236 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_595 c22250R_52_11 (by norm_num)

theorem c22250R_52_9 : rowsJ2 52 53 30 340 ≤ 27531583350929 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_594 c22250R_52_10 (by norm_num)

theorem c22250R_52_8 : rowsJ2 52 53 29 340 ≤ 27578258082613 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_593 c22250R_52_9 (by norm_num)

theorem c22250R_52_7 : rowsJ2 52 53 28 340 ≤ 27641361660989 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_592 c22250R_52_8 (by norm_num)

theorem c22250R_52_6 : rowsJ2 52 53 27 340 ≤ 27720972656837 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_591 c22250R_52_7 (by norm_num)

theorem c22250R_52_5 : rowsJ2 52 53 26 340 ≤ 27814183093842 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_590 c22250R_52_6 (by norm_num)

theorem c22250R_52_4 : rowsJ2 52 53 25 340 ≤ 27926604523559 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_589 c22250R_52_5 (by norm_num)

theorem c22250R_52_3 : rowsJ2 52 53 23 340 ≤ 28220856565442 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_588 c22250R_52_4 (by norm_num)

theorem c22250R_52_2 : rowsJ2 52 53 20 340 ≤ 28886761181803 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_587 c22250R_52_3 (by norm_num)

theorem c22250R_52_1 : rowsJ2 52 53 15 340 ≤ 30818678554384 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_586 c22250R_52_2 (by norm_num)

theorem c22250R_52_0 : rowsJ2 52 53 0 340 ≤ 33561847015031 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_585 c22250R_52_1 (by norm_num)

theorem hr22250R_52 : rows2 52 53 ≤ 33561847015031 := rows2_le_of_rowsJ2 52 53 c22250R_52_0

theorem c22250R_53_32 : rowsJ2 53 54 52 340 ≤ 16455699761605 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_649 rows22250R_650 (by norm_num)

theorem c22250R_53_31 : rowsJ2 53 54 51 340 ≤ 22557412256960 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_648 c22250R_53_32 (by norm_num)

theorem c22250R_53_30 : rowsJ2 53 54 50 340 ≤ 27214408212624 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_647 c22250R_53_31 (by norm_num)

theorem c22250R_53_29 : rowsJ2 53 54 49 340 ≤ 30681063326504 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_646 c22250R_53_30 (by norm_num)

theorem c22250R_53_28 : rowsJ2 53 54 48 340 ≤ 33215544714349 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_645 c22250R_53_29 (by norm_num)

theorem c22250R_53_27 : rowsJ2 53 54 47 340 ≤ 34930755943501 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_644 c22250R_53_28 (by norm_num)

theorem c22250R_53_26 : rowsJ2 53 54 46 340 ≤ 35794474576906 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_643 c22250R_53_27 (by norm_num)

theorem c22250R_53_25 : rowsJ2 53 54 45 340 ≤ 36083987713642 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_642 c22250R_53_26 (by norm_num)

theorem c22250R_53_24 : rowsJ2 53 54 44 340 ≤ 36157748978256 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_641 c22250R_53_25 (by norm_num)

theorem c22250R_53_23 : rowsJ2 53 54 43 340 ≤ 36157748978256 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_640 c22250R_53_24 (by norm_num)

theorem c22250R_53_22 : rowsJ2 53 54 42 340 ≤ 36157748978256 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_639 c22250R_53_23 (by norm_num)

theorem c22250R_53_21 : rowsJ2 53 54 41 340 ≤ 36157748978256 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_638 c22250R_53_22 (by norm_num)

theorem c22250R_53_20 : rowsJ2 53 54 40 340 ≤ 36157748978256 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_637 c22250R_53_21 (by norm_num)

theorem c22250R_53_19 : rowsJ2 53 54 39 340 ≤ 36157748978256 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_636 c22250R_53_20 (by norm_num)

theorem c22250R_53_18 : rowsJ2 53 54 38 340 ≤ 36157748978256 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_635 c22250R_53_19 (by norm_num)

theorem c22250R_53_17 : rowsJ2 53 54 37 340 ≤ 36157748978256 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_634 c22250R_53_18 (by norm_num)

theorem c22250R_53_16 : rowsJ2 53 54 36 340 ≤ 36157748978256 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_633 c22250R_53_17 (by norm_num)

theorem c22250R_53_15 : rowsJ2 53 54 35 340 ≤ 36157748978256 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_632 c22250R_53_16 (by norm_num)

theorem c22250R_53_14 : rowsJ2 53 54 34 340 ≤ 36157748978256 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_631 c22250R_53_15 (by norm_num)

theorem c22250R_53_13 : rowsJ2 53 54 33 340 ≤ 36157748978256 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_630 c22250R_53_14 (by norm_num)

theorem c22250R_53_12 : rowsJ2 53 54 32 340 ≤ 36162205024561 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_629 c22250R_53_13 (by norm_num)

theorem c22250R_53_11 : rowsJ2 53 54 31 340 ≤ 36172356665322 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_628 c22250R_53_12 (by norm_num)

theorem c22250R_53_10 : rowsJ2 53 54 30 340 ≤ 36192626690407 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_627 c22250R_53_11 (by norm_num)

theorem c22250R_53_9 : rowsJ2 53 54 29 340 ≤ 36223639946723 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_626 c22250R_53_10 (by norm_num)

theorem c22250R_53_8 : rowsJ2 53 54 28 340 ≤ 36269802505140 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_625 c22250R_53_9 (by norm_num)

theorem c22250R_53_7 : rowsJ2 53 54 27 340 ≤ 36330580221462 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_624 c22250R_53_8 (by norm_num)

theorem c22250R_53_6 : rowsJ2 53 54 26 340 ≤ 36406115257459 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_623 c22250R_53_7 (by norm_num)

theorem c22250R_53_5 : rowsJ2 53 54 25 340 ≤ 36496601351772 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_622 c22250R_53_6 (by norm_num)

theorem c22250R_53_4 : rowsJ2 53 54 24 340 ≤ 36608230038564 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_621 c22250R_53_5 (by norm_num)

theorem c22250R_53_3 : rowsJ2 53 54 23 340 ≤ 36742462094576 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_620 c22250R_53_4 (by norm_num)

theorem c22250R_53_2 : rowsJ2 53 54 21 340 ≤ 37092378885888 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_619 c22250R_53_3 (by norm_num)

theorem c22250R_53_1 : rowsJ2 53 54 16 340 ≤ 38604777317042 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_618 c22250R_53_2 (by norm_num)

theorem c22250R_53_0 : rowsJ2 53 54 0 340 ≤ 41755300328569 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_617 c22250R_53_1 (by norm_num)

theorem hr22250R_53 : rows2 53 54 ≤ 41755300328569 := rows2_le_of_rowsJ2 53 54 c22250R_53_0

theorem c22250R_54_33 : rowsJ2 54 55 53 340 ≤ 19457799134803 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_684 rows22250R_685 (by norm_num)

theorem c22250R_54_32 : rowsJ2 54 55 52 340 ≤ 26872287067399 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_683 c22250R_54_33 (by norm_num)

theorem c22250R_54_31 : rowsJ2 54 55 51 340 ≤ 32913605789970 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_682 c22250R_54_32 (by norm_num)

theorem c22250R_54_30 : rowsJ2 54 55 50 340 ≤ 37524507545719 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_681 c22250R_54_31 (by norm_num)

theorem c22250R_54_29 : rowsJ2 54 55 49 340 ≤ 40956850262641 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_680 c22250R_54_30 (by norm_num)

theorem c22250R_54_28 : rowsJ2 54 55 48 340 ≤ 43466245759733 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_679 c22250R_54_29 (by norm_num)

theorem c22250R_54_27 : rowsJ2 54 55 47 340 ≤ 45164480102912 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_678 c22250R_54_28 (by norm_num)

theorem c22250R_54_26 : rowsJ2 54 55 46 340 ≤ 46019649787651 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_677 c22250R_54_27 (by norm_num)

theorem c22250R_54_25 : rowsJ2 54 55 45 340 ≤ 46306297369739 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_676 c22250R_54_26 (by norm_num)

theorem c22250R_54_24 : rowsJ2 54 55 44 340 ≤ 46379328557172 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_675 c22250R_54_25 (by norm_num)

theorem c22250R_54_23 : rowsJ2 54 55 43 340 ≤ 46379328557172 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_674 c22250R_54_24 (by norm_num)

theorem c22250R_54_22 : rowsJ2 54 55 42 340 ≤ 46379328557172 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_673 c22250R_54_23 (by norm_num)

theorem c22250R_54_21 : rowsJ2 54 55 41 340 ≤ 46379328557172 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_672 c22250R_54_22 (by norm_num)

theorem c22250R_54_20 : rowsJ2 54 55 40 340 ≤ 46379328557172 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_671 c22250R_54_21 (by norm_num)

theorem c22250R_54_19 : rowsJ2 54 55 39 340 ≤ 46379328557172 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_670 c22250R_54_20 (by norm_num)

theorem c22250R_54_18 : rowsJ2 54 55 38 340 ≤ 46379328557172 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_669 c22250R_54_19 (by norm_num)

theorem c22250R_54_17 : rowsJ2 54 55 37 340 ≤ 46379328557172 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_668 c22250R_54_18 (by norm_num)

theorem c22250R_54_16 : rowsJ2 54 55 36 340 ≤ 46379328557172 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_667 c22250R_54_17 (by norm_num)

theorem c22250R_54_15 : rowsJ2 54 55 35 340 ≤ 46379328557172 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_666 c22250R_54_16 (by norm_num)

theorem c22250R_54_14 : rowsJ2 54 55 34 340 ≤ 46379328557172 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_665 c22250R_54_15 (by norm_num)

theorem c22250R_54_13 : rowsJ2 54 55 33 340 ≤ 46379328557172 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_664 c22250R_54_14 (by norm_num)

theorem c22250R_54_12 : rowsJ2 54 55 32 340 ≤ 46379328557172 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_663 c22250R_54_13 (by norm_num)

theorem c22250R_54_11 : rowsJ2 54 55 31 340 ≤ 46383797038290 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_662 c22250R_54_12 (by norm_num)

theorem c22250R_54_10 : rowsJ2 54 55 30 340 ≤ 46393978679829 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_661 c22250R_54_11 (by norm_num)

theorem c22250R_54_9 : rowsJ2 54 55 29 340 ≤ 46413656675963 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_660 c22250R_54_10 (by norm_num)

theorem c22250R_54_8 : rowsJ2 54 55 28 340 ≤ 46444117336044 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_659 c22250R_54_9 (by norm_num)

theorem c22250R_54_7 : rowsJ2 54 55 27 340 ≤ 46489131223595 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_658 c22250R_54_8 (by norm_num)

theorem c22250R_54_6 : rowsJ2 54 55 26 340 ≤ 46547018916234 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_657 c22250R_54_7 (by norm_num)

theorem c22250R_54_5 : rowsJ2 54 55 25 340 ≤ 46619801377482 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_656 c22250R_54_6 (by norm_num)

theorem c22250R_54_4 : rowsJ2 54 55 24 340 ≤ 46709429600868 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_655 c22250R_54_5 (by norm_num)

theorem c22250R_54_3 : rowsJ2 54 55 23 340 ≤ 46821531591525 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_654 c22250R_54_4 (by norm_num)

theorem c22250R_54_2 : rowsJ2 54 55 21 340 ≤ 47118382055336 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_653 c22250R_54_3 (by norm_num)

theorem c22250R_54_1 : rowsJ2 54 55 16 340 ≤ 48435424856791 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_652 c22250R_54_2 (by norm_num)

theorem c22250R_54_0 : rowsJ2 54 55 0 340 ≤ 51505162288976 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_651 c22250R_54_1 (by norm_num)

theorem hr22250R_54 : rows2 54 55 ≤ 51505162288976 := rows2_le_of_rowsJ2 54 55 c22250R_54_0

theorem c22250R_55_34 : rowsJ2 55 56 54 340 ≤ 22682699063233 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_720 rows22250R_721 (by norm_num)

theorem c22250R_55_33 : rowsJ2 55 56 53 340 ≤ 31474019926670 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_719 c22250R_55_34 (by norm_num)

theorem c22250R_55_32 : rowsJ2 55 56 52 340 ≤ 38815839703280 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_718 c22250R_55_33 (by norm_num)

theorem c22250R_55_31 : rowsJ2 55 56 51 340 ≤ 44797948471592 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_717 c22250R_55_32 (by norm_num)

theorem c22250R_55_30 : rowsJ2 55 56 50 340 ≤ 49363659550508 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_716 c22250R_55_31 (by norm_num)

theorem c22250R_55_29 : rowsJ2 55 56 49 340 ≤ 52762362450594 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_715 c22250R_55_30 (by norm_num)

theorem c22250R_55_28 : rowsJ2 55 56 48 340 ≤ 55247163782170 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_714 c22250R_55_29 (by norm_num)

theorem c22250R_55_27 : rowsJ2 55 56 47 340 ≤ 56928754014623 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_713 c22250R_55_28 (by norm_num)

theorem c22250R_55_26 : rowsJ2 55 56 46 340 ≤ 57775542324327 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_712 c22250R_55_27 (by norm_num)

theorem c22250R_55_25 : rowsJ2 55 56 45 340 ≤ 58059380521411 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_711 c22250R_55_26 (by norm_num)

theorem c22250R_55_24 : rowsJ2 55 56 44 340 ≤ 58131695942392 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_710 c22250R_55_25 (by norm_num)

theorem c22250R_55_23 : rowsJ2 55 56 43 340 ≤ 58131695942392 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_709 c22250R_55_24 (by norm_num)

theorem c22250R_55_22 : rowsJ2 55 56 42 340 ≤ 58131695942392 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_708 c22250R_55_23 (by norm_num)

theorem c22250R_55_21 : rowsJ2 55 56 41 340 ≤ 58131695942392 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_707 c22250R_55_22 (by norm_num)

theorem c22250R_55_20 : rowsJ2 55 56 40 340 ≤ 58131695942392 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_706 c22250R_55_21 (by norm_num)

theorem c22250R_55_19 : rowsJ2 55 56 39 340 ≤ 58131695942392 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_705 c22250R_55_20 (by norm_num)

theorem c22250R_55_18 : rowsJ2 55 56 38 340 ≤ 58131695942392 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_704 c22250R_55_19 (by norm_num)

theorem c22250R_55_17 : rowsJ2 55 56 37 340 ≤ 58131695942392 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_703 c22250R_55_18 (by norm_num)

theorem c22250R_55_16 : rowsJ2 55 56 36 340 ≤ 58131695942392 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_702 c22250R_55_17 (by norm_num)

theorem c22250R_55_15 : rowsJ2 55 56 35 340 ≤ 58131695942392 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_701 c22250R_55_16 (by norm_num)

theorem c22250R_55_14 : rowsJ2 55 56 34 340 ≤ 58131695942392 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_700 c22250R_55_15 (by norm_num)

theorem c22250R_55_13 : rowsJ2 55 56 33 340 ≤ 58131695942392 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_699 c22250R_55_14 (by norm_num)

theorem c22250R_55_12 : rowsJ2 55 56 32 340 ≤ 58131695942392 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_698 c22250R_55_13 (by norm_num)

theorem c22250R_55_11 : rowsJ2 55 56 31 340 ≤ 58131695942392 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_697 c22250R_55_12 (by norm_num)

theorem c22250R_55_10 : rowsJ2 55 56 30 340 ≤ 58136178068152 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_696 c22250R_55_11 (by norm_num)

theorem c22250R_55_9 : rowsJ2 55 56 29 340 ≤ 58145743585225 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_695 c22250R_55_10 (by norm_num)

theorem c22250R_55_8 : rowsJ2 55 56 28 340 ≤ 58164839955608 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_694 c22250R_55_9 (by norm_num)

theorem c22250R_55_7 : rowsJ2 55 56 27 340 ≤ 58194113188759 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_693 c22250R_55_8 (by norm_num)

theorem c22250R_55_6 : rowsJ2 55 56 26 340 ≤ 58237422768407 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_692 c22250R_55_7 (by norm_num)

theorem c22250R_55_5 : rowsJ2 55 56 25 340 ≤ 58292525508448 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_691 c22250R_55_6 (by norm_num)

theorem c22250R_55_4 : rowsJ2 55 56 24 340 ≤ 58364397710605 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_690 c22250R_55_5 (by norm_num)

theorem c22250R_55_3 : rowsJ2 55 56 23 340 ≤ 58454414774964 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_689 c22250R_55_4 (by norm_num)

theorem c22250R_55_2 : rowsJ2 55 56 21 340 ≤ 58702495736523 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_688 c22250R_55_3 (by norm_num)

theorem c22250R_55_1 : rowsJ2 55 56 16 340 ≤ 59844223327098 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_687 c22250R_55_2 (by norm_num)

theorem c22250R_55_0 : rowsJ2 55 56 0 340 ≤ 62817455468496 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_686 c22250R_55_1 (by norm_num)

theorem hr22250R_55 : rows2 55 56 ≤ 62817455468496 := rows2_le_of_rowsJ2 55 56 c22250R_55_0

theorem c22250R_56_34 : rowsJ2 56 57 55 340 ≤ 25418340372712 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_756 rows22250R_757 (by norm_num)

theorem c22250R_56_33 : rowsJ2 56 57 54 340 ≤ 35745241833884 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_755 c22250R_56_34 (by norm_num)

theorem c22250R_56_32 : rowsJ2 56 57 53 340 ≤ 44451236697930 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_754 c22250R_56_33 (by norm_num)

theorem c22250R_56_31 : rowsJ2 56 57 52 340 ≤ 51721798910447 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_753 c22250R_56_32 (by norm_num)

theorem c22250R_56_30 : rowsJ2 56 57 51 340 ≤ 57645847073641 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_752 c22250R_56_31 (by norm_num)

theorem c22250R_56_29 : rowsJ2 56 57 50 340 ≤ 62167244690810 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_751 c22250R_56_30 (by norm_num)

theorem c22250R_56_28 : rowsJ2 56 57 49 340 ≤ 65532960770589 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_750 c22250R_56_29 (by norm_num)

theorem c22250R_56_27 : rowsJ2 56 57 48 340 ≤ 67993645344262 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_749 c22250R_56_28 (by norm_num)

theorem c22250R_56_26 : rowsJ2 56 57 47 340 ≤ 69658914551764 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_748 c22250R_56_27 (by norm_num)

theorem c22250R_56_25 : rowsJ2 56 57 46 340 ≤ 70497484180802 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_747 c22250R_56_26 (by norm_num)

theorem c22250R_56_24 : rowsJ2 56 57 45 340 ≤ 70778567527027 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_746 c22250R_56_25 (by norm_num)

theorem c22250R_56_23 : rowsJ2 56 57 44 340 ≤ 70850181075597 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_745 c22250R_56_24 (by norm_num)

theorem c22250R_56_22 : rowsJ2 56 57 43 340 ≤ 70850181075597 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_744 c22250R_56_23 (by norm_num)

theorem c22250R_56_21 : rowsJ2 56 57 42 340 ≤ 70850181075597 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_743 c22250R_56_22 (by norm_num)

theorem c22250R_56_20 : rowsJ2 56 57 41 340 ≤ 70850181075597 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_742 c22250R_56_21 (by norm_num)

theorem c22250R_56_19 : rowsJ2 56 57 40 340 ≤ 70850181075597 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_741 c22250R_56_20 (by norm_num)

theorem c22250R_56_18 : rowsJ2 56 57 39 340 ≤ 70850181075597 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_740 c22250R_56_19 (by norm_num)

theorem c22250R_56_17 : rowsJ2 56 57 38 340 ≤ 70850181075597 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_739 c22250R_56_18 (by norm_num)

theorem c22250R_56_16 : rowsJ2 56 57 37 340 ≤ 70850181075597 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_738 c22250R_56_17 (by norm_num)

theorem c22250R_56_15 : rowsJ2 56 57 36 340 ≤ 70850181075597 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_737 c22250R_56_16 (by norm_num)

theorem c22250R_56_14 : rowsJ2 56 57 35 340 ≤ 70850181075597 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_736 c22250R_56_15 (by norm_num)

theorem c22250R_56_13 : rowsJ2 56 57 34 340 ≤ 70850181075597 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_735 c22250R_56_14 (by norm_num)

theorem c22250R_56_12 : rowsJ2 56 57 33 340 ≤ 70850181075597 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_734 c22250R_56_13 (by norm_num)

theorem c22250R_56_11 : rowsJ2 56 57 32 340 ≤ 70850181075597 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_733 c22250R_56_12 (by norm_num)

theorem c22250R_56_10 : rowsJ2 56 57 31 340 ≤ 70850181075597 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_732 c22250R_56_11 (by norm_num)

theorem c22250R_56_9 : rowsJ2 56 57 30 340 ≤ 70850181075597 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_731 c22250R_56_10 (by norm_num)

theorem c22250R_56_8 : rowsJ2 56 57 29 340 ≤ 70854678077399 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_730 c22250R_56_9 (by norm_num)

theorem c22250R_56_7 : rowsJ2 56 57 28 340 ≤ 70864277002595 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_729 c22250R_56_8 (by norm_num)

theorem c22250R_56_6 : rowsJ2 56 57 27 340 ≤ 70883443472615 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_728 c22250R_56_7 (by norm_num)

theorem c22250R_56_5 : rowsJ2 56 57 26 340 ≤ 70912829524670 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_727 c22250R_56_6 (by norm_num)

theorem c22250R_56_4 : rowsJ2 56 57 25 340 ≤ 70954543179233 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_726 c22250R_56_5 (by norm_num)

theorem c22250R_56_3 : rowsJ2 56 57 24 340 ≤ 71008679552247 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_725 c22250R_56_4 (by norm_num)

theorem c22250R_56_2 : rowsJ2 56 57 22 340 ≤ 71171305213919 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_724 c22250R_56_3 (by norm_num)

theorem c22250R_56_1 : rowsJ2 56 57 17 340 ≤ 72002430755983 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_723 c22250R_56_2 (by norm_num)

theorem c22250R_56_0 : rowsJ2 56 57 0 340 ≤ 75126932878028 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_722 c22250R_56_1 (by norm_num)

theorem hr22250R_56 : rows2 56 57 ≤ 75126932878028 := rows2_le_of_rowsJ2 56 57 c22250R_56_0

theorem c22250R_57_36 : rowsJ2 57 58 56 340 ≤ 27411481879561 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_794 rows22250R_795 (by norm_num)

theorem c22250R_57_35 : rowsJ2 57 58 55 340 ≤ 39144260337981 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_793 c22250R_57_36 (by norm_num)

theorem c22250R_57_34 : rowsJ2 57 58 54 340 ≤ 49324210419676 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_792 c22250R_57_35 (by norm_num)

theorem c22250R_57_33 : rowsJ2 57 58 53 340 ≤ 57946519661892 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_791 c22250R_57_34 (by norm_num)

theorem c22250R_57_32 : rowsJ2 57 58 52 340 ≤ 65147194224662 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_790 c22250R_57_33 (by norm_num)

theorem c22250R_57_31 : rowsJ2 57 58 51 340 ≤ 71014297987814 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_789 c22250R_57_32 (by norm_num)

theorem c22250R_57_30 : rowsJ2 57 58 50 340 ≤ 75492234061872 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_788 c22250R_57_31 (by norm_num)

theorem c22250R_57_29 : rowsJ2 57 58 49 340 ≤ 78825597487251 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_787 c22250R_57_30 (by norm_num)

theorem c22250R_57_28 : rowsJ2 57 58 48 340 ≤ 81262628943518 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_786 c22250R_57_29 (by norm_num)

theorem c22250R_57_27 : rowsJ2 57 58 47 340 ≤ 82911890894950 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_785 c22250R_57_28 (by norm_num)

theorem c22250R_57_26 : rowsJ2 57 58 46 340 ≤ 83742399846036 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_784 c22250R_57_27 (by norm_num)

theorem c22250R_57_25 : rowsJ2 57 58 45 340 ≤ 84020781302933 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_783 c22250R_57_26 (by norm_num)

theorem c22250R_57_24 : rowsJ2 57 58 44 340 ≤ 84091706472469 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_782 c22250R_57_25 (by norm_num)

theorem c22250R_57_23 : rowsJ2 57 58 43 340 ≤ 84091706472469 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_781 c22250R_57_24 (by norm_num)

theorem c22250R_57_22 : rowsJ2 57 58 42 340 ≤ 84091706472469 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_780 c22250R_57_23 (by norm_num)

theorem c22250R_57_21 : rowsJ2 57 58 41 340 ≤ 84091706472469 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_779 c22250R_57_22 (by norm_num)

theorem c22250R_57_20 : rowsJ2 57 58 40 340 ≤ 84091706472469 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_778 c22250R_57_21 (by norm_num)

theorem c22250R_57_19 : rowsJ2 57 58 39 340 ≤ 84091706472469 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_777 c22250R_57_20 (by norm_num)

theorem c22250R_57_18 : rowsJ2 57 58 38 340 ≤ 84091706472469 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_776 c22250R_57_19 (by norm_num)

theorem c22250R_57_17 : rowsJ2 57 58 37 340 ≤ 84091706472469 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_775 c22250R_57_18 (by norm_num)

theorem c22250R_57_16 : rowsJ2 57 58 36 340 ≤ 84091706472469 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_774 c22250R_57_17 (by norm_num)

theorem c22250R_57_15 : rowsJ2 57 58 35 340 ≤ 84091706472469 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_773 c22250R_57_16 (by norm_num)

theorem c22250R_57_14 : rowsJ2 57 58 34 340 ≤ 84091706472469 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_772 c22250R_57_15 (by norm_num)

theorem c22250R_57_13 : rowsJ2 57 58 33 340 ≤ 84091706472469 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_771 c22250R_57_14 (by norm_num)

theorem c22250R_57_12 : rowsJ2 57 58 32 340 ≤ 84091706472469 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_770 c22250R_57_13 (by norm_num)

theorem c22250R_57_11 : rowsJ2 57 58 31 340 ≤ 84091706472469 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_769 c22250R_57_12 (by norm_num)

theorem c22250R_57_10 : rowsJ2 57 58 30 340 ≤ 84091706472469 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_768 c22250R_57_11 (by norm_num)

theorem c22250R_57_9 : rowsJ2 57 58 29 340 ≤ 84091706472469 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_767 c22250R_57_10 (by norm_num)

theorem c22250R_57_8 : rowsJ2 57 58 28 340 ≤ 84096219605451 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_766 c22250R_57_9 (by norm_num)

theorem c22250R_57_7 : rowsJ2 57 58 27 340 ≤ 84105854674356 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_765 c22250R_57_8 (by norm_num)

theorem c22250R_57_6 : rowsJ2 57 58 26 340 ≤ 84125096824489 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_764 c22250R_57_7 (by norm_num)

theorem c22250R_57_5 : rowsJ2 57 58 25 340 ≤ 84153424282090 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_763 c22250R_57_6 (by norm_num)

theorem c22250R_57_4 : rowsJ2 57 58 24 340 ≤ 84194130335489 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_762 c22250R_57_5 (by norm_num)

theorem c22250R_57_3 : rowsJ2 57 58 23 340 ≤ 84248511918457 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_761 c22250R_57_4 (by norm_num)

theorem c22250R_57_2 : rowsJ2 57 58 21 340 ≤ 84411926577314 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_760 c22250R_57_3 (by norm_num)

theorem c22250R_57_1 : rowsJ2 57 58 17 340 ≤ 85019889821751 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_759 c22250R_57_2 (by norm_num)

theorem c22250R_57_0 : rowsJ2 57 58 0 340 ≤ 87984289323497 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_758 c22250R_57_1 (by norm_num)

theorem hr22250R_57 : rows2 57 58 ≤ 87984289323497 := rows2_le_of_rowsJ2 57 58 c22250R_57_0

theorem c22250R_58_37 : rowsJ2 58 59 57 340 ≤ 28954002072375 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_833 rows22250R_834 (by norm_num)

theorem c22250R_58_36 : rowsJ2 58 59 56 340 ≤ 41683905966919 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_832 c22250R_58_37 (by norm_num)

theorem c22250R_58_35 : rowsJ2 58 59 55 340 ≤ 53158870297823 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_831 c22250R_58_36 (by norm_num)

theorem c22250R_58_34 : rowsJ2 58 59 54 340 ≤ 63146005463278 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_830 c22250R_58_35 (by norm_num)

theorem c22250R_58_33 : rowsJ2 58 59 53 340 ≤ 71686222607639 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_829 c22250R_58_34 (by norm_num)

theorem c22250R_58_32 : rowsJ2 58 59 52 340 ≤ 78818340306563 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_828 c22250R_58_33 (by norm_num)

theorem c22250R_58_31 : rowsJ2 58 59 51 340 ≤ 84629583992942 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_827 c22250R_58_32 (by norm_num)

theorem c22250R_58_30 : rowsJ2 58 59 50 340 ≤ 89064886109430 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_826 c22250R_58_31 (by norm_num)

theorem c22250R_58_29 : rowsJ2 58 59 49 340 ≤ 92366512932841 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_825 c22250R_58_30 (by norm_num)

theorem c22250R_58_28 : rowsJ2 58 59 48 340 ≤ 94780341669377 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_824 c22250R_58_29 (by norm_num)

theorem c22250R_58_27 : rowsJ2 58 59 47 340 ≤ 96413901171535 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_823 c22250R_58_28 (by norm_num)

theorem c22250R_58_26 : rowsJ2 58 59 46 340 ≤ 97236502934399 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_822 c22250R_58_27 (by norm_num)

theorem c22250R_58_25 : rowsJ2 58 59 45 340 ≤ 97512233950775 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_821 c22250R_58_26 (by norm_num)

theorem c22250R_58_24 : rowsJ2 58 59 44 340 ≤ 97582483849244 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_820 c22250R_58_25 (by norm_num)

theorem c22250R_58_23 : rowsJ2 58 59 43 340 ≤ 97582483849244 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_819 c22250R_58_24 (by norm_num)

theorem c22250R_58_22 : rowsJ2 58 59 42 340 ≤ 97582483849244 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_818 c22250R_58_23 (by norm_num)

theorem c22250R_58_21 : rowsJ2 58 59 41 340 ≤ 97582483849244 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_817 c22250R_58_22 (by norm_num)

theorem c22250R_58_20 : rowsJ2 58 59 40 340 ≤ 97582483849244 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_816 c22250R_58_21 (by norm_num)

theorem c22250R_58_19 : rowsJ2 58 59 39 340 ≤ 97582483849244 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_815 c22250R_58_20 (by norm_num)

theorem c22250R_58_18 : rowsJ2 58 59 38 340 ≤ 97582483849244 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_814 c22250R_58_19 (by norm_num)

theorem c22250R_58_17 : rowsJ2 58 59 37 340 ≤ 97582483849244 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_813 c22250R_58_18 (by norm_num)

theorem c22250R_58_16 : rowsJ2 58 59 36 340 ≤ 97582483849244 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_812 c22250R_58_17 (by norm_num)

theorem c22250R_58_15 : rowsJ2 58 59 35 340 ≤ 97582483849244 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_811 c22250R_58_16 (by norm_num)

theorem c22250R_58_14 : rowsJ2 58 59 34 340 ≤ 97582483849244 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_810 c22250R_58_15 (by norm_num)

theorem c22250R_58_13 : rowsJ2 58 59 33 340 ≤ 97582483849244 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_809 c22250R_58_14 (by norm_num)

theorem c22250R_58_12 : rowsJ2 58 59 32 340 ≤ 97582483849244 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_808 c22250R_58_13 (by norm_num)

theorem c22250R_58_11 : rowsJ2 58 59 31 340 ≤ 97582483849244 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_807 c22250R_58_12 (by norm_num)

theorem c22250R_58_10 : rowsJ2 58 59 30 340 ≤ 97582483849244 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_806 c22250R_58_11 (by norm_num)

theorem c22250R_58_9 : rowsJ2 58 59 29 340 ≤ 97582483849244 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_805 c22250R_58_10 (by norm_num)

theorem c22250R_58_8 : rowsJ2 58 59 28 340 ≤ 97582483849244 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_804 c22250R_58_9 (by norm_num)

theorem c22250R_58_7 : rowsJ2 58 59 27 340 ≤ 97587014394553 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_803 c22250R_58_8 (by norm_num)

theorem c22250R_58_6 : rowsJ2 58 59 26 340 ≤ 97596688402047 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_802 c22250R_58_7 (by norm_num)

theorem c22250R_58_5 : rowsJ2 58 59 25 340 ≤ 97615419363563 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_801 c22250R_58_6 (by norm_num)

theorem c22250R_58_4 : rowsJ2 58 59 24 340 ≤ 97642695194564 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_800 c22250R_58_5 (by norm_num)

theorem c22250R_58_3 : rowsJ2 58 59 23 340 ≤ 97683589404033 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_799 c22250R_58_4 (by norm_num)

theorem c22250R_58_2 : rowsJ2 58 59 21 340 ≤ 97811131645902 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_798 c22250R_58_3 (by norm_num)

theorem c22250R_58_1 : rowsJ2 58 59 17 340 ≤ 98320114453463 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_797 c22250R_58_2 (by norm_num)

theorem c22250R_58_0 : rowsJ2 58 59 0 340 ≤ 101114104426063 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_796 c22250R_58_1 (by norm_num)

theorem hr22250R_58 : rows2 58 59 ≤ 101114104426063 := rows2_le_of_rowsJ2 58 59 c22250R_58_0

theorem c22250R_59_38 : rowsJ2 59 60 58 340 ≤ 30177321680116 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_873 rows22250R_874 (by norm_num)

theorem c22250R_59_37 : rowsJ2 59 60 57 340 ≤ 43567681536509 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_872 c22250R_59_38 (by norm_num)

theorem c22250R_59_36 : rowsJ2 59 60 56 340 ≤ 55928526548329 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_871 c22250R_59_37 (by norm_num)

theorem c22250R_59_35 : rowsJ2 59 60 55 340 ≤ 67099318907223 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_870 c22250R_59_36 (by norm_num)

theorem c22250R_59_34 : rowsJ2 59 60 54 340 ≤ 76895338118866 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_869 c22250R_59_35 (by norm_num)

theorem c22250R_59_33 : rowsJ2 59 60 53 340 ≤ 85307286028264 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_868 c22250R_59_34 (by norm_num)

theorem c22250R_59_32 : rowsJ2 59 60 52 340 ≤ 92372139996893 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_867 c22250R_59_33 (by norm_num)

theorem c22250R_59_31 : rowsJ2 59 60 51 340 ≤ 98128577250677 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_866 c22250R_59_32 (by norm_num)

theorem c22250R_59_30 : rowsJ2 59 60 50 340 ≤ 102522049580013 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_865 c22250R_59_31 (by norm_num)

theorem c22250R_59_29 : rowsJ2 59 60 49 340 ≤ 105792538423716 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_864 c22250R_59_30 (by norm_num)

theorem c22250R_59_28 : rowsJ2 59 60 48 340 ≤ 108183602094957 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_863 c22250R_59_29 (by norm_num)

theorem c22250R_59_27 : rowsJ2 59 60 47 340 ≤ 109801755330643 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_862 c22250R_59_28 (by norm_num)

theorem c22250R_59_26 : rowsJ2 59 60 46 340 ≤ 110616599052284 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_861 c22250R_59_27 (by norm_num)

theorem c22250R_59_25 : rowsJ2 59 60 45 340 ≤ 110889729621289 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_860 c22250R_59_26 (by norm_num)

theorem c22250R_59_24 : rowsJ2 59 60 44 340 ≤ 110959316985792 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_859 c22250R_59_25 (by norm_num)

theorem c22250R_59_23 : rowsJ2 59 60 43 340 ≤ 110959316985792 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_858 c22250R_59_24 (by norm_num)

theorem c22250R_59_22 : rowsJ2 59 60 42 340 ≤ 110959316985792 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_857 c22250R_59_23 (by norm_num)

theorem c22250R_59_21 : rowsJ2 59 60 41 340 ≤ 110959316985792 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_856 c22250R_59_22 (by norm_num)

theorem c22250R_59_20 : rowsJ2 59 60 40 340 ≤ 110959316985792 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_855 c22250R_59_21 (by norm_num)

theorem c22250R_59_19 : rowsJ2 59 60 39 340 ≤ 110959316985792 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_854 c22250R_59_20 (by norm_num)

theorem c22250R_59_18 : rowsJ2 59 60 38 340 ≤ 110959316985792 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_853 c22250R_59_19 (by norm_num)

theorem c22250R_59_17 : rowsJ2 59 60 37 340 ≤ 110959316985792 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_852 c22250R_59_18 (by norm_num)

theorem c22250R_59_16 : rowsJ2 59 60 36 340 ≤ 110959316985792 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_851 c22250R_59_17 (by norm_num)

theorem c22250R_59_15 : rowsJ2 59 60 35 340 ≤ 110959316985792 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_850 c22250R_59_16 (by norm_num)

theorem c22250R_59_14 : rowsJ2 59 60 34 340 ≤ 110959316985792 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_849 c22250R_59_15 (by norm_num)

theorem c22250R_59_13 : rowsJ2 59 60 33 340 ≤ 110959316985792 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_848 c22250R_59_14 (by norm_num)

theorem c22250R_59_12 : rowsJ2 59 60 32 340 ≤ 110959316985792 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_847 c22250R_59_13 (by norm_num)

theorem c22250R_59_11 : rowsJ2 59 60 31 340 ≤ 110959316985792 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_846 c22250R_59_12 (by norm_num)

theorem c22250R_59_10 : rowsJ2 59 60 30 340 ≤ 110959316985792 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_845 c22250R_59_11 (by norm_num)

theorem c22250R_59_9 : rowsJ2 59 60 29 340 ≤ 110959316985792 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_844 c22250R_59_10 (by norm_num)

theorem c22250R_59_8 : rowsJ2 59 60 28 340 ≤ 110959316985792 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_843 c22250R_59_9 (by norm_num)

theorem c22250R_59_7 : rowsJ2 59 60 27 340 ≤ 110959316985792 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_842 c22250R_59_8 (by norm_num)

theorem c22250R_59_6 : rowsJ2 59 60 26 340 ≤ 110963866252954 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_841 c22250R_59_7 (by norm_num)

theorem c22250R_59_5 : rowsJ2 59 60 25 340 ≤ 110972995071575 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_840 c22250R_59_6 (by norm_num)

theorem c22250R_59_4 : rowsJ2 59 60 24 340 ≤ 110991223602529 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_839 c22250R_59_5 (by norm_num)

theorem c22250R_59_3 : rowsJ2 59 60 23 340 ≤ 111018627995061 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_838 c22250R_59_4 (by norm_num)

theorem c22250R_59_2 : rowsJ2 59 60 21 340 ≤ 111114647707791 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_837 c22250R_59_3 (by norm_num)

theorem c22250R_59_1 : rowsJ2 59 60 17 340 ≤ 111533334852640 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_836 c22250R_59_2 (by norm_num)

theorem c22250R_59_0 : rowsJ2 59 60 0 340 ≤ 114155562008162 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_835 c22250R_59_1 (by norm_num)

theorem hr22250R_59 : rows2 59 60 ≤ 114155562008162 := rows2_le_of_rowsJ2 59 60 c22250R_59_0

theorem c22250R_60_39 : rowsJ2 60 61 59 340 ≤ 30032143209855 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_914 rows22250R_915 (by norm_num)

theorem c22250R_60_38 : rowsJ2 60 61 58 340 ≤ 43959373491786 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_913 c22250R_60_39 (by norm_num)

theorem c22250R_60_37 : rowsJ2 60 61 57 340 ≤ 56867728483705 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_912 c22250R_60_38 (by norm_num)

theorem c22250R_60_36 : rowsJ2 60 61 56 340 ≤ 68812419535197 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_911 c22250R_60_37 (by norm_num)

theorem c22250R_60_35 : rowsJ2 60 61 55 340 ≤ 79680679870856 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_910 c22250R_60_36 (by norm_num)

theorem c22250R_60_34 : rowsJ2 60 61 54 340 ≤ 89238930958672 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_909 c22250R_60_35 (by norm_num)

theorem c22250R_60_33 : rowsJ2 60 61 53 340 ≤ 97524046813066 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_908 c22250R_60_34 (by norm_num)

theorem c22250R_60_32 : rowsJ2 60 61 52 340 ≤ 104522893939781 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_907 c22250R_60_33 (by norm_num)

theorem c22250R_60_31 : rowsJ2 60 61 51 340 ≤ 110225548872584 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_906 c22250R_60_32 (by norm_num)

theorem c22250R_60_30 : rowsJ2 60 61 50 340 ≤ 114577973045114 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_905 c22250R_60_31 (by norm_num)

theorem c22250R_60_29 : rowsJ2 60 61 49 340 ≤ 117817905752617 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_904 c22250R_60_30 (by norm_num)

theorem c22250R_60_28 : rowsJ2 60 61 48 340 ≤ 120186629746007 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_903 c22250R_60_29 (by norm_num)

theorem c22250R_60_27 : rowsJ2 60 61 47 340 ≤ 121789664596332 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_902 c22250R_60_28 (by norm_num)

theorem c22250R_60_26 : rowsJ2 60 61 46 340 ≤ 122596895243315 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_901 c22250R_60_27 (by norm_num)

theorem c22250R_60_25 : rowsJ2 60 61 45 340 ≤ 122867473956844 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_900 c22250R_60_26 (by norm_num)

theorem c22250R_60_24 : rowsJ2 60 61 44 340 ≤ 122936411167475 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_899 c22250R_60_25 (by norm_num)

theorem c22250R_60_23 : rowsJ2 60 61 43 340 ≤ 122936411167475 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_898 c22250R_60_24 (by norm_num)

theorem c22250R_60_22 : rowsJ2 60 61 42 340 ≤ 122936411167475 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_897 c22250R_60_23 (by norm_num)

theorem c22250R_60_21 : rowsJ2 60 61 41 340 ≤ 122936411167475 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_896 c22250R_60_22 (by norm_num)

theorem c22250R_60_20 : rowsJ2 60 61 40 340 ≤ 122936411167475 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_895 c22250R_60_21 (by norm_num)

theorem c22250R_60_19 : rowsJ2 60 61 39 340 ≤ 122936411167475 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_894 c22250R_60_20 (by norm_num)

theorem c22250R_60_18 : rowsJ2 60 61 38 340 ≤ 122936411167475 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_893 c22250R_60_19 (by norm_num)

theorem c22250R_60_17 : rowsJ2 60 61 37 340 ≤ 122936411167475 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_892 c22250R_60_18 (by norm_num)

theorem c22250R_60_16 : rowsJ2 60 61 36 340 ≤ 122936411167475 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_891 c22250R_60_17 (by norm_num)

theorem c22250R_60_15 : rowsJ2 60 61 35 340 ≤ 122936411167475 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_890 c22250R_60_16 (by norm_num)

theorem c22250R_60_14 : rowsJ2 60 61 34 340 ≤ 122936411167475 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_889 c22250R_60_15 (by norm_num)

theorem c22250R_60_13 : rowsJ2 60 61 33 340 ≤ 122936411167475 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_888 c22250R_60_14 (by norm_num)

theorem c22250R_60_12 : rowsJ2 60 61 32 340 ≤ 122936411167475 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_887 c22250R_60_13 (by norm_num)

theorem c22250R_60_11 : rowsJ2 60 61 31 340 ≤ 122936411167475 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_886 c22250R_60_12 (by norm_num)

theorem c22250R_60_10 : rowsJ2 60 61 30 340 ≤ 122936411167475 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_885 c22250R_60_11 (by norm_num)

theorem c22250R_60_9 : rowsJ2 60 61 29 340 ≤ 122936411167475 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_884 c22250R_60_10 (by norm_num)

theorem c22250R_60_8 : rowsJ2 60 61 28 340 ≤ 122936411167475 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_883 c22250R_60_9 (by norm_num)

theorem c22250R_60_7 : rowsJ2 60 61 27 340 ≤ 122936411167475 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_882 c22250R_60_8 (by norm_num)

theorem c22250R_60_6 : rowsJ2 60 61 26 340 ≤ 122936411167475 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_881 c22250R_60_7 (by norm_num)

theorem c22250R_60_5 : rowsJ2 60 61 25 340 ≤ 122940980496893 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_880 c22250R_60_6 (by norm_num)

theorem c22250R_60_4 : rowsJ2 60 61 24 340 ≤ 122950151341069 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_879 c22250R_60_5 (by norm_num)

theorem c22250R_60_3 : rowsJ2 60 61 23 340 ≤ 122968467419271 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_878 c22250R_60_4 (by norm_num)

theorem c22250R_60_2 : rowsJ2 60 61 22 340 ≤ 122996009044087 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_877 c22250R_60_3 (by norm_num)

theorem c22250R_60_1 : rowsJ2 60 61 18 340 ≤ 123258654032276 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_876 c22250R_60_2 (by norm_num)

theorem c22250R_60_0 : rowsJ2 60 61 0 340 ≤ 125820844960110 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_875 c22250R_60_1 (by norm_num)

theorem hr22250R_60 : rows2 60 61 ≤ 125820844960110 := rows2_le_of_rowsJ2 60 61 c22250R_60_0

theorem c22250R_61_40 : rowsJ2 61 62 60 340 ≤ 26758307795769 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_956 rows22250R_957 (by norm_num)

theorem c22250R_61_39 : rowsJ2 61 62 59 340 ≤ 41014708343539 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_955 c22250R_61_40 (by norm_num)

theorem c22250R_61_38 : rowsJ2 61 62 58 340 ≤ 54342625906692 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_954 c22250R_61_39 (by norm_num)

theorem c22250R_61_37 : rowsJ2 61 62 57 340 ≤ 66720900489917 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_953 c22250R_61_38 (by norm_num)

theorem c22250R_61_36 : rowsJ2 61 62 56 340 ≤ 78250801984111 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_952 c22250R_61_37 (by norm_num)

theorem c22250R_61_35 : rowsJ2 61 62 55 340 ≤ 88769205858054 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_951 c22250R_61_36 (by norm_num)

theorem c22250R_61_34 : rowsJ2 61 62 54 340 ≤ 98091088366060 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_950 c22250R_61_35 (by norm_num)

theorem c22250R_61_33 : rowsJ2 61 62 53 340 ≤ 106202464789065 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_949 c22250R_61_34 (by norm_num)

theorem c22250R_61_32 : rowsJ2 61 62 52 340 ≤ 113136527059074 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_948 c22250R_61_33 (by norm_num)

theorem c22250R_61_31 : rowsJ2 61 62 51 340 ≤ 118786395343450 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_947 c22250R_61_32 (by norm_num)

theorem c22250R_61_30 : rowsJ2 61 62 50 340 ≤ 123098531284041 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_946 c22250R_61_31 (by norm_num)

theorem c22250R_61_29 : rowsJ2 61 62 49 340 ≤ 126308473541348 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_945 c22250R_61_30 (by norm_num)

theorem c22250R_61_28 : rowsJ2 61 62 48 340 ≤ 128655271431516 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_944 c22250R_61_29 (by norm_num)

theorem c22250R_61_27 : rowsJ2 61 62 47 340 ≤ 130243467783272 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_943 c22250R_61_28 (by norm_num)

theorem c22250R_61_26 : rowsJ2 61 62 46 340 ≤ 131043226296510 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_942 c22250R_61_27 (by norm_num)

theorem c22250R_61_25 : rowsJ2 61 62 45 340 ≤ 131311300397084 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_941 c22250R_61_26 (by norm_num)

theorem c22250R_61_24 : rowsJ2 61 62 44 340 ≤ 131379599490146 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_940 c22250R_61_25 (by norm_num)

theorem c22250R_61_23 : rowsJ2 61 62 43 340 ≤ 131379599490146 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_939 c22250R_61_24 (by norm_num)

theorem c22250R_61_22 : rowsJ2 61 62 42 340 ≤ 131379599490146 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_938 c22250R_61_23 (by norm_num)

theorem c22250R_61_21 : rowsJ2 61 62 41 340 ≤ 131379599490146 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_937 c22250R_61_22 (by norm_num)

theorem c22250R_61_20 : rowsJ2 61 62 40 340 ≤ 131379599490146 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_936 c22250R_61_21 (by norm_num)

theorem c22250R_61_19 : rowsJ2 61 62 39 340 ≤ 131379599490146 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_935 c22250R_61_20 (by norm_num)

theorem c22250R_61_18 : rowsJ2 61 62 38 340 ≤ 131379599490146 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_934 c22250R_61_19 (by norm_num)

theorem c22250R_61_17 : rowsJ2 61 62 37 340 ≤ 131379599490146 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_933 c22250R_61_18 (by norm_num)

theorem c22250R_61_16 : rowsJ2 61 62 36 340 ≤ 131379599490146 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_932 c22250R_61_17 (by norm_num)

theorem c22250R_61_15 : rowsJ2 61 62 35 340 ≤ 131379599490146 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_931 c22250R_61_16 (by norm_num)

theorem c22250R_61_14 : rowsJ2 61 62 34 340 ≤ 131379599490146 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_930 c22250R_61_15 (by norm_num)

theorem c22250R_61_13 : rowsJ2 61 62 33 340 ≤ 131379599490146 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_929 c22250R_61_14 (by norm_num)

theorem c22250R_61_12 : rowsJ2 61 62 32 340 ≤ 131379599490146 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_928 c22250R_61_13 (by norm_num)

theorem c22250R_61_11 : rowsJ2 61 62 31 340 ≤ 131379599490146 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_927 c22250R_61_12 (by norm_num)

theorem c22250R_61_10 : rowsJ2 61 62 30 340 ≤ 131379599490146 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_926 c22250R_61_11 (by norm_num)

theorem c22250R_61_9 : rowsJ2 61 62 29 340 ≤ 131379599490146 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_925 c22250R_61_10 (by norm_num)

theorem c22250R_61_8 : rowsJ2 61 62 28 340 ≤ 131379599490146 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_924 c22250R_61_9 (by norm_num)

theorem c22250R_61_7 : rowsJ2 61 62 27 340 ≤ 131379599490146 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_923 c22250R_61_8 (by norm_num)

theorem c22250R_61_6 : rowsJ2 61 62 26 340 ≤ 131379599490146 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_922 c22250R_61_7 (by norm_num)

theorem c22250R_61_5 : rowsJ2 61 62 25 340 ≤ 131379599490146 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_921 c22250R_61_6 (by norm_num)

theorem c22250R_61_4 : rowsJ2 61 62 24 340 ≤ 131384190255726 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_920 c22250R_61_5 (by norm_num)

theorem c22250R_61_3 : rowsJ2 61 62 23 340 ≤ 131393405949711 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_919 c22250R_61_4 (by norm_num)

theorem c22250R_61_2 : rowsJ2 61 62 22 340 ≤ 131411815355860 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_918 c22250R_61_3 (by norm_num)

theorem c22250R_61_1 : rowsJ2 61 62 18 340 ≤ 131610724715796 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_917 c22250R_61_2 (by norm_num)

theorem c22250R_61_0 : rowsJ2 61 62 0 340 ≤ 133974589468165 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_916 c22250R_61_1 (by norm_num)

theorem hr22250R_61 : rows2 61 62 ≤ 133974589468165 := rows2_le_of_rowsJ2 61 62 c22250R_61_0

theorem c22250R_62_41 : rowsJ2 62 63 61 340 ≤ 22956466915170 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_999 rows22250R_1000 (by norm_num)

theorem c22250R_62_40 : rowsJ2 62 63 60 340 ≤ 35253674964678 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_998 c22250R_62_41 (by norm_num)

theorem c22250R_62_39 : rowsJ2 62 63 59 340 ≤ 48133110604532 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_997 c22250R_62_40 (by norm_num)

theorem c22250R_62_38 : rowsJ2 62 63 58 340 ≤ 60812435452743 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_996 c22250R_62_39 (by norm_num)

theorem c22250R_62_37 : rowsJ2 62 63 57 340 ≤ 72661500989501 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_995 c22250R_62_38 (by norm_num)

theorem c22250R_62_36 : rowsJ2 62 63 56 340 ≤ 83728365918974 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_994 c22250R_62_37 (by norm_num)

theorem c22250R_62_35 : rowsJ2 62 63 55 340 ≤ 93898103534958 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_993 c22250R_62_36 (by norm_num)

theorem c22250R_62_34 : rowsJ2 62 63 54 340 ≤ 102936061736594 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_992 c22250R_62_35 (by norm_num)

theorem c22250R_62_33 : rowsJ2 62 63 53 340 ≤ 110874903629811 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_991 c22250R_62_34 (by norm_num)

theorem c22250R_62_32 : rowsJ2 62 63 52 340 ≤ 117697053764835 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_990 c22250R_62_33 (by norm_num)

theorem c22250R_62_31 : rowsJ2 62 63 51 340 ≤ 123295103677566 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_989 c22250R_62_32 (by norm_num)

theorem c22250R_62_30 : rowsJ2 62 63 50 340 ≤ 127567690401876 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_988 c22250R_62_31 (by norm_num)

theorem c22250R_62_29 : rowsJ2 62 63 49 340 ≤ 130748192330228 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_987 c22250R_62_30 (by norm_num)

theorem c22250R_62_28 : rowsJ2 62 63 48 340 ≤ 133073466312387 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_986 c22250R_62_29 (by norm_num)

theorem c22250R_62_27 : rowsJ2 62 63 47 340 ≤ 134647096351330 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_985 c22250R_62_28 (by norm_num)

theorem c22250R_62_26 : rowsJ2 62 63 46 340 ≤ 135439519793769 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_984 c22250R_62_27 (by norm_num)

theorem c22250R_62_25 : rowsJ2 62 63 45 340 ≤ 135705135224040 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_983 c22250R_62_26 (by norm_num)

theorem c22250R_62_24 : rowsJ2 62 63 44 340 ≤ 135772807904660 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_982 c22250R_62_25 (by norm_num)

theorem c22250R_62_23 : rowsJ2 62 63 43 340 ≤ 135772807904660 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_981 c22250R_62_24 (by norm_num)

theorem c22250R_62_22 : rowsJ2 62 63 42 340 ≤ 135772807904660 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_980 c22250R_62_23 (by norm_num)

theorem c22250R_62_21 : rowsJ2 62 63 41 340 ≤ 135772807904660 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_979 c22250R_62_22 (by norm_num)

theorem c22250R_62_20 : rowsJ2 62 63 40 340 ≤ 135772807904660 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_978 c22250R_62_21 (by norm_num)

theorem c22250R_62_19 : rowsJ2 62 63 39 340 ≤ 135772807904660 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_977 c22250R_62_20 (by norm_num)

theorem c22250R_62_18 : rowsJ2 62 63 38 340 ≤ 135772807904660 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_976 c22250R_62_19 (by norm_num)

theorem c22250R_62_17 : rowsJ2 62 63 37 340 ≤ 135772807904660 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_975 c22250R_62_18 (by norm_num)

theorem c22250R_62_16 : rowsJ2 62 63 36 340 ≤ 135772807904660 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_974 c22250R_62_17 (by norm_num)

theorem c22250R_62_15 : rowsJ2 62 63 35 340 ≤ 135772807904660 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_973 c22250R_62_16 (by norm_num)

theorem c22250R_62_14 : rowsJ2 62 63 34 340 ≤ 135772807904660 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_972 c22250R_62_15 (by norm_num)

theorem c22250R_62_13 : rowsJ2 62 63 33 340 ≤ 135772807904660 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_971 c22250R_62_14 (by norm_num)

theorem c22250R_62_12 : rowsJ2 62 63 32 340 ≤ 135772807904660 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_970 c22250R_62_13 (by norm_num)

theorem c22250R_62_11 : rowsJ2 62 63 31 340 ≤ 135772807904660 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_969 c22250R_62_12 (by norm_num)

theorem c22250R_62_10 : rowsJ2 62 63 30 340 ≤ 135772807904660 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_968 c22250R_62_11 (by norm_num)

theorem c22250R_62_9 : rowsJ2 62 63 29 340 ≤ 135772807904660 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_967 c22250R_62_10 (by norm_num)

theorem c22250R_62_8 : rowsJ2 62 63 28 340 ≤ 135772807904660 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_966 c22250R_62_9 (by norm_num)

theorem c22250R_62_7 : rowsJ2 62 63 27 340 ≤ 135772807904660 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_965 c22250R_62_8 (by norm_num)

theorem c22250R_62_6 : rowsJ2 62 63 26 340 ≤ 135772807904660 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_964 c22250R_62_7 (by norm_num)

theorem c22250R_62_5 : rowsJ2 62 63 25 340 ≤ 135772807904660 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_963 c22250R_62_6 (by norm_num)

theorem c22250R_62_4 : rowsJ2 62 63 24 340 ≤ 135772807904660 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_962 c22250R_62_5 (by norm_num)

theorem c22250R_62_3 : rowsJ2 62 63 23 340 ≤ 135777421516584 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_961 c22250R_62_4 (by norm_num)

theorem c22250R_62_2 : rowsJ2 62 63 21 340 ≤ 135805193641156 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_960 c22250R_62_3 (by norm_num)

theorem c22250R_62_1 : rowsJ2 62 63 18 340 ≤ 135930694173884 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_959 c22250R_62_2 (by norm_num)

theorem c22250R_62_0 : rowsJ2 62 63 0 340 ≤ 138101729988001 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_958 c22250R_62_1 (by norm_num)

theorem hr22250R_62 : rows2 62 63 ≤ 138101729988001 := rows2_le_of_rowsJ2 62 63 c22250R_62_0

theorem c22250R_63_42 : rowsJ2 63 64 62 340 ≤ 19343677575816 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1043 rows22250R_1044 (by norm_num)

theorem c22250R_63_41 : rowsJ2 63 64 61 340 ≤ 29811782867762 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1042 c22250R_63_42 (by norm_num)

theorem c22250R_63_40 : rowsJ2 63 64 60 340 ≤ 40800468604280 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1041 c22250R_63_41 (by norm_num)

theorem c22250R_63_39 : rowsJ2 63 64 59 340 ≤ 52315933596732 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1040 c22250R_63_40 (by norm_num)

theorem c22250R_63_38 : rowsJ2 63 64 58 340 ≤ 64346844404175 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1039 c22250R_63_39 (by norm_num)

theorem c22250R_63_37 : rowsJ2 63 64 57 340 ≤ 75617277299467 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1038 c22250R_63_38 (by norm_num)

theorem c22250R_63_36 : rowsJ2 63 64 56 340 ≤ 86221862662016 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1037 c22250R_63_37 (by norm_num)

theorem c22250R_63_35 : rowsJ2 63 64 55 340 ≤ 95994523637803 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1036 c22250R_63_36 (by norm_num)

theorem c22250R_63_34 : rowsJ2 63 64 54 340 ≤ 104749579185687 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1035 c22250R_63_35 (by norm_num)

theorem c22250R_63_33 : rowsJ2 63 64 53 340 ≤ 112468133989502 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1034 c22250R_63_34 (by norm_num)

theorem c22250R_63_32 : rowsJ2 63 64 52 340 ≤ 119179424427602 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1033 c22250R_63_33 (by norm_num)

theorem c22250R_63_31 : rowsJ2 63 64 51 340 ≤ 124726597845645 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1032 c22250R_63_32 (by norm_num)

theorem c22250R_63_30 : rowsJ2 63 64 50 340 ≤ 128960354220255 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1031 c22250R_63_31 (by norm_num)

theorem c22250R_63_29 : rowsJ2 63 64 49 340 ≤ 132111950941981 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1030 c22250R_63_30 (by norm_num)

theorem c22250R_63_28 : rowsJ2 63 64 48 340 ≤ 134416092245579 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1029 c22250R_63_29 (by norm_num)

theorem c22250R_63_27 : rowsJ2 63 64 47 340 ≤ 135975420736382 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1028 c22250R_63_28 (by norm_num)

theorem c22250R_63_26 : rowsJ2 63 64 46 340 ≤ 136760642433986 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1027 c22250R_63_27 (by norm_num)

theorem c22250R_63_25 : rowsJ2 63 64 45 340 ≤ 137023843883989 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1026 c22250R_63_26 (by norm_num)

theorem c22250R_63_24 : rowsJ2 63 64 44 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1025 c22250R_63_25 (by norm_num)

theorem c22250R_63_23 : rowsJ2 63 64 43 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1024 c22250R_63_24 (by norm_num)

theorem c22250R_63_22 : rowsJ2 63 64 42 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1023 c22250R_63_23 (by norm_num)

theorem c22250R_63_21 : rowsJ2 63 64 41 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1022 c22250R_63_22 (by norm_num)

theorem c22250R_63_20 : rowsJ2 63 64 40 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1021 c22250R_63_21 (by norm_num)

theorem c22250R_63_19 : rowsJ2 63 64 39 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1020 c22250R_63_20 (by norm_num)

theorem c22250R_63_18 : rowsJ2 63 64 38 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1019 c22250R_63_19 (by norm_num)

theorem c22250R_63_17 : rowsJ2 63 64 37 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1018 c22250R_63_18 (by norm_num)

theorem c22250R_63_16 : rowsJ2 63 64 36 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1017 c22250R_63_17 (by norm_num)

theorem c22250R_63_15 : rowsJ2 63 64 35 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1016 c22250R_63_16 (by norm_num)

theorem c22250R_63_14 : rowsJ2 63 64 34 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1015 c22250R_63_15 (by norm_num)

theorem c22250R_63_13 : rowsJ2 63 64 33 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1014 c22250R_63_14 (by norm_num)

theorem c22250R_63_12 : rowsJ2 63 64 32 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1013 c22250R_63_13 (by norm_num)

theorem c22250R_63_11 : rowsJ2 63 64 31 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1012 c22250R_63_12 (by norm_num)

theorem c22250R_63_10 : rowsJ2 63 64 30 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1011 c22250R_63_11 (by norm_num)

theorem c22250R_63_9 : rowsJ2 63 64 29 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1010 c22250R_63_10 (by norm_num)

theorem c22250R_63_8 : rowsJ2 63 64 28 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1009 c22250R_63_9 (by norm_num)

theorem c22250R_63_7 : rowsJ2 63 64 27 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1008 c22250R_63_8 (by norm_num)

theorem c22250R_63_6 : rowsJ2 63 64 26 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1007 c22250R_63_7 (by norm_num)

theorem c22250R_63_5 : rowsJ2 63 64 25 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1006 c22250R_63_6 (by norm_num)

theorem c22250R_63_4 : rowsJ2 63 64 24 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1005 c22250R_63_5 (by norm_num)

theorem c22250R_63_3 : rowsJ2 63 64 23 340 ≤ 137090901538157 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1004 c22250R_63_4 (by norm_num)

theorem c22250R_63_2 : rowsJ2 63 64 21 340 ≤ 137104853628019 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1003 c22250R_63_3 (by norm_num)

theorem c22250R_63_1 : rowsJ2 63 64 18 340 ≤ 137193512782295 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1002 c22250R_63_2 (by norm_num)

theorem c22250R_63_0 : rowsJ2 63 64 0 340 ≤ 139176067184458 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1001 c22250R_63_1 (by norm_num)

theorem hr22250R_63 : rows2 63 64 ≤ 139176067184458 := rows2_le_of_rowsJ2 63 64 c22250R_63_0

theorem c22250R_64_43 : rowsJ2 64 65 63 340 ≤ 16063811242448 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1088 rows22250R_1089 (by norm_num)

theorem c22250R_64_42 : rowsJ2 64 65 62 340 ≤ 24835151745350 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1087 c22250R_64_43 (by norm_num)

theorem c22250R_64_41 : rowsJ2 64 65 61 340 ≤ 34135352047424 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1086 c22250R_64_42 (by norm_num)

theorem c22250R_64_40 : rowsJ2 64 65 60 340 ≤ 43900843374871 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1085 c22250R_64_41 (by norm_num)

theorem c22250R_64_39 : rowsJ2 64 65 59 340 ≤ 54188911652773 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1084 c22250R_64_40 (by norm_num)

theorem c22250R_64_38 : rowsJ2 64 65 58 340 ≤ 64937491873224 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1083 c22250R_64_39 (by norm_num)

theorem c22250R_64_37 : rowsJ2 64 65 57 340 ≤ 75629387659520 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1082 c22250R_64_38 (by norm_num)

theorem c22250R_64_36 : rowsJ2 64 65 56 340 ≤ 85722168703330 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1081 c22250R_64_37 (by norm_num)

theorem c22250R_64_35 : rowsJ2 64 65 55 340 ≤ 95098410840297 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1080 c22250R_64_36 (by norm_num)

theorem c22250R_64_34 : rowsJ2 64 65 54 340 ≤ 103521985344541 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1079 c22250R_64_35 (by norm_num)

theorem c22250R_64_33 : rowsJ2 64 65 53 340 ≤ 111021147312182 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1078 c22250R_64_34 (by norm_num)

theorem c22250R_64_32 : rowsJ2 64 65 52 340 ≤ 117573659687216 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1077 c22250R_64_33 (by norm_num)

theorem c22250R_64_31 : rowsJ2 64 65 51 340 ≤ 123070873038778 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1076 c22250R_64_32 (by norm_num)

theorem c22250R_64_30 : rowsJ2 64 65 50 340 ≤ 127266498507061 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1075 c22250R_64_31 (by norm_num)

theorem c22250R_64_29 : rowsJ2 64 65 49 340 ≤ 130389710685899 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1074 c22250R_64_30 (by norm_num)

theorem c22250R_64_28 : rowsJ2 64 65 48 340 ≤ 132673099969669 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1073 c22250R_64_29 (by norm_num)

theorem c22250R_64_27 : rowsJ2 64 65 47 340 ≤ 134218384523277 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1072 c22250R_64_28 (by norm_num)

theorem c22250R_64_26 : rowsJ2 64 65 46 340 ≤ 134996534199642 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1071 c22250R_64_27 (by norm_num)

theorem c22250R_64_25 : rowsJ2 64 65 45 340 ≤ 135257365151924 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1070 c22250R_64_26 (by norm_num)

theorem c22250R_64_24 : rowsJ2 64 65 44 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1069 c22250R_64_25 (by norm_num)

theorem c22250R_64_23 : rowsJ2 64 65 43 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1068 c22250R_64_24 (by norm_num)

theorem c22250R_64_22 : rowsJ2 64 65 42 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1067 c22250R_64_23 (by norm_num)

theorem c22250R_64_21 : rowsJ2 64 65 41 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1066 c22250R_64_22 (by norm_num)

theorem c22250R_64_20 : rowsJ2 64 65 40 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1065 c22250R_64_21 (by norm_num)

theorem c22250R_64_19 : rowsJ2 64 65 39 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1064 c22250R_64_20 (by norm_num)

theorem c22250R_64_18 : rowsJ2 64 65 38 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1063 c22250R_64_19 (by norm_num)

theorem c22250R_64_17 : rowsJ2 64 65 37 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1062 c22250R_64_18 (by norm_num)

theorem c22250R_64_16 : rowsJ2 64 65 36 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1061 c22250R_64_17 (by norm_num)

theorem c22250R_64_15 : rowsJ2 64 65 35 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1060 c22250R_64_16 (by norm_num)

theorem c22250R_64_14 : rowsJ2 64 65 34 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1059 c22250R_64_15 (by norm_num)

theorem c22250R_64_13 : rowsJ2 64 65 33 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1058 c22250R_64_14 (by norm_num)

theorem c22250R_64_12 : rowsJ2 64 65 32 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1057 c22250R_64_13 (by norm_num)

theorem c22250R_64_11 : rowsJ2 64 65 31 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1056 c22250R_64_12 (by norm_num)

theorem c22250R_64_10 : rowsJ2 64 65 30 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1055 c22250R_64_11 (by norm_num)

theorem c22250R_64_9 : rowsJ2 64 65 29 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1054 c22250R_64_10 (by norm_num)

theorem c22250R_64_8 : rowsJ2 64 65 28 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1053 c22250R_64_9 (by norm_num)

theorem c22250R_64_7 : rowsJ2 64 65 27 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1052 c22250R_64_8 (by norm_num)

theorem c22250R_64_6 : rowsJ2 64 65 26 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1051 c22250R_64_7 (by norm_num)

theorem c22250R_64_5 : rowsJ2 64 65 25 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1050 c22250R_64_6 (by norm_num)

theorem c22250R_64_4 : rowsJ2 64 65 24 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1049 c22250R_64_5 (by norm_num)

theorem c22250R_64_3 : rowsJ2 64 65 23 340 ≤ 135323818857989 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1048 c22250R_64_4 (by norm_num)

theorem c22250R_64_2 : rowsJ2 64 65 21 340 ≤ 135328482553106 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1047 c22250R_64_3 (by norm_num)

theorem c22250R_64_1 : rowsJ2 64 65 18 340 ≤ 135384758755747 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1046 c22250R_64_2 (by norm_num)

theorem c22250R_64_0 : rowsJ2 64 65 0 340 ≤ 137180618962578 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1045 c22250R_64_1 (by norm_num)

theorem hr22250R_64 : rows2 64 65 ≤ 137180618962578 := rows2_le_of_rowsJ2 64 65 c22250R_64_0

theorem c22250R_65_42 : rowsJ2 65 66 64 340 ≤ 13110678002284 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1132 rows22250R_1133 (by norm_num)

theorem c22250R_65_41 : rowsJ2 65 66 63 340 ≤ 20383703651273 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1131 c22250R_65_42 (by norm_num)

theorem c22250R_65_40 : rowsJ2 65 66 62 340 ≤ 28124799101844 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1130 c22250R_65_41 (by norm_num)

theorem c22250R_65_39 : rowsJ2 65 66 61 340 ≤ 36338894548967 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1129 c22250R_65_40 (by norm_num)

theorem c22250R_65_38 : rowsJ2 65 66 60 340 ≤ 45014876334836 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1128 c22250R_65_39 (by norm_num)

theorem c22250R_65_37 : rowsJ2 65 66 59 340 ≤ 54158028394499 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1127 c22250R_65_38 (by norm_num)

theorem c22250R_65_36 : rowsJ2 65 66 58 340 ≤ 63758011064584 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1126 c22250R_65_37 (by norm_num)

theorem c22250R_65_35 : rowsJ2 65 66 57 340 ≤ 73820463567799 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1125 c22250R_65_36 (by norm_num)

theorem c22250R_65_34 : rowsJ2 65 66 56 340 ≤ 83401501016331 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1124 c22250R_65_35 (by norm_num)

theorem c22250R_65_33 : rowsJ2 65 66 55 340 ≤ 92331702927985 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1123 c22250R_65_34 (by norm_num)

theorem c22250R_65_32 : rowsJ2 65 66 54 340 ≤ 100424357902881 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1122 c22250R_65_33 (by norm_num)

theorem c22250R_65_31 : rowsJ2 65 66 53 340 ≤ 107655410595836 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1121 c22250R_65_32 (by norm_num)

theorem c22250R_65_30 : rowsJ2 65 66 52 340 ≤ 114049949712672 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1120 c22250R_65_31 (by norm_num)

theorem c22250R_65_29 : rowsJ2 65 66 51 340 ≤ 119449124855784 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1119 c22250R_65_30 (by norm_num)

theorem c22250R_65_28 : rowsJ2 65 66 50 340 ≤ 123607300131402 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1118 c22250R_65_29 (by norm_num)

theorem c22250R_65_27 : rowsJ2 65 66 49 340 ≤ 126702634488754 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1117 c22250R_65_28 (by norm_num)

theorem c22250R_65_26 : rowsJ2 65 66 48 340 ≤ 128965642218152 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1116 c22250R_65_27 (by norm_num)

theorem c22250R_65_25 : rowsJ2 65 66 47 340 ≤ 130497133547199 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1115 c22250R_65_26 (by norm_num)

theorem c22250R_65_24 : rowsJ2 65 66 46 340 ≤ 131268337452183 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1114 c22250R_65_25 (by norm_num)

theorem c22250R_65_23 : rowsJ2 65 66 45 340 ≤ 131526840224914 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1113 c22250R_65_24 (by norm_num)

theorem c22250R_65_22 : rowsJ2 65 66 44 340 ≤ 131592700764569 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1112 c22250R_65_23 (by norm_num)

theorem c22250R_65_21 : rowsJ2 65 66 43 340 ≤ 131592700764569 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1111 c22250R_65_22 (by norm_num)

theorem c22250R_65_20 : rowsJ2 65 66 42 340 ≤ 131592700764569 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1110 c22250R_65_21 (by norm_num)

theorem c22250R_65_19 : rowsJ2 65 66 41 340 ≤ 131592700764569 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1109 c22250R_65_20 (by norm_num)

theorem c22250R_65_18 : rowsJ2 65 66 39 340 ≤ 131592700764569 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1108 c22250R_65_19 (by norm_num)

theorem c22250R_65_17 : rowsJ2 65 66 37 340 ≤ 131592700764569 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1107 c22250R_65_18 (by norm_num)

theorem c22250R_65_16 : rowsJ2 65 66 36 340 ≤ 131592700764569 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1106 c22250R_65_17 (by norm_num)

theorem c22250R_65_15 : rowsJ2 65 66 35 340 ≤ 131592700764569 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1105 c22250R_65_16 (by norm_num)

theorem c22250R_65_14 : rowsJ2 65 66 34 340 ≤ 131592700764569 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1104 c22250R_65_15 (by norm_num)

theorem c22250R_65_13 : rowsJ2 65 66 33 340 ≤ 131592700764569 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1103 c22250R_65_14 (by norm_num)

theorem c22250R_65_12 : rowsJ2 65 66 32 340 ≤ 131592700764569 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1102 c22250R_65_13 (by norm_num)

theorem c22250R_65_11 : rowsJ2 65 66 31 340 ≤ 131592700764569 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1101 c22250R_65_12 (by norm_num)

theorem c22250R_65_10 : rowsJ2 65 66 30 340 ≤ 131592700764569 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1100 c22250R_65_11 (by norm_num)

theorem c22250R_65_9 : rowsJ2 65 66 29 340 ≤ 131592700764569 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1099 c22250R_65_10 (by norm_num)

theorem c22250R_65_8 : rowsJ2 65 66 28 340 ≤ 131592700764569 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1098 c22250R_65_9 (by norm_num)

theorem c22250R_65_7 : rowsJ2 65 66 27 340 ≤ 131592700764569 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1097 c22250R_65_8 (by norm_num)

theorem c22250R_65_6 : rowsJ2 65 66 26 340 ≤ 131592700764569 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1096 c22250R_65_7 (by norm_num)

theorem c22250R_65_5 : rowsJ2 65 66 25 340 ≤ 131592700764569 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1095 c22250R_65_6 (by norm_num)

theorem c22250R_65_4 : rowsJ2 65 66 24 340 ≤ 131592700764569 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1094 c22250R_65_5 (by norm_num)

theorem c22250R_65_3 : rowsJ2 65 66 23 340 ≤ 131592700764569 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1093 c22250R_65_4 (by norm_num)

theorem c22250R_65_2 : rowsJ2 65 66 21 340 ≤ 131592700764569 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1092 c22250R_65_3 (by norm_num)

theorem c22250R_65_1 : rowsJ2 65 66 18 340 ≤ 131625660777941 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1091 c22250R_65_2 (by norm_num)

theorem c22250R_65_0 : rowsJ2 65 66 0 340 ≤ 133244628095711 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1090 c22250R_65_1 (by norm_num)

theorem hr22250R_65 : rows2 65 66 ≤ 133244628095711 := rows2_le_of_rowsJ2 65 66 c22250R_65_0

theorem c22250R_66_43 : rowsJ2 66 67 65 340 ≤ 10477786509225 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1177 rows22250R_1178 (by norm_num)

theorem c22250R_66_42 : rowsJ2 66 67 64 340 ≤ 16378120593349 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1176 c22250R_66_43 (by norm_num)

theorem c22250R_66_41 : rowsJ2 66 67 63 340 ≤ 22755320362151 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1175 c22250R_66_42 (by norm_num)

theorem c22250R_66_40 : rowsJ2 66 67 62 340 ≤ 29544675200026 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1174 c22250R_66_41 (by norm_num)

theorem c22250R_66_39 : rowsJ2 66 67 61 340 ≤ 36803741438012 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1173 c22250R_66_40 (by norm_num)

theorem c22250R_66_38 : rowsJ2 66 67 60 340 ≤ 44469320506041 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1172 c22250R_66_39 (by norm_num)

theorem c22250R_66_37 : rowsJ2 66 67 59 340 ≤ 52598565761913 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1171 c22250R_66_38 (by norm_num)

theorem c22250R_66_36 : rowsJ2 66 67 58 340 ≤ 61129719396371 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1170 c22250R_66_37 (by norm_num)

theorem c22250R_66_35 : rowsJ2 66 67 57 340 ≤ 70119578893816 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1169 c22250R_66_36 (by norm_num)

theorem c22250R_66_34 : rowsJ2 66 67 56 340 ≤ 79137937043712 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1168 c22250R_66_35 (by norm_num)

theorem c22250R_66_33 : rowsJ2 66 67 55 340 ≤ 87622136223515 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1167 c22250R_66_34 (by norm_num)

theorem c22250R_66_32 : rowsJ2 66 67 54 340 ≤ 95334146295443 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1166 c22250R_66_33 (by norm_num)

theorem c22250R_66_31 : rowsJ2 66 67 53 340 ≤ 102297591640968 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1165 c22250R_66_32 (by norm_num)

theorem c22250R_66_30 : rowsJ2 66 67 52 340 ≤ 108485329905804 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1164 c22250R_66_31 (by norm_num)

theorem c22250R_66_29 : rowsJ2 66 67 51 340 ≤ 113787195954357 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1163 c22250R_66_30 (by norm_num)

theorem c22250R_66_28 : rowsJ2 66 67 50 340 ≤ 117908583684061 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1162 c22250R_66_29 (by norm_num)

theorem c22250R_66_27 : rowsJ2 66 67 49 340 ≤ 120976533492370 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1161 c22250R_66_28 (by norm_num)

theorem c22250R_66_26 : rowsJ2 66 67 48 340 ≤ 123219520300280 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1160 c22250R_66_27 (by norm_num)

theorem c22250R_66_25 : rowsJ2 66 67 47 340 ≤ 124737462463208 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1159 c22250R_66_26 (by norm_num)

theorem c22250R_66_24 : rowsJ2 66 67 46 340 ≤ 125501843495855 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1158 c22250R_66_25 (by norm_num)

theorem c22250R_66_23 : rowsJ2 66 67 45 340 ≤ 125758059284036 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1157 c22250R_66_24 (by norm_num)

theorem c22250R_66_22 : rowsJ2 66 67 44 340 ≤ 125823337152817 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1156 c22250R_66_23 (by norm_num)

theorem c22250R_66_21 : rowsJ2 66 67 43 340 ≤ 125823337152817 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1155 c22250R_66_22 (by norm_num)

theorem c22250R_66_20 : rowsJ2 66 67 42 340 ≤ 125823337152817 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1154 c22250R_66_21 (by norm_num)

theorem c22250R_66_19 : rowsJ2 66 67 40 340 ≤ 125823337152817 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1153 c22250R_66_20 (by norm_num)

theorem c22250R_66_18 : rowsJ2 66 67 38 340 ≤ 125823337152817 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1152 c22250R_66_19 (by norm_num)

theorem c22250R_66_17 : rowsJ2 66 67 36 340 ≤ 125823337152817 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1151 c22250R_66_18 (by norm_num)

theorem c22250R_66_16 : rowsJ2 66 67 35 340 ≤ 125823337152817 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1150 c22250R_66_17 (by norm_num)

theorem c22250R_66_15 : rowsJ2 66 67 34 340 ≤ 125823337152817 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1149 c22250R_66_16 (by norm_num)

theorem c22250R_66_14 : rowsJ2 66 67 33 340 ≤ 125823337152817 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1148 c22250R_66_15 (by norm_num)

theorem c22250R_66_13 : rowsJ2 66 67 32 340 ≤ 125823337152817 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1147 c22250R_66_14 (by norm_num)

theorem c22250R_66_12 : rowsJ2 66 67 31 340 ≤ 125823337152817 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1146 c22250R_66_13 (by norm_num)

theorem c22250R_66_11 : rowsJ2 66 67 30 340 ≤ 125823337152817 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1145 c22250R_66_12 (by norm_num)

theorem c22250R_66_10 : rowsJ2 66 67 29 340 ≤ 125823337152817 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1144 c22250R_66_11 (by norm_num)

theorem c22250R_66_9 : rowsJ2 66 67 28 340 ≤ 125823337152817 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1143 c22250R_66_10 (by norm_num)

theorem c22250R_66_8 : rowsJ2 66 67 27 340 ≤ 125823337152817 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1142 c22250R_66_9 (by norm_num)

theorem c22250R_66_7 : rowsJ2 66 67 26 340 ≤ 125823337152817 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1141 c22250R_66_8 (by norm_num)

theorem c22250R_66_6 : rowsJ2 66 67 25 340 ≤ 125823337152817 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1140 c22250R_66_7 (by norm_num)

theorem c22250R_66_5 : rowsJ2 66 67 24 340 ≤ 125823337152817 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1139 c22250R_66_6 (by norm_num)

theorem c22250R_66_4 : rowsJ2 66 67 23 340 ≤ 125823337152817 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1138 c22250R_66_5 (by norm_num)

theorem c22250R_66_3 : rowsJ2 66 67 22 340 ≤ 125823337152817 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1137 c22250R_66_4 (by norm_num)

theorem c22250R_66_2 : rowsJ2 66 67 21 340 ≤ 125823337152817 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1136 c22250R_66_3 (by norm_num)

theorem c22250R_66_1 : rowsJ2 66 67 18 340 ≤ 125837542326231 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1135 c22250R_66_2 (by norm_num)

theorem c22250R_66_0 : rowsJ2 66 67 0 340 ≤ 127285754733793 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1134 c22250R_66_1 (by norm_num)

theorem hr22250R_66 : rows2 66 67 ≤ 127285754733793 := rows2_le_of_rowsJ2 66 67 c22250R_66_0

theorem c22250R_67_44 : rowsJ2 67 68 66 340 ≤ 8160867047005 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1223 rows22250R_1224 (by norm_num)

theorem c22250R_67_43 : rowsJ2 67 68 65 340 ≤ 12881153626297 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1222 c22250R_67_44 (by norm_num)

theorem c22250R_67_42 : rowsJ2 67 68 64 340 ≤ 18017791961358 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1221 c22250R_67_43 (by norm_num)

theorem c22250R_67_41 : rowsJ2 67 68 63 340 ≤ 23574607446681 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1220 c22250R_67_42 (by norm_num)

theorem c22250R_67_40 : rowsJ2 67 68 62 340 ≤ 29540947794698 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1219 c22250R_67_41 (by norm_num)

theorem c22250R_67_39 : rowsJ2 67 68 61 340 ≤ 35920951929594 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1218 c22250R_67_40 (by norm_num)

theorem c22250R_67_38 : rowsJ2 67 68 60 340 ≤ 42704673809139 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1217 c22250R_67_39 (by norm_num)

theorem c22250R_67_37 : rowsJ2 67 68 59 340 ≤ 49896563660811 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1216 c22250R_67_38 (by norm_num)

theorem c22250R_67_36 : rowsJ2 67 68 58 340 ≤ 57487358256308 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1215 c22250R_67_37 (by norm_num)

theorem c22250R_67_35 : rowsJ2 67 68 57 340 ≤ 65481819533892 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1214 c22250R_67_36 (by norm_num)

theorem c22250R_67_34 : rowsJ2 67 68 56 340 ≤ 73936767073047 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1213 c22250R_67_35 (by norm_num)

theorem c22250R_67_33 : rowsJ2 67 68 55 340 ≤ 81923999237666 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1212 c22250R_67_34 (by norm_num)

theorem c22250R_67_32 : rowsJ2 67 68 54 340 ≤ 89255378822106 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1211 c22250R_67_33 (by norm_num)

theorem c22250R_67_31 : rowsJ2 67 68 53 340 ≤ 95901413043691 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1210 c22250R_67_32 (by norm_num)

theorem c22250R_67_30 : rowsJ2 67 68 52 340 ≤ 101882826657754 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1209 c22250R_67_31 (by norm_num)

theorem c22250R_67_29 : rowsJ2 67 68 51 340 ≤ 107038448231546 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1208 c22250R_67_30 (by norm_num)

theorem c22250R_67_28 : rowsJ2 67 68 50 340 ≤ 111123693628952 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1207 c22250R_67_29 (by norm_num)

theorem c22250R_67_27 : rowsJ2 67 68 49 340 ≤ 114164739183464 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1206 c22250R_67_28 (by norm_num)

theorem c22250R_67_26 : rowsJ2 67 68 48 340 ≤ 116388056215101 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1205 c22250R_67_27 (by norm_num)

theorem c22250R_67_25 : rowsJ2 67 68 47 340 ≤ 117892686849567 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1204 c22250R_67_26 (by norm_num)

theorem c22250R_67_24 : rowsJ2 67 68 46 340 ≤ 118650364675650 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1203 c22250R_67_25 (by norm_num)

theorem c22250R_67_23 : rowsJ2 67 68 45 340 ≤ 118904333590503 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1202 c22250R_67_24 (by norm_num)

theorem c22250R_67_22 : rowsJ2 67 68 44 340 ≤ 118969039007823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1201 c22250R_67_23 (by norm_num)

theorem c22250R_67_21 : rowsJ2 67 68 43 340 ≤ 118969039007823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1200 c22250R_67_22 (by norm_num)

theorem c22250R_67_20 : rowsJ2 67 68 42 340 ≤ 118969039007823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1199 c22250R_67_21 (by norm_num)

theorem c22250R_67_19 : rowsJ2 67 68 41 340 ≤ 118969039007823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1198 c22250R_67_20 (by norm_num)

theorem c22250R_67_18 : rowsJ2 67 68 39 340 ≤ 118969039007823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1197 c22250R_67_19 (by norm_num)

theorem c22250R_67_17 : rowsJ2 67 68 37 340 ≤ 118969039007823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1196 c22250R_67_18 (by norm_num)

theorem c22250R_67_16 : rowsJ2 67 68 35 340 ≤ 118969039007823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1195 c22250R_67_17 (by norm_num)

theorem c22250R_67_15 : rowsJ2 67 68 34 340 ≤ 118969039007823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1194 c22250R_67_16 (by norm_num)

theorem c22250R_67_14 : rowsJ2 67 68 33 340 ≤ 118969039007823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1193 c22250R_67_15 (by norm_num)

theorem c22250R_67_13 : rowsJ2 67 68 32 340 ≤ 118969039007823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1192 c22250R_67_14 (by norm_num)

theorem c22250R_67_12 : rowsJ2 67 68 31 340 ≤ 118969039007823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1191 c22250R_67_13 (by norm_num)

theorem c22250R_67_11 : rowsJ2 67 68 30 340 ≤ 118969039007823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1190 c22250R_67_12 (by norm_num)

theorem c22250R_67_10 : rowsJ2 67 68 29 340 ≤ 118969039007823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1189 c22250R_67_11 (by norm_num)

theorem c22250R_67_9 : rowsJ2 67 68 28 340 ≤ 118969039007823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1188 c22250R_67_10 (by norm_num)

theorem c22250R_67_8 : rowsJ2 67 68 27 340 ≤ 118969039007823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1187 c22250R_67_9 (by norm_num)

theorem c22250R_67_7 : rowsJ2 67 68 26 340 ≤ 118969039007823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1186 c22250R_67_8 (by norm_num)

theorem c22250R_67_6 : rowsJ2 67 68 25 340 ≤ 118969039007823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1185 c22250R_67_7 (by norm_num)

theorem c22250R_67_5 : rowsJ2 67 68 24 340 ≤ 118969039007823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1184 c22250R_67_6 (by norm_num)

theorem c22250R_67_4 : rowsJ2 67 68 23 340 ≤ 118969039007823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1183 c22250R_67_5 (by norm_num)

theorem c22250R_67_3 : rowsJ2 67 68 22 340 ≤ 118969039007823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1182 c22250R_67_4 (by norm_num)

theorem c22250R_67_2 : rowsJ2 67 68 21 340 ≤ 118969039007823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1181 c22250R_67_3 (by norm_num)

theorem c22250R_67_1 : rowsJ2 67 68 18 340 ≤ 118973789489775 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1180 c22250R_67_2 (by norm_num)

theorem c22250R_67_0 : rowsJ2 67 68 0 340 ≤ 120257345809489 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1179 c22250R_67_1 (by norm_num)

theorem hr22250R_67 : rows2 67 68 ≤ 120257345809489 := rows2_le_of_rowsJ2 67 68 c22250R_67_0

theorem c22250R_68_44 : rowsJ2 68 69 67 340 ≤ 6090949738662 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1269 rows22250R_1270 (by norm_num)

theorem c22250R_68_43 : rowsJ2 68 69 66 340 ≤ 9684872311355 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1268 c22250R_68_44 (by norm_num)

theorem c22250R_68_42 : rowsJ2 68 69 65 340 ≤ 13704072721943 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1267 c22250R_68_43 (by norm_num)

theorem c22250R_68_41 : rowsJ2 68 69 64 340 ≤ 18082772331981 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1266 c22250R_68_42 (by norm_num)

theorem c22250R_68_40 : rowsJ2 68 69 63 340 ≤ 22879103167919 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1265 c22250R_68_41 (by norm_num)

theorem c22250R_68_39 : rowsJ2 68 69 62 340 ≤ 28028812334466 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1264 c22250R_68_40 (by norm_num)

theorem c22250R_68_38 : rowsJ2 68 69 61 340 ≤ 33589509525486 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1263 c22250R_68_39 (by norm_num)

theorem c22250R_68_37 : rowsJ2 68 69 60 340 ≤ 39498391376160 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1262 c22250R_68_38 (by norm_num)

theorem c22250R_68_36 : rowsJ2 68 69 59 340 ≤ 45812591995947 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1261 c22250R_68_37 (by norm_num)

theorem c22250R_68_35 : rowsJ2 68 69 58 340 ≤ 52470686652743 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1260 c22250R_68_36 (by norm_num)

theorem c22250R_68_34 : rowsJ2 68 69 57 340 ≤ 59529381573930 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1259 c22250R_68_35 (by norm_num)

theorem c22250R_68_33 : rowsJ2 68 69 56 340 ≤ 66993415669304 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1258 c22250R_68_34 (by norm_num)

theorem c22250R_68_32 : rowsJ2 68 69 55 340 ≤ 74483003809630 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1257 c22250R_68_33 (by norm_num)

theorem c22250R_68_31 : rowsJ2 68 69 54 340 ≤ 81382749919426 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1256 c22250R_68_32 (by norm_num)

theorem c22250R_68_30 : rowsJ2 68 69 53 340 ≤ 87711396714769 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1255 c22250R_68_31 (by norm_num)

theorem c22250R_68_29 : rowsJ2 68 69 52 340 ≤ 93436626361452 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1254 c22250R_68_30 (by norm_num)

theorem c22250R_68_28 : rowsJ2 68 69 51 340 ≤ 98446465034192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1253 c22250R_68_29 (by norm_num)

theorem c22250R_68_27 : rowsJ2 68 69 50 340 ≤ 102446506909313 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1252 c22250R_68_28 (by norm_num)

theorem c22250R_68_26 : rowsJ2 68 69 49 340 ≤ 105461115979339 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1251 c22250R_68_27 (by norm_num)

theorem c22250R_68_25 : rowsJ2 68 69 48 340 ≤ 107665105222179 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1250 c22250R_68_26 (by norm_num)

theorem c22250R_68_24 : rowsJ2 68 69 47 340 ≤ 109156655768327 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1249 c22250R_68_25 (by norm_num)

theorem c22250R_68_23 : rowsJ2 68 69 46 340 ≤ 109907746932771 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1248 c22250R_68_24 (by norm_num)

theorem c22250R_68_22 : rowsJ2 68 69 45 340 ≤ 110159508039437 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1247 c22250R_68_23 (by norm_num)

theorem c22250R_68_21 : rowsJ2 68 69 44 340 ≤ 110223650958192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1246 c22250R_68_22 (by norm_num)

theorem c22250R_68_20 : rowsJ2 68 69 43 340 ≤ 110223650958192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1245 c22250R_68_21 (by norm_num)

theorem c22250R_68_19 : rowsJ2 68 69 42 340 ≤ 110223650958192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1244 c22250R_68_20 (by norm_num)

theorem c22250R_68_18 : rowsJ2 68 69 40 340 ≤ 110223650958192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1243 c22250R_68_19 (by norm_num)

theorem c22250R_68_17 : rowsJ2 68 69 38 340 ≤ 110223650958192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1242 c22250R_68_18 (by norm_num)

theorem c22250R_68_16 : rowsJ2 68 69 36 340 ≤ 110223650958192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1241 c22250R_68_17 (by norm_num)

theorem c22250R_68_15 : rowsJ2 68 69 34 340 ≤ 110223650958192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1240 c22250R_68_16 (by norm_num)

theorem c22250R_68_14 : rowsJ2 68 69 33 340 ≤ 110223650958192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1239 c22250R_68_15 (by norm_num)

theorem c22250R_68_13 : rowsJ2 68 69 32 340 ≤ 110223650958192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1238 c22250R_68_14 (by norm_num)

theorem c22250R_68_12 : rowsJ2 68 69 31 340 ≤ 110223650958192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1237 c22250R_68_13 (by norm_num)

theorem c22250R_68_11 : rowsJ2 68 69 30 340 ≤ 110223650958192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1236 c22250R_68_12 (by norm_num)

theorem c22250R_68_10 : rowsJ2 68 69 29 340 ≤ 110223650958192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1235 c22250R_68_11 (by norm_num)

theorem c22250R_68_9 : rowsJ2 68 69 28 340 ≤ 110223650958192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1234 c22250R_68_10 (by norm_num)

theorem c22250R_68_8 : rowsJ2 68 69 27 340 ≤ 110223650958192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1233 c22250R_68_9 (by norm_num)

theorem c22250R_68_7 : rowsJ2 68 69 26 340 ≤ 110223650958192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1232 c22250R_68_8 (by norm_num)

theorem c22250R_68_6 : rowsJ2 68 69 25 340 ≤ 110223650958192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1231 c22250R_68_7 (by norm_num)

theorem c22250R_68_5 : rowsJ2 68 69 24 340 ≤ 110223650958192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1230 c22250R_68_6 (by norm_num)

theorem c22250R_68_4 : rowsJ2 68 69 23 340 ≤ 110223650958192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1229 c22250R_68_5 (by norm_num)

theorem c22250R_68_3 : rowsJ2 68 69 22 340 ≤ 110223650958192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1228 c22250R_68_4 (by norm_num)

theorem c22250R_68_2 : rowsJ2 68 69 21 340 ≤ 110223650958192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1227 c22250R_68_3 (by norm_num)

theorem c22250R_68_1 : rowsJ2 68 69 18 340 ≤ 110223650958192 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1226 c22250R_68_2 (by norm_num)

theorem c22250R_68_0 : rowsJ2 68 69 0 340 ≤ 111354452906087 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1225 c22250R_68_1 (by norm_num)

theorem hr22250R_68 : rows2 68 69 ≤ 111354452906087 := rows2_le_of_rowsJ2 68 69 c22250R_68_0

theorem c22250R_69_44 : rowsJ2 69 70 68 340 ≤ 4266422846841 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1315 rows22250R_1316 (by norm_num)

theorem c22250R_69_43 : rowsJ2 69 70 67 340 ≤ 6857187043122 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1314 c22250R_69_44 (by norm_num)

theorem c22250R_69_42 : rowsJ2 69 70 66 340 ≤ 9812698480573 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1313 c22250R_69_43 (by norm_num)

theorem c22250R_69_41 : rowsJ2 69 70 65 340 ≤ 13135797352311 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1312 c22250R_69_42 (by norm_num)

theorem c22250R_69_40 : rowsJ2 69 70 64 340 ≤ 16816503408243 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1311 c22250R_69_41 (by norm_num)

theorem c22250R_69_39 : rowsJ2 69 70 63 340 ≤ 20857933891577 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1310 c22250R_69_40 (by norm_num)

theorem c22250R_69_38 : rowsJ2 69 70 62 340 ≤ 25250745535759 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1309 c22250R_69_39 (by norm_num)

theorem c22250R_69_37 : rowsJ2 69 70 61 340 ≤ 29998327437874 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1308 c22250R_69_38 (by norm_num)

theorem c22250R_69_36 : rowsJ2 69 70 60 340 ≤ 35091948571520 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1307 c22250R_69_37 (by norm_num)

theorem c22250R_69_35 : rowsJ2 69 70 59 340 ≤ 40535267055977 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1306 c22250R_69_36 (by norm_num)

theorem c22250R_69_34 : rowsJ2 69 70 58 340 ≤ 46320142833018 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1305 c22250R_69_35 (by norm_num)

theorem c22250R_69_33 : rowsJ2 69 70 57 340 ≤ 52450502511629 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1304 c22250R_69_34 (by norm_num)

theorem c22250R_69_32 : rowsJ2 69 70 56 340 ≤ 58983071056915 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1303 c22250R_69_33 (by norm_num)

theorem c22250R_69_31 : rowsJ2 69 70 55 340 ≤ 65922568051688 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1302 c22250R_69_32 (by norm_num)

theorem c22250R_69_30 : rowsJ2 69 70 54 340 ≤ 72390055317642 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1301 c22250R_69_31 (by norm_num)

theorem c22250R_69_29 : rowsJ2 69 70 53 340 ≤ 78350294279896 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1300 c22250R_69_30 (by norm_num)

theorem c22250R_69_28 : rowsJ2 69 70 52 340 ≤ 83819402805133 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1299 c22250R_69_29 (by norm_num)

theorem c22250R_69_27 : rowsJ2 69 70 51 340 ≤ 88633544435413 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1298 c22250R_69_28 (by norm_num)

theorem c22250R_69_26 : rowsJ2 69 70 50 340 ≤ 92548820131572 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1297 c22250R_69_27 (by norm_num)

theorem c22250R_69_25 : rowsJ2 69 70 49 340 ≤ 95537448392289 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1296 c22250R_69_26 (by norm_num)

theorem c22250R_69_24 : rowsJ2 69 70 48 340 ≤ 97722442991740 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1295 c22250R_69_25 (by norm_num)

theorem c22250R_69_23 : rowsJ2 69 70 47 340 ≤ 99201138905853 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1294 c22250R_69_24 (by norm_num)

theorem c22250R_69_22 : rowsJ2 69 70 46 340 ≤ 99945756940326 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1293 c22250R_69_23 (by norm_num)

theorem c22250R_69_21 : rowsJ2 69 70 45 340 ≤ 100195348293914 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1292 c22250R_69_22 (by norm_num)

theorem c22250R_69_20 : rowsJ2 69 70 44 340 ≤ 100258938409668 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1291 c22250R_69_21 (by norm_num)

theorem c22250R_69_19 : rowsJ2 69 70 43 340 ≤ 100258938409668 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1290 c22250R_69_20 (by norm_num)

theorem c22250R_69_18 : rowsJ2 69 70 41 340 ≤ 100258938409668 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1289 c22250R_69_19 (by norm_num)

theorem c22250R_69_17 : rowsJ2 69 70 39 340 ≤ 100258938409668 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1288 c22250R_69_18 (by norm_num)

theorem c22250R_69_16 : rowsJ2 69 70 37 340 ≤ 100258938409668 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1287 c22250R_69_17 (by norm_num)

theorem c22250R_69_15 : rowsJ2 69 70 35 340 ≤ 100258938409668 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1286 c22250R_69_16 (by norm_num)

theorem c22250R_69_14 : rowsJ2 69 70 33 340 ≤ 100258938409668 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1285 c22250R_69_15 (by norm_num)

theorem c22250R_69_13 : rowsJ2 69 70 32 340 ≤ 100258938409668 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1284 c22250R_69_14 (by norm_num)

theorem c22250R_69_12 : rowsJ2 69 70 31 340 ≤ 100258938409668 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1283 c22250R_69_13 (by norm_num)

theorem c22250R_69_11 : rowsJ2 69 70 30 340 ≤ 100258938409668 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1282 c22250R_69_12 (by norm_num)

theorem c22250R_69_10 : rowsJ2 69 70 29 340 ≤ 100258938409668 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1281 c22250R_69_11 (by norm_num)

theorem c22250R_69_9 : rowsJ2 69 70 28 340 ≤ 100258938409668 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1280 c22250R_69_10 (by norm_num)

theorem c22250R_69_8 : rowsJ2 69 70 27 340 ≤ 100258938409668 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1279 c22250R_69_9 (by norm_num)

theorem c22250R_69_7 : rowsJ2 69 70 26 340 ≤ 100258938409668 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1278 c22250R_69_8 (by norm_num)

theorem c22250R_69_6 : rowsJ2 69 70 25 340 ≤ 100258938409668 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1277 c22250R_69_7 (by norm_num)

theorem c22250R_69_5 : rowsJ2 69 70 24 340 ≤ 100258938409668 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1276 c22250R_69_6 (by norm_num)

theorem c22250R_69_4 : rowsJ2 69 70 23 340 ≤ 100258938409668 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1275 c22250R_69_5 (by norm_num)

theorem c22250R_69_3 : rowsJ2 69 70 22 340 ≤ 100258938409668 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1274 c22250R_69_4 (by norm_num)

theorem c22250R_69_2 : rowsJ2 69 70 21 340 ≤ 100258938409668 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1273 c22250R_69_3 (by norm_num)

theorem c22250R_69_1 : rowsJ2 69 70 18 340 ≤ 100258938409668 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1272 c22250R_69_2 (by norm_num)

theorem c22250R_69_0 : rowsJ2 69 70 0 340 ≤ 101247714290956 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1271 c22250R_69_1 (by norm_num)

theorem hr22250R_69 : rows2 69 70 ≤ 101247714290956 := rows2_le_of_rowsJ2 69 70 c22250R_69_0

theorem c22250R_70_44 : rowsJ2 70 71 69 340 ≤ 2686209619553 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1361 rows22250R_1362 (by norm_num)

theorem c22250R_70_43 : rowsJ2 70 71 68 340 ≤ 4396282011364 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1360 c22250R_70_44 (by norm_num)

theorem c22250R_70_42 : rowsJ2 70 71 67 340 ≤ 6410890373992 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1359 c22250R_70_43 (by norm_num)

theorem c22250R_70_41 : rowsJ2 70 71 66 340 ≤ 8732243345554 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1358 c22250R_70_42 (by norm_num)

theorem c22250R_70_40 : rowsJ2 70 71 65 340 ≤ 11419324520439 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1357 c22250R_70_41 (by norm_num)

theorem c22250R_70_39 : rowsJ2 70 71 64 340 ≤ 14406862812961 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1356 c22250R_70_40 (by norm_num)

theorem c22250R_70_38 : rowsJ2 70 71 63 340 ≤ 17753196404468 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1355 c22250R_70_39 (by norm_num)

theorem c22250R_70_37 : rowsJ2 70 71 62 340 ≤ 21394517389202 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1354 c22250R_70_38 (by norm_num)

theorem c22250R_70_36 : rowsJ2 70 71 61 340 ≤ 25388566193009 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1353 c22250R_70_37 (by norm_num)

theorem c22250R_70_35 : rowsJ2 70 71 60 340 ≤ 29672922751109 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1352 c22250R_70_36 (by norm_num)

theorem c22250R_70_34 : rowsJ2 70 71 59 340 ≤ 34304777787723 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1351 c22250R_70_35 (by norm_num)

theorem c22250R_70_33 : rowsJ2 70 71 58 340 ≤ 39223028672848 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1350 c22250R_70_34 (by norm_num)

theorem c22250R_70_32 : rowsJ2 70 71 57 340 ≤ 44484364989443 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1349 c22250R_70_33 (by norm_num)

theorem c22250R_70_31 : rowsJ2 70 71 56 340 ≤ 50092678402258 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1348 c22250R_70_32 (by norm_num)

theorem c22250R_70_30 : rowsJ2 70 71 55 340 ≤ 56104724837110 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1347 c22250R_70_31 (by norm_num)

theorem c22250R_70_29 : rowsJ2 70 71 54 340 ≤ 62087534537755 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1346 c22250R_70_30 (by norm_num)

theorem c22250R_70_28 : rowsJ2 70 71 53 340 ≤ 67678820022539 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1345 c22250R_70_29 (by norm_num)

theorem c22250R_70_27 : rowsJ2 70 71 52 340 ≤ 72840788492612 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1344 c22250R_70_28 (by norm_num)

theorem c22250R_70_26 : rowsJ2 70 71 51 340 ≤ 77459343520289 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1343 c22250R_70_27 (by norm_num)

theorem c22250R_70_25 : rowsJ2 70 71 50 340 ≤ 81239864612404 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1342 c22250R_70_26 (by norm_num)

theorem c22250R_70_24 : rowsJ2 70 71 49 340 ≤ 84202956058220 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1341 c22250R_70_25 (by norm_num)

theorem c22250R_70_23 : rowsJ2 70 71 48 340 ≤ 86369280619855 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1340 c22250R_70_24 (by norm_num)

theorem c22250R_70_22 : rowsJ2 70 71 47 340 ≤ 87835341578881 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1339 c22250R_70_23 (by norm_num)

theorem c22250R_70_21 : rowsJ2 70 71 46 340 ≤ 88573597104786 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1338 c22250R_70_22 (by norm_num)

theorem c22250R_70_20 : rowsJ2 70 71 45 340 ≤ 88821055784907 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1337 c22250R_70_21 (by norm_num)

theorem c22250R_70_19 : rowsJ2 70 71 44 340 ≤ 88884102544689 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1336 c22250R_70_20 (by norm_num)

theorem c22250R_70_18 : rowsJ2 70 71 43 340 ≤ 88884102544689 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1335 c22250R_70_19 (by norm_num)

theorem c22250R_70_17 : rowsJ2 70 71 41 340 ≤ 88884102544689 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1334 c22250R_70_18 (by norm_num)

theorem c22250R_70_16 : rowsJ2 70 71 39 340 ≤ 88884102544689 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1333 c22250R_70_17 (by norm_num)

theorem c22250R_70_15 : rowsJ2 70 71 37 340 ≤ 88884102544689 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1332 c22250R_70_16 (by norm_num)

theorem c22250R_70_14 : rowsJ2 70 71 35 340 ≤ 88884102544689 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1331 c22250R_70_15 (by norm_num)

theorem c22250R_70_13 : rowsJ2 70 71 33 340 ≤ 88884102544689 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1330 c22250R_70_14 (by norm_num)

theorem c22250R_70_12 : rowsJ2 70 71 31 340 ≤ 88884102544689 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1329 c22250R_70_13 (by norm_num)

theorem c22250R_70_11 : rowsJ2 70 71 30 340 ≤ 88884102544689 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1328 c22250R_70_12 (by norm_num)

theorem c22250R_70_10 : rowsJ2 70 71 29 340 ≤ 88884102544689 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1327 c22250R_70_11 (by norm_num)

theorem c22250R_70_9 : rowsJ2 70 71 28 340 ≤ 88884102544689 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1326 c22250R_70_10 (by norm_num)

theorem c22250R_70_8 : rowsJ2 70 71 27 340 ≤ 88884102544689 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1325 c22250R_70_9 (by norm_num)

theorem c22250R_70_7 : rowsJ2 70 71 26 340 ≤ 88884102544689 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1324 c22250R_70_8 (by norm_num)

theorem c22250R_70_6 : rowsJ2 70 71 25 340 ≤ 88884102544689 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1323 c22250R_70_7 (by norm_num)

theorem c22250R_70_5 : rowsJ2 70 71 24 340 ≤ 88884102544689 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1322 c22250R_70_6 (by norm_num)

theorem c22250R_70_4 : rowsJ2 70 71 23 340 ≤ 88884102544689 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1321 c22250R_70_5 (by norm_num)

theorem c22250R_70_3 : rowsJ2 70 71 22 340 ≤ 88884102544689 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1320 c22250R_70_4 (by norm_num)

theorem c22250R_70_2 : rowsJ2 70 71 21 340 ≤ 88884102544689 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1319 c22250R_70_3 (by norm_num)

theorem c22250R_70_1 : rowsJ2 70 71 18 340 ≤ 88884102544689 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1318 c22250R_70_2 (by norm_num)

theorem c22250R_70_0 : rowsJ2 70 71 0 340 ≤ 89739080517259 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1317 c22250R_70_1 (by norm_num)

theorem hr22250R_70 : rows2 70 71 ≤ 89739080517259 := rows2_le_of_rowsJ2 70 71 c22250R_70_0

theorem c22250R_71_45 : rowsJ2 71 72 70 340 ≤ 1349773800330 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1408 rows22250R_1409 (by norm_num)

theorem c22250R_71_44 : rowsJ2 71 72 69 340 ≤ 2301149854244 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1407 c22250R_71_45 (by norm_num)

theorem c22250R_71_43 : rowsJ2 71 72 68 340 ≤ 3497036064139 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1406 c22250R_71_44 (by norm_num)

theorem c22250R_71_42 : rowsJ2 71 72 67 340 ≤ 4939059464957 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1405 c22250R_71_43 (by norm_num)

theorem c22250R_71_41 : rowsJ2 71 72 66 340 ≤ 6686560574559 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1404 c22250R_71_42 (by norm_num)

theorem c22250R_71_40 : rowsJ2 71 72 65 340 ≤ 8741741216431 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1403 c22250R_71_41 (by norm_num)

theorem c22250R_71_39 : rowsJ2 71 72 64 340 ≤ 11096067152581 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1402 c22250R_71_40 (by norm_num)

theorem c22250R_71_38 : rowsJ2 71 72 63 340 ≤ 13751975673019 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1401 c22250R_71_39 (by norm_num)

theorem c22250R_71_37 : rowsJ2 71 72 62 340 ≤ 16701471541270 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1400 c22250R_71_38 (by norm_num)

theorem c22250R_71_36 : rowsJ2 71 72 61 340 ≤ 19947222200067 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1399 c22250R_71_37 (by norm_num)

theorem c22250R_71_35 : rowsJ2 71 72 60 340 ≤ 23481749561310 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1398 c22250R_71_36 (by norm_num)

theorem c22250R_71_34 : rowsJ2 71 72 59 340 ≤ 27307947935524 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1397 c22250R_71_35 (by norm_num)

theorem c22250R_71_33 : rowsJ2 71 72 58 340 ≤ 31418837497354 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1396 c22250R_71_34 (by norm_num)

theorem c22250R_71_32 : rowsJ2 71 72 57 340 ≤ 35817538101707 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1395 c22250R_71_33 (by norm_num)

theorem c22250R_71_31 : rowsJ2 71 72 56 340 ≤ 40560754734705 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1394 c22250R_71_32 (by norm_num)

theorem c22250R_71_30 : rowsJ2 71 72 55 340 ≤ 45652347286880 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1393 c22250R_71_31 (by norm_num)

theorem c22250R_71_29 : rowsJ2 71 72 54 340 ≤ 51149114752460 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1392 c22250R_71_30 (by norm_num)

theorem c22250R_71_28 : rowsJ2 71 72 53 340 ≤ 56319073449693 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1391 c22250R_71_29 (by norm_num)

theorem c22250R_71_27 : rowsJ2 71 72 52 340 ≤ 61173461868612 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1390 c22250R_71_28 (by norm_num)

theorem c22250R_71_26 : rowsJ2 71 72 51 340 ≤ 65545410871619 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1389 c22250R_71_27 (by norm_num)

theorem c22250R_71_25 : rowsJ2 71 72 50 340 ≤ 69191324327254 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1388 c22250R_71_26 (by norm_num)

theorem c22250R_71_24 : rowsJ2 71 72 49 340 ≤ 72078836214697 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1387 c22250R_71_25 (by norm_num)

theorem c22250R_71_23 : rowsJ2 71 72 48 340 ≤ 74226807093651 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1386 c22250R_71_24 (by norm_num)

theorem c22250R_71_22 : rowsJ2 71 72 47 340 ≤ 75680447191046 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1385 c22250R_71_23 (by norm_num)

theorem c22250R_71_21 : rowsJ2 71 72 46 340 ≤ 76412448018142 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1384 c22250R_71_22 (by norm_num)

theorem c22250R_71_20 : rowsJ2 71 72 45 340 ≤ 76657810161957 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1383 c22250R_71_21 (by norm_num)

theorem c22250R_71_19 : rowsJ2 71 72 44 340 ≤ 76720322772681 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1382 c22250R_71_20 (by norm_num)

theorem c22250R_71_18 : rowsJ2 71 72 43 340 ≤ 76720322772681 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1381 c22250R_71_19 (by norm_num)

theorem c22250R_71_17 : rowsJ2 71 72 42 340 ≤ 76720322772681 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1380 c22250R_71_18 (by norm_num)

theorem c22250R_71_16 : rowsJ2 71 72 40 340 ≤ 76720322772681 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1379 c22250R_71_17 (by norm_num)

theorem c22250R_71_15 : rowsJ2 71 72 38 340 ≤ 76720322772681 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1378 c22250R_71_16 (by norm_num)

theorem c22250R_71_14 : rowsJ2 71 72 36 340 ≤ 76720322772681 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1377 c22250R_71_15 (by norm_num)

theorem c22250R_71_13 : rowsJ2 71 72 34 340 ≤ 76720322772681 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1376 c22250R_71_14 (by norm_num)

theorem c22250R_71_12 : rowsJ2 71 72 32 340 ≤ 76720322772681 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1375 c22250R_71_13 (by norm_num)

theorem c22250R_71_11 : rowsJ2 71 72 30 340 ≤ 76720322772681 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1374 c22250R_71_12 (by norm_num)

theorem c22250R_71_10 : rowsJ2 71 72 29 340 ≤ 76720322772681 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1373 c22250R_71_11 (by norm_num)

theorem c22250R_71_9 : rowsJ2 71 72 28 340 ≤ 76720322772681 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1372 c22250R_71_10 (by norm_num)

theorem c22250R_71_8 : rowsJ2 71 72 27 340 ≤ 76720322772681 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1371 c22250R_71_9 (by norm_num)

theorem c22250R_71_7 : rowsJ2 71 72 26 340 ≤ 76720322772681 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1370 c22250R_71_8 (by norm_num)

theorem c22250R_71_6 : rowsJ2 71 72 25 340 ≤ 76720322772681 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1369 c22250R_71_7 (by norm_num)

theorem c22250R_71_5 : rowsJ2 71 72 24 340 ≤ 76720322772681 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1368 c22250R_71_6 (by norm_num)

theorem c22250R_71_4 : rowsJ2 71 72 23 340 ≤ 76720322772681 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1367 c22250R_71_5 (by norm_num)

theorem c22250R_71_3 : rowsJ2 71 72 22 340 ≤ 76720322772681 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1366 c22250R_71_4 (by norm_num)

theorem c22250R_71_2 : rowsJ2 71 72 21 340 ≤ 76720322772681 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1365 c22250R_71_3 (by norm_num)

theorem c22250R_71_1 : rowsJ2 71 72 18 340 ≤ 76720322772681 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1364 c22250R_71_2 (by norm_num)

theorem c22250R_71_0 : rowsJ2 71 72 0 340 ≤ 77458379766238 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1363 c22250R_71_1 (by norm_num)

theorem hr22250R_71 : rows2 71 72 ≤ 77458379766238 := rows2_le_of_rowsJ2 71 72 c22250R_71_0

theorem c22250R_72_45 : rowsJ2 72 73 71 340 ≤ 390204061451 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1455 rows22250R_1456 (by norm_num)

theorem c22250R_72_44 : rowsJ2 72 73 70 340 ≤ 773162824987 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1454 c22250R_72_45 (by norm_num)

theorem c22250R_72_43 : rowsJ2 72 73 69 340 ≤ 1340443181691 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1453 c22250R_72_44 (by norm_num)

theorem c22250R_72_42 : rowsJ2 72 73 68 340 ≤ 2093154916391 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1452 c22250R_72_43 (by norm_num)

theorem c22250R_72_41 : rowsJ2 72 73 67 340 ≤ 3091108632850 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1451 c22250R_72_42 (by norm_num)

theorem c22250R_72_40 : rowsJ2 72 73 66 340 ≤ 4335927201549 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1450 c22250R_72_41 (by norm_num)

theorem c22250R_72_39 : rowsJ2 72 73 65 340 ≤ 5886975056564 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1449 c22250R_72_40 (by norm_num)

theorem c22250R_72_38 : rowsJ2 72 73 64 340 ≤ 7679491271956 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1448 c22250R_72_39 (by norm_num)

theorem c22250R_72_37 : rowsJ2 72 73 63 340 ≤ 9772114981434 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1447 c22250R_72_38 (by norm_num)

theorem c22250R_72_36 : rowsJ2 72 73 62 340 ≤ 12101486075798 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1446 c22250R_72_37 (by norm_num)

theorem c22250R_72_35 : rowsJ2 72 73 61 340 ≤ 14725568174092 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1445 c22250R_72_36 (by norm_num)

theorem c22250R_72_34 : rowsJ2 72 73 60 340 ≤ 17582327705261 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1444 c22250R_72_35 (by norm_num)

theorem c22250R_72_33 : rowsJ2 72 73 59 340 ≤ 20729102483328 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1443 c22250R_72_34 (by norm_num)

theorem c22250R_72_32 : rowsJ2 72 73 58 340 ≤ 24105115741224 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1442 c22250R_72_33 (by norm_num)

theorem c22250R_72_31 : rowsJ2 72 73 57 340 ≤ 27767129241557 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1441 c22250R_72_32 (by norm_num)

theorem c22250R_72_30 : rowsJ2 72 73 56 340 ≤ 31718229151262 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1440 c22250R_72_31 (by norm_num)

theorem c22250R_72_29 : rowsJ2 72 73 55 340 ≤ 36015160692283 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1439 c22250R_72_30 (by norm_num)

theorem c22250R_72_28 : rowsJ2 72 73 54 340 ≤ 40661768062895 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1438 c22250R_72_29 (by norm_num)

theorem c22250R_72_27 : rowsJ2 72 73 53 340 ≤ 45409187598321 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1437 c22250R_72_28 (by norm_num)

theorem c22250R_72_26 : rowsJ2 72 73 52 340 ≤ 49903683008028 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1436 c22250R_72_27 (by norm_num)

theorem c22250R_72_25 : rowsJ2 72 73 51 340 ≤ 54028697404908 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1435 c22250R_72_26 (by norm_num)

theorem c22250R_72_24 : rowsJ2 72 73 50 340 ≤ 57488962324972 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1434 c22250R_72_25 (by norm_num)

theorem c22250R_72_23 : rowsJ2 72 73 49 340 ≤ 60301105656232 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1433 c22250R_72_24 (by norm_num)

theorem c22250R_72_22 : rowsJ2 72 73 48 340 ≤ 62431031234456 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1432 c22250R_72_23 (by norm_num)

theorem c22250R_72_21 : rowsJ2 72 73 47 340 ≤ 63872459167817 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1431 c22250R_72_22 (by norm_num)

theorem c22250R_72_20 : rowsJ2 72 73 46 340 ≤ 64598310388701 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1430 c22250R_72_21 (by norm_num)

theorem c22250R_72_19 : rowsJ2 72 73 45 340 ≤ 64841611222600 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1429 c22250R_72_20 (by norm_num)

theorem c22250R_72_18 : rowsJ2 72 73 44 340 ≤ 64903598659137 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1428 c22250R_72_19 (by norm_num)

theorem c22250R_72_17 : rowsJ2 72 73 43 340 ≤ 64903598659137 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1427 c22250R_72_18 (by norm_num)

theorem c22250R_72_16 : rowsJ2 72 73 41 340 ≤ 64903598659137 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1426 c22250R_72_17 (by norm_num)

theorem c22250R_72_15 : rowsJ2 72 73 39 340 ≤ 64903598659137 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1425 c22250R_72_16 (by norm_num)

theorem c22250R_72_14 : rowsJ2 72 73 37 340 ≤ 64903598659137 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1424 c22250R_72_15 (by norm_num)

theorem c22250R_72_13 : rowsJ2 72 73 35 340 ≤ 64903598659137 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1423 c22250R_72_14 (by norm_num)

theorem c22250R_72_12 : rowsJ2 72 73 33 340 ≤ 64903598659137 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1422 c22250R_72_13 (by norm_num)

theorem c22250R_72_11 : rowsJ2 72 73 31 340 ≤ 64903598659137 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1421 c22250R_72_12 (by norm_num)

theorem c22250R_72_10 : rowsJ2 72 73 29 340 ≤ 64903598659137 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1420 c22250R_72_11 (by norm_num)

theorem c22250R_72_9 : rowsJ2 72 73 28 340 ≤ 64903598659137 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1419 c22250R_72_10 (by norm_num)

theorem c22250R_72_8 : rowsJ2 72 73 27 340 ≤ 64903598659137 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1418 c22250R_72_9 (by norm_num)

theorem c22250R_72_7 : rowsJ2 72 73 26 340 ≤ 64903598659137 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1417 c22250R_72_8 (by norm_num)

theorem c22250R_72_6 : rowsJ2 72 73 25 340 ≤ 64903598659137 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1416 c22250R_72_7 (by norm_num)

theorem c22250R_72_5 : rowsJ2 72 73 24 340 ≤ 64903598659137 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1415 c22250R_72_6 (by norm_num)

theorem c22250R_72_4 : rowsJ2 72 73 23 340 ≤ 64903598659137 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1414 c22250R_72_5 (by norm_num)

theorem c22250R_72_3 : rowsJ2 72 73 22 340 ≤ 64903598659137 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1413 c22250R_72_4 (by norm_num)

theorem c22250R_72_2 : rowsJ2 72 73 20 340 ≤ 64903598659137 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1412 c22250R_72_3 (by norm_num)

theorem c22250R_72_1 : rowsJ2 72 73 18 340 ≤ 64903598659137 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1411 c22250R_72_2 (by norm_num)

theorem c22250R_72_0 : rowsJ2 72 73 0 340 ≤ 65532987936197 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1410 c22250R_72_1 (by norm_num)

theorem hr22250R_72 : rows2 72 73 ≤ 65532987936197 := rows2_le_of_rowsJ2 72 73 c22250R_72_0

theorem c22250R_73_45 : rowsJ2 73 74 71 340 ≤ 64788357587 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1502 rows22250R_1503 (by norm_num)

theorem c22250R_73_44 : rowsJ2 73 74 70 340 ≤ 192352789999 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1501 c22250R_73_45 (by norm_num)

theorem c22250R_73_43 : rowsJ2 73 74 69 340 ≤ 444348439579 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1500 c22250R_73_44 (by norm_num)

theorem c22250R_73_42 : rowsJ2 73 74 68 340 ≤ 881172042690 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1499 c22250R_73_43 (by norm_num)

theorem c22250R_73_41 : rowsJ2 73 74 67 340 ≤ 1503932717053 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1498 c22250R_73_42 (by norm_num)

theorem c22250R_73_40 : rowsJ2 73 74 66 340 ≤ 2372467876699 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1497 c22250R_73_41 (by norm_num)

theorem c22250R_73_39 : rowsJ2 73 74 65 340 ≤ 3488412216420 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1496 c22250R_73_40 (by norm_num)

theorem c22250R_73_38 : rowsJ2 73 74 64 340 ≤ 4844764179619 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1495 c22250R_73_39 (by norm_num)

theorem c22250R_73_37 : rowsJ2 73 74 63 340 ≤ 6443350873630 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1494 c22250R_73_38 (by norm_num)

theorem c22250R_73_36 : rowsJ2 73 74 62 340 ≤ 8277609095791 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1493 c22250R_73_37 (by norm_num)

theorem c22250R_73_35 : rowsJ2 73 74 61 340 ≤ 10349553318613 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1492 c22250R_73_36 (by norm_num)

theorem c22250R_73_34 : rowsJ2 73 74 60 340 ≤ 12653040200059 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1491 c22250R_73_35 (by norm_num)

theorem c22250R_73_33 : rowsJ2 73 74 59 340 ≤ 15190268205917 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1490 c22250R_73_34 (by norm_num)

theorem c22250R_73_32 : rowsJ2 73 74 58 340 ≤ 17955497801880 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1489 c22250R_73_33 (by norm_num)

theorem c22250R_73_31 : rowsJ2 73 74 57 340 ≤ 20951109685965 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1488 c22250R_73_32 (by norm_num)

theorem c22250R_73_30 : rowsJ2 73 74 56 340 ≤ 24233903905942 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1487 c22250R_73_31 (by norm_num)

theorem c22250R_73_29 : rowsJ2 73 74 55 340 ≤ 27806948530153 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1486 c22250R_73_30 (by norm_num)

theorem c22250R_73_28 : rowsJ2 73 74 54 340 ≤ 31727053542230 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1485 c22250R_73_29 (by norm_num)

theorem c22250R_73_27 : rowsJ2 73 74 53 340 ≤ 35998063202921 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1484 c22250R_73_28 (by norm_num)

theorem c22250R_73_26 : rowsJ2 73 74 52 340 ≤ 40131627514275 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1483 c22250R_73_27 (by norm_num)

theorem c22250R_73_25 : rowsJ2 73 74 51 340 ≤ 43957450004627 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1482 c22250R_73_26 (by norm_num)

theorem c22250R_73_24 : rowsJ2 73 74 50 340 ≤ 47231836599041 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1481 c22250R_73_25 (by norm_num)

theorem c22250R_73_23 : rowsJ2 73 74 49 340 ≤ 49917565584255 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1480 c22250R_73_24 (by norm_num)

theorem c22250R_73_22 : rowsJ2 73 74 48 340 ≤ 52029746536212 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1479 c22250R_73_23 (by norm_num)

theorem c22250R_73_21 : rowsJ2 73 74 47 340 ≤ 53459165787096 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1478 c22250R_73_22 (by norm_num)

theorem c22250R_73_20 : rowsJ2 73 74 46 340 ≤ 54178969867755 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1477 c22250R_73_21 (by norm_num)

theorem c22250R_73_19 : rowsJ2 73 74 45 340 ≤ 54420243737702 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1476 c22250R_73_20 (by norm_num)

theorem c22250R_73_18 : rowsJ2 73 74 44 340 ≤ 54481714750611 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1475 c22250R_73_19 (by norm_num)

theorem c22250R_73_17 : rowsJ2 73 74 43 340 ≤ 54481714750611 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1474 c22250R_73_18 (by norm_num)

theorem c22250R_73_16 : rowsJ2 73 74 42 340 ≤ 54481714750611 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1473 c22250R_73_17 (by norm_num)

theorem c22250R_73_15 : rowsJ2 73 74 41 340 ≤ 54481714750611 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1472 c22250R_73_16 (by norm_num)

theorem c22250R_73_14 : rowsJ2 73 74 39 340 ≤ 54481714750611 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1471 c22250R_73_15 (by norm_num)

theorem c22250R_73_13 : rowsJ2 73 74 37 340 ≤ 54481714750611 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1470 c22250R_73_14 (by norm_num)

theorem c22250R_73_12 : rowsJ2 73 74 34 340 ≤ 54481714750611 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1469 c22250R_73_13 (by norm_num)

theorem c22250R_73_11 : rowsJ2 73 74 32 340 ≤ 54481714750611 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1468 c22250R_73_12 (by norm_num)

theorem c22250R_73_10 : rowsJ2 73 74 30 340 ≤ 54481714750611 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1467 c22250R_73_11 (by norm_num)

theorem c22250R_73_9 : rowsJ2 73 74 28 340 ≤ 54481714750611 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1466 c22250R_73_10 (by norm_num)

theorem c22250R_73_8 : rowsJ2 73 74 27 340 ≤ 54481714750611 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1465 c22250R_73_9 (by norm_num)

theorem c22250R_73_7 : rowsJ2 73 74 26 340 ≤ 54481714750611 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1464 c22250R_73_8 (by norm_num)

theorem c22250R_73_6 : rowsJ2 73 74 25 340 ≤ 54481714750611 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1463 c22250R_73_7 (by norm_num)

theorem c22250R_73_5 : rowsJ2 73 74 24 340 ≤ 54481714750611 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1462 c22250R_73_6 (by norm_num)

theorem c22250R_73_4 : rowsJ2 73 74 23 340 ≤ 54481714750611 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1461 c22250R_73_5 (by norm_num)

theorem c22250R_73_3 : rowsJ2 73 74 22 340 ≤ 54481714750611 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1460 c22250R_73_4 (by norm_num)

theorem c22250R_73_2 : rowsJ2 73 74 20 340 ≤ 54481714750611 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1459 c22250R_73_3 (by norm_num)

theorem c22250R_73_1 : rowsJ2 73 74 18 340 ≤ 54481714750611 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1458 c22250R_73_2 (by norm_num)

theorem c22250R_73_0 : rowsJ2 73 74 0 340 ≤ 55010723196491 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1457 c22250R_73_1 (by norm_num)

theorem hr22250R_73 : rows2 73 74 ≤ 55010723196491 := rows2_le_of_rowsJ2 73 74 c22250R_73_0

theorem c22250R_74_44 : rowsJ2 74 75 71 340 ≤ 0 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1548 rows22250R_1549 (by norm_num)

theorem c22250R_74_43 : rowsJ2 74 75 70 340 ≤ 0 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1547 c22250R_74_44 (by norm_num)

theorem c22250R_74_42 : rowsJ2 74 75 69 340 ≤ 63027374706 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1546 c22250R_74_43 (by norm_num)

theorem c22250R_74_41 : rowsJ2 74 75 68 340 ≤ 250753897788 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1545 c22250R_74_42 (by norm_num)

theorem c22250R_74_40 : rowsJ2 74 75 67 340 ≤ 623606901775 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1544 c22250R_74_41 (by norm_num)

theorem c22250R_74_39 : rowsJ2 74 75 66 340 ≤ 1182710467907 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1543 c22250R_74_40 (by norm_num)

theorem c22250R_74_38 : rowsJ2 74 75 65 340 ≤ 1987952891835 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1542 c22250R_74_39 (by norm_num)

theorem c22250R_74_37 : rowsJ2 74 75 64 340 ≤ 2975130479502 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1541 c22250R_74_38 (by norm_num)

theorem c22250R_74_36 : rowsJ2 74 75 63 340 ≤ 4203322071368 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1540 c22250R_74_37 (by norm_num)

theorem c22250R_74_35 : rowsJ2 74 75 62 340 ≤ 5609661293081 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1539 c22250R_74_36 (by norm_num)

theorem c22250R_74_34 : rowsJ2 74 75 61 340 ≤ 7252470060274 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1538 c22250R_74_35 (by norm_num)

theorem c22250R_74_33 : rowsJ2 74 75 60 340 ≤ 9070146518426 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1537 c22250R_74_34 (by norm_num)

theorem c22250R_74_32 : rowsJ2 74 75 59 340 ≤ 11120307605952 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1536 c22250R_74_33 (by norm_num)

theorem c22250R_74_31 : rowsJ2 74 75 58 340 ≤ 13342547324928 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1535 c22250R_74_32 (by norm_num)

theorem c22250R_74_30 : rowsJ2 74 75 57 340 ≤ 15793829138045 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1534 c22250R_74_31 (by norm_num)

theorem c22250R_74_29 : rowsJ2 74 75 56 340 ≤ 18476514084889 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1533 c22250R_74_30 (by norm_num)

theorem c22250R_74_28 : rowsJ2 74 75 55 340 ≤ 21447464511116 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1532 c22250R_74_29 (by norm_num)

theorem c22250R_74_27 : rowsJ2 74 75 54 340 ≤ 24709745625523 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1531 c22250R_74_28 (by norm_num)

theorem c22250R_74_26 : rowsJ2 74 75 53 340 ≤ 28320256465647 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1530 c22250R_74_27 (by norm_num)

theorem c22250R_74_25 : rowsJ2 74 75 52 340 ≤ 32039140571968 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1529 c22250R_74_26 (by norm_num)

theorem c22250R_74_24 : rowsJ2 74 75 51 340 ≤ 35564910377597 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1528 c22250R_74_25 (by norm_num)

theorem c22250R_74_23 : rowsJ2 74 75 50 340 ≤ 38601194366237 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1527 c22250R_74_24 (by norm_num)

theorem c22250R_74_22 : rowsJ2 74 75 49 340 ≤ 41160402183166 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1526 c22250R_74_23 (by norm_num)

theorem c22250R_74_21 : rowsJ2 74 75 48 340 ≤ 43203802567341 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1525 c22250R_74_22 (by norm_num)

theorem c22250R_74_20 : rowsJ2 74 75 47 340 ≤ 44621411573649 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1524 c22250R_74_21 (by norm_num)

theorem c22250R_74_19 : rowsJ2 74 75 46 340 ≤ 45335268440266 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1523 c22250R_74_20 (by norm_num)

theorem c22250R_74_18 : rowsJ2 74 75 45 340 ≤ 45574548840898 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1522 c22250R_74_19 (by norm_num)

theorem c22250R_74_17 : rowsJ2 74 75 44 340 ≤ 45635511963839 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1521 c22250R_74_18 (by norm_num)

theorem c22250R_74_16 : rowsJ2 74 75 43 340 ≤ 45635511963839 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1520 c22250R_74_17 (by norm_num)

theorem c22250R_74_15 : rowsJ2 74 75 42 340 ≤ 45635511963839 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1519 c22250R_74_16 (by norm_num)

theorem c22250R_74_14 : rowsJ2 74 75 41 340 ≤ 45635511963839 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1518 c22250R_74_15 (by norm_num)

theorem c22250R_74_13 : rowsJ2 74 75 39 340 ≤ 45635511963839 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1517 c22250R_74_14 (by norm_num)

theorem c22250R_74_12 : rowsJ2 74 75 36 340 ≤ 45635511963839 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1516 c22250R_74_13 (by norm_num)

theorem c22250R_74_11 : rowsJ2 74 75 33 340 ≤ 45635511963839 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1515 c22250R_74_12 (by norm_num)

theorem c22250R_74_10 : rowsJ2 74 75 31 340 ≤ 45635511963839 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1514 c22250R_74_11 (by norm_num)

theorem c22250R_74_9 : rowsJ2 74 75 29 340 ≤ 45635511963839 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1513 c22250R_74_10 (by norm_num)

theorem c22250R_74_8 : rowsJ2 74 75 27 340 ≤ 45635511963839 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1512 c22250R_74_9 (by norm_num)

theorem c22250R_74_7 : rowsJ2 74 75 26 340 ≤ 45635511963839 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1511 c22250R_74_8 (by norm_num)

theorem c22250R_74_6 : rowsJ2 74 75 25 340 ≤ 45636577520448 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1510 c22250R_74_7 (by norm_num)

theorem c22250R_74_5 : rowsJ2 74 75 24 340 ≤ 45637641202867 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1509 c22250R_74_6 (by norm_num)

theorem c22250R_74_4 : rowsJ2 74 75 23 340 ≤ 45639765505977 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1508 c22250R_74_5 (by norm_num)

theorem c22250R_74_3 : rowsJ2 74 75 22 340 ≤ 45641887694088 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1507 c22250R_74_4 (by norm_num)

theorem c22250R_74_2 : rowsJ2 74 75 20 340 ≤ 45649166080019 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1506 c22250R_74_3 (by norm_num)

theorem c22250R_74_1 : rowsJ2 74 75 18 340 ≤ 45653189051488 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1505 c22250R_74_2 (by norm_num)

theorem c22250R_74_0 : rowsJ2 74 75 0 340 ≤ 46091457200591 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1504 c22250R_74_1 (by norm_num)

theorem hr22250R_74 : rows2 74 75 ≤ 46091457200591 := rows2_le_of_rowsJ2 74 75 c22250R_74_0

theorem c22250R_75_43 : rowsJ2 75 76 72 340 ≤ 18723016622 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1593 rows22250R_1594 (by norm_num)

theorem c22250R_75_42 : rowsJ2 75 76 70 340 ≤ 18723016622 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1592 c22250R_75_43 (by norm_num)

theorem c22250R_75_41 : rowsJ2 75 76 69 340 ≤ 18723016622 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1591 c22250R_75_42 (by norm_num)

theorem c22250R_75_40 : rowsJ2 75 76 68 340 ≤ 81777330670 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1590 c22250R_75_41 (by norm_num)

theorem c22250R_75_39 : rowsJ2 75 76 67 340 ≤ 269598286391 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1589 c22250R_75_40 (by norm_num)

theorem c22250R_75_38 : rowsJ2 75 76 66 340 ≤ 642667538034 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1588 c22250R_75_39 (by norm_num)

theorem c22250R_75_37 : rowsJ2 75 76 65 340 ≤ 1202139163524 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1587 c22250R_75_38 (by norm_num)

theorem c22250R_75_36 : rowsJ2 75 76 64 340 ≤ 1942650000906 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1586 c22250R_75_37 (by norm_num)

theorem c22250R_75_35 : rowsJ2 75 76 63 340 ≤ 2865501175871 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1585 c22250R_75_36 (by norm_num)

theorem c22250R_75_34 : rowsJ2 75 76 62 340 ≤ 3965663604629 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1584 c22250R_75_35 (by norm_num)

theorem c22250R_75_33 : rowsJ2 75 76 61 340 ≤ 5244581170733 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1583 c22250R_75_34 (by norm_num)

theorem c22250R_75_32 : rowsJ2 75 76 60 340 ≤ 6697544318742 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1582 c22250R_75_33 (by norm_num)

theorem c22250R_75_31 : rowsJ2 75 76 59 340 ≤ 8326136694556 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1581 c22250R_75_32 (by norm_num)

theorem c22250R_75_30 : rowsJ2 75 76 58 340 ≤ 10125955601482 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1580 c22250R_75_31 (by norm_num)

theorem c22250R_75_29 : rowsJ2 75 76 57 340 ≤ 12098722691042 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1579 c22250R_75_30 (by norm_num)

theorem c22250R_75_28 : rowsJ2 75 76 56 340 ≤ 14301462168036 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1578 c22250R_75_29 (by norm_num)

theorem c22250R_75_27 : rowsJ2 75 76 55 340 ≤ 16736530181619 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1577 c22250R_75_28 (by norm_num)

theorem c22250R_75_26 : rowsJ2 75 76 54 340 ≤ 19460875129710 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1576 c22250R_75_27 (by norm_num)

theorem c22250R_75_25 : rowsJ2 75 76 53 340 ≤ 22477574313214 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1575 c22250R_75_26 (by norm_num)

theorem c22250R_75_24 : rowsJ2 75 76 52 340 ≤ 25780039890897 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1574 c22250R_75_25 (by norm_num)

theorem c22250R_75_23 : rowsJ2 75 76 51 340 ≤ 28952121992831 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1573 c22250R_75_24 (by norm_num)

theorem c22250R_75_22 : rowsJ2 75 76 50 340 ≤ 31749605608604 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1572 c22250R_75_23 (by norm_num)

theorem c22250R_75_21 : rowsJ2 75 76 49 340 ≤ 34130114219116 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1571 c22250R_75_22 (by norm_num)

theorem c22250R_75_20 : rowsJ2 75 76 48 340 ≤ 36104772741030 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1570 c22250R_75_21 (by norm_num)

theorem c22250R_75_19 : rowsJ2 75 76 47 340 ≤ 37510765062327 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1569 c22250R_75_20 (by norm_num)

theorem c22250R_75_18 : rowsJ2 75 76 46 340 ≤ 38218772184533 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1568 c22250R_75_19 (by norm_num)

theorem c22250R_75_17 : rowsJ2 75 76 45 340 ≤ 38456091787068 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1567 c22250R_75_18 (by norm_num)

theorem c22250R_75_16 : rowsJ2 75 76 44 340 ≤ 38516555343913 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1566 c22250R_75_17 (by norm_num)

theorem c22250R_75_15 : rowsJ2 75 76 43 340 ≤ 38516555343913 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1565 c22250R_75_16 (by norm_num)

theorem c22250R_75_14 : rowsJ2 75 76 42 340 ≤ 38516555343913 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1564 c22250R_75_15 (by norm_num)

theorem c22250R_75_13 : rowsJ2 75 76 41 340 ≤ 38516555343913 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1563 c22250R_75_14 (by norm_num)

theorem c22250R_75_12 : rowsJ2 75 76 39 340 ≤ 38516555343913 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1562 c22250R_75_13 (by norm_num)

theorem c22250R_75_11 : rowsJ2 75 76 37 340 ≤ 38516555343913 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1561 c22250R_75_12 (by norm_num)

theorem c22250R_75_10 : rowsJ2 75 76 34 340 ≤ 38516555343913 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1560 c22250R_75_11 (by norm_num)

theorem c22250R_75_9 : rowsJ2 75 76 31 340 ≤ 38516555343913 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1559 c22250R_75_10 (by norm_num)

theorem c22250R_75_8 : rowsJ2 75 76 29 340 ≤ 38516555343913 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1558 c22250R_75_9 (by norm_num)

theorem c22250R_75_7 : rowsJ2 75 76 27 340 ≤ 38516555343913 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1557 c22250R_75_8 (by norm_num)

theorem c22250R_75_6 : rowsJ2 75 76 25 340 ≤ 38517612168752 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1556 c22250R_75_7 (by norm_num)

theorem c22250R_75_5 : rowsJ2 75 76 24 340 ≤ 38519738837719 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1555 c22250R_75_6 (by norm_num)

theorem c22250R_75_4 : rowsJ2 75 76 23 340 ≤ 38522915763127 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1554 c22250R_75_5 (by norm_num)

theorem c22250R_75_3 : rowsJ2 75 76 22 340 ≤ 38527157976707 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1553 c22250R_75_4 (by norm_num)

theorem c22250R_75_2 : rowsJ2 75 76 20 340 ≤ 38540710439506 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1552 c22250R_75_3 (by norm_num)

theorem c22250R_75_1 : rowsJ2 75 76 18 340 ≤ 38548752517133 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1551 c22250R_75_2 (by norm_num)

theorem c22250R_75_0 : rowsJ2 75 76 0 340 ≤ 38904640873868 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1550 c22250R_75_1 (by norm_num)

theorem hr22250R_75 : rows2 75 76 ≤ 38904640873868 := rows2_le_of_rowsJ2 75 76 c22250R_75_0

theorem c22250R_76_42 : rowsJ2 76 77 73 340 ≤ 129418249772 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1637 rows22250R_1638 (by norm_num)

theorem c22250R_76_41 : rowsJ2 76 77 71 340 ≤ 129418249772 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1636 c22250R_76_42 (by norm_num)

theorem c22250R_76_40 : rowsJ2 76 77 69 340 ≤ 129418249772 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1635 c22250R_76_41 (by norm_num)

theorem c22250R_76_39 : rowsJ2 76 77 68 340 ≤ 129418249772 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1634 c22250R_76_40 (by norm_num)

theorem c22250R_76_38 : rowsJ2 76 77 67 340 ≤ 192508518787 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1633 c22250R_76_39 (by norm_num)

theorem c22250R_76_37 : rowsJ2 76 77 66 340 ≤ 380451027593 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1632 c22250R_76_38 (by norm_num)

theorem c22250R_76_36 : rowsJ2 76 77 65 340 ≤ 753790941804 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1631 c22250R_76_37 (by norm_num)

theorem c22250R_76_35 : rowsJ2 76 77 64 340 ≤ 1248918158495 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1630 c22250R_76_36 (by norm_num)

theorem c22250R_76_34 : rowsJ2 76 77 63 340 ≤ 1925479695135 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1629 c22250R_76_35 (by norm_num)

theorem c22250R_76_33 : rowsJ2 76 77 62 340 ≤ 2721137973339 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1628 c22250R_76_34 (by norm_num)

theorem c22250R_76_32 : rowsJ2 76 77 61 340 ≤ 3694697732980 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1627 c22250R_76_33 (by norm_num)

theorem c22250R_76_31 : rowsJ2 76 77 60 340 ≤ 4785022985655 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1626 c22250R_76_32 (by norm_num)

theorem c22250R_76_30 : rowsJ2 76 77 59 340 ≤ 6050130936650 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1625 c22250R_76_31 (by norm_num)

theorem c22250R_76_29 : rowsJ2 76 77 58 340 ≤ 7430019959297 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1624 c22250R_76_30 (by norm_num)

theorem c22250R_76_28 : rowsJ2 76 77 57 340 ≤ 8981973499790 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1623 c22250R_76_29 (by norm_num)

theorem c22250R_76_27 : rowsJ2 76 77 56 340 ≤ 10707694541828 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1622 c22250R_76_28 (by norm_num)

theorem c22250R_76_26 : rowsJ2 76 77 55 340 ≤ 12664278753748 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1621 c22250R_76_27 (by norm_num)

theorem c22250R_76_25 : rowsJ2 76 77 54 340 ≤ 14854079360831 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1620 c22250R_76_26 (by norm_num)

theorem c22250R_76_24 : rowsJ2 76 77 53 340 ≤ 17334141927268 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1619 c22250R_76_25 (by norm_num)

theorem c22250R_76_23 : rowsJ2 76 77 52 340 ≤ 20044475017349 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1618 c22250R_76_24 (by norm_num)

theorem c22250R_76_22 : rowsJ2 76 77 51 340 ≤ 22861376895451 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1617 c22250R_76_23 (by norm_num)

theorem c22250R_76_21 : rowsJ2 76 77 50 340 ≤ 25366514774960 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1616 c22250R_76_22 (by norm_num)

theorem c22250R_76_20 : rowsJ2 76 77 49 340 ≤ 27567810278271 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1615 c22250R_76_21 (by norm_num)

theorem c22250R_76_19 : rowsJ2 76 77 48 340 ≤ 29421606758104 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1614 c22250R_76_20 (by norm_num)

theorem c22250R_76_18 : rowsJ2 76 77 47 340 ≤ 30816171234221 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1613 c22250R_76_19 (by norm_num)

theorem c22250R_76_17 : rowsJ2 76 77 46 340 ≤ 31518423704958 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1612 c22250R_76_18 (by norm_num)

theorem c22250R_76_16 : rowsJ2 76 77 45 340 ≤ 31753814383960 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1611 c22250R_76_17 (by norm_num)

theorem c22250R_76_15 : rowsJ2 76 77 44 340 ≤ 31813786495613 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1610 c22250R_76_16 (by norm_num)

theorem c22250R_76_14 : rowsJ2 76 77 43 340 ≤ 31813786495613 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1609 c22250R_76_15 (by norm_num)

theorem c22250R_76_13 : rowsJ2 76 77 42 340 ≤ 31813786495613 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1608 c22250R_76_14 (by norm_num)

theorem c22250R_76_12 : rowsJ2 76 77 41 340 ≤ 31813786495613 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1607 c22250R_76_13 (by norm_num)

theorem c22250R_76_11 : rowsJ2 76 77 39 340 ≤ 31813786495613 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1606 c22250R_76_12 (by norm_num)

theorem c22250R_76_10 : rowsJ2 76 77 37 340 ≤ 31813786495613 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1605 c22250R_76_11 (by norm_num)

theorem c22250R_76_9 : rowsJ2 76 77 34 340 ≤ 31813786495613 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1604 c22250R_76_10 (by norm_num)

theorem c22250R_76_8 : rowsJ2 76 77 31 340 ≤ 31813786495613 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1603 c22250R_76_9 (by norm_num)

theorem c22250R_76_7 : rowsJ2 76 77 29 340 ≤ 31813786495613 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1602 c22250R_76_8 (by norm_num)

theorem c22250R_76_6 : rowsJ2 76 77 27 340 ≤ 31813786495613 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1601 c22250R_76_7 (by norm_num)

theorem c22250R_76_5 : rowsJ2 76 77 25 340 ≤ 31813786495613 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1600 c22250R_76_6 (by norm_num)

theorem c22250R_76_4 : rowsJ2 76 77 23 340 ≤ 31816988991526 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1599 c22250R_76_5 (by norm_num)

theorem c22250R_76_3 : rowsJ2 76 77 22 340 ≤ 31820185741920 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1598 c22250R_76_4 (by norm_num)

theorem c22250R_76_2 : rowsJ2 76 77 20 340 ≤ 31832715204716 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1597 c22250R_76_3 (by norm_num)

theorem c22250R_76_1 : rowsJ2 76 77 18 340 ≤ 31843804125248 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1596 c22250R_76_2 (by norm_num)

theorem c22250R_76_0 : rowsJ2 76 77 0 340 ≤ 32128104805650 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1595 c22250R_76_1 (by norm_num)

theorem hr22250R_76 : rows2 76 77 ≤ 32128104805650 := rows2_le_of_rowsJ2 76 77 c22250R_76_0

theorem c22250R_77_41 : rowsJ2 77 78 74 340 ≤ 420644450346 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1680 rows22250R_1681 (by norm_num)

theorem c22250R_77_40 : rowsJ2 77 78 72 340 ≤ 420644450346 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1679 c22250R_77_41 (by norm_num)

theorem c22250R_77_39 : rowsJ2 77 78 70 340 ≤ 420644450346 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1678 c22250R_77_40 (by norm_num)

theorem c22250R_77_38 : rowsJ2 77 78 68 340 ≤ 420644450346 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1677 c22250R_77_39 (by norm_num)

theorem c22250R_77_37 : rowsJ2 77 78 67 340 ≤ 420644450346 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1676 c22250R_77_38 (by norm_num)

theorem c22250R_77_36 : rowsJ2 77 78 66 340 ≤ 483779720774 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1675 c22250R_77_37 (by norm_num)

theorem c22250R_77_35 : rowsJ2 77 78 65 340 ≤ 671871008289 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1674 c22250R_77_36 (by norm_num)

theorem c22250R_77_34 : rowsJ2 77 78 64 340 ≤ 981263722929 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1673 c22250R_77_35 (by norm_num)

theorem c22250R_77_33 : rowsJ2 77 78 63 340 ≤ 1412777744010 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1672 c22250R_77_34 (by norm_num)

theorem c22250R_77_32 : rowsJ2 77 78 62 340 ≤ 1962985139996 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1671 c22250R_77_33 (by norm_num)

theorem c22250R_77_31 : rowsJ2 77 78 61 340 ≤ 2632802702105 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1670 c22250R_77_32 (by norm_num)

theorem c22250R_77_30 : rowsJ2 77 78 60 340 ≤ 3419018969387 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1669 c22250R_77_31 (by norm_num)

theorem c22250R_77_29 : rowsJ2 77 78 59 340 ≤ 4322645313716 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1668 c22250R_77_30 (by norm_num)

theorem c22250R_77_28 : rowsJ2 77 78 58 340 ≤ 5340677848097 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1667 c22250R_77_29 (by norm_num)

theorem c22250R_77_27 : rowsJ2 77 78 57 340 ≤ 6474221043572 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1666 c22250R_77_28 (by norm_num)

theorem c22250R_77_26 : rowsJ2 77 78 56 340 ≤ 7780616112792 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1665 c22250R_77_27 (by norm_num)

theorem c22250R_77_25 : rowsJ2 77 78 55 340 ≤ 9261548996714 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1664 c22250R_77_26 (by norm_num)

theorem c22250R_77_24 : rowsJ2 77 78 54 340 ≤ 10974197539852 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1663 c22250R_77_25 (by norm_num)

theorem c22250R_77_23 : rowsJ2 77 78 53 340 ≤ 12920913933594 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1662 c22250R_77_24 (by norm_num)

theorem c22250R_77_22 : rowsJ2 77 78 52 340 ≤ 15096277526149 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1661 c22250R_77_23 (by norm_num)

theorem c22250R_77_21 : rowsJ2 77 78 51 340 ≤ 17502838091939 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1660 c22250R_77_22 (by norm_num)

theorem c22250R_77_20 : rowsJ2 77 78 50 340 ≤ 19714367393221 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1659 c22250R_77_21 (by norm_num)

theorem c22250R_77_19 : rowsJ2 77 78 49 340 ≤ 21683003917804 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1658 c22250R_77_20 (by norm_num)

theorem c22250R_77_18 : rowsJ2 77 78 48 340 ≤ 23415627807002 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1657 c22250R_77_19 (by norm_num)

theorem c22250R_77_17 : rowsJ2 77 78 47 340 ≤ 24746696169146 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1656 c22250R_77_18 (by norm_num)

theorem c22250R_77_16 : rowsJ2 77 78 46 340 ≤ 25443286781317 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1655 c22250R_77_17 (by norm_num)

theorem c22250R_77_15 : rowsJ2 77 78 45 340 ≤ 25676779640392 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1654 c22250R_77_16 (by norm_num)

theorem c22250R_77_14 : rowsJ2 77 78 44 340 ≤ 25736268231334 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1653 c22250R_77_15 (by norm_num)

theorem c22250R_77_13 : rowsJ2 77 78 43 340 ≤ 25736268231334 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1652 c22250R_77_14 (by norm_num)

theorem c22250R_77_12 : rowsJ2 77 78 42 340 ≤ 25736268231334 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1651 c22250R_77_13 (by norm_num)

theorem c22250R_77_11 : rowsJ2 77 78 41 340 ≤ 25736268231334 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1650 c22250R_77_12 (by norm_num)

theorem c22250R_77_10 : rowsJ2 77 78 39 340 ≤ 25736268231334 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1649 c22250R_77_11 (by norm_num)

theorem c22250R_77_9 : rowsJ2 77 78 36 340 ≤ 25736268231334 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1648 c22250R_77_10 (by norm_num)

theorem c22250R_77_8 : rowsJ2 77 78 33 340 ≤ 25736268231334 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1647 c22250R_77_9 (by norm_num)

theorem c22250R_77_7 : rowsJ2 77 78 30 340 ≤ 25736268231334 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1646 c22250R_77_8 (by norm_num)

theorem c22250R_77_6 : rowsJ2 77 78 28 340 ≤ 25736268231334 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1645 c22250R_77_7 (by norm_num)

theorem c22250R_77_5 : rowsJ2 77 78 26 340 ≤ 25736268231334 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1644 c22250R_77_6 (by norm_num)

theorem c22250R_77_4 : rowsJ2 77 78 24 340 ≤ 25736268231334 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1643 c22250R_77_5 (by norm_num)

theorem c22250R_77_3 : rowsJ2 77 78 22 340 ≤ 25739490706600 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1642 c22250R_77_4 (by norm_num)

theorem c22250R_77_2 : rowsJ2 77 78 20 340 ≤ 25749917011581 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1641 c22250R_77_3 (by norm_num)

theorem c22250R_77_1 : rowsJ2 77 78 18 340 ≤ 25764124162621 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1640 c22250R_77_2 (by norm_num)

theorem c22250R_77_0 : rowsJ2 77 78 0 340 ≤ 25986737422786 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1639 c22250R_77_1 (by norm_num)

theorem hr22250R_77 : rows2 77 78 ≤ 25986737422786 := rows2_le_of_rowsJ2 77 78 c22250R_77_0

theorem c22250R_78_40 : rowsJ2 78 79 76 340 ≤ 1809892560081 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1722 rows22250R_1723 (by norm_num)

theorem c22250R_78_39 : rowsJ2 78 79 73 340 ≤ 1828166339835 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1721 c22250R_78_40 (by norm_num)

theorem c22250R_78_38 : rowsJ2 78 79 71 340 ≤ 1828166339835 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1720 c22250R_78_39 (by norm_num)

theorem c22250R_78_37 : rowsJ2 78 79 69 340 ≤ 1828166339835 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1719 c22250R_78_38 (by norm_num)

theorem c22250R_78_36 : rowsJ2 78 79 67 340 ≤ 1828166339835 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1718 c22250R_78_37 (by norm_num)

theorem c22250R_78_35 : rowsJ2 78 79 66 340 ≤ 1828166339835 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1717 c22250R_78_36 (by norm_num)

theorem c22250R_78_34 : rowsJ2 78 79 65 340 ≤ 1891355696771 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1716 c22250R_78_35 (by norm_num)

theorem c22250R_78_33 : rowsJ2 78 79 64 340 ≤ 2015864652038 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1715 c22250R_78_34 (by norm_num)

theorem c22250R_78_32 : rowsJ2 78 79 63 340 ≤ 2261999927629 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1714 c22250R_78_33 (by norm_num)

theorem c22250R_78_31 : rowsJ2 78 79 62 340 ≤ 2567950381577 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1713 c22250R_78_32 (by norm_num)

theorem c22250R_78_30 : rowsJ2 78 79 61 340 ≤ 2993091689908 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1712 c22250R_78_31 (by norm_num)

theorem c22250R_78_29 : rowsJ2 78 79 60 340 ≤ 3476751021536 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1711 c22250R_78_30 (by norm_num)

theorem c22250R_78_28 : rowsJ2 78 79 59 340 ≤ 4077430932578 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1710 c22250R_78_29 (by norm_num)

theorem c22250R_78_27 : rowsJ2 78 79 58 340 ≤ 4735531297330 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1709 c22250R_78_28 (by norm_num)

theorem c22250R_78_26 : rowsJ2 78 79 57 340 ≤ 5508737962514 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1708 c22250R_78_27 (by norm_num)

theorem c22250R_78_25 : rowsJ2 78 79 56 340 ≤ 6398125053531 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1707 c22250R_78_26 (by norm_num)

theorem c22250R_78_24 : rowsJ2 78 79 55 340 ≤ 7461101910724 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1706 c22250R_78_25 (by norm_num)

theorem c22250R_78_23 : rowsJ2 78 79 54 340 ≤ 8699338962622 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1705 c22250R_78_24 (by norm_num)

theorem c22250R_78_22 : rowsJ2 78 79 53 340 ≤ 10170106946773 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1704 c22250R_78_23 (by norm_num)

theorem c22250R_78_21 : rowsJ2 78 79 52 340 ≤ 11813684783908 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1703 c22250R_78_22 (by norm_num)

theorem c22250R_78_20 : rowsJ2 78 79 51 340 ≤ 13686791748517 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1702 c22250R_78_21 (by norm_num)

theorem c22250R_78_19 : rowsJ2 78 79 50 340 ≤ 15549700304753 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1701 c22250R_78_20 (by norm_num)

theorem c22250R_78_18 : rowsJ2 78 79 49 340 ≤ 17284662193530 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1700 c22250R_78_19 (by norm_num)

theorem c22250R_78_17 : rowsJ2 78 79 48 340 ≤ 18842775581254 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1699 c22250R_78_18 (by norm_num)

theorem c22250R_78_16 : rowsJ2 78 79 47 340 ≤ 20110243179046 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1698 c22250R_78_17 (by norm_num)

theorem c22250R_78_15 : rowsJ2 78 79 46 340 ≤ 20801262499097 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1697 c22250R_78_16 (by norm_num)

theorem c22250R_78_14 : rowsJ2 78 79 45 340 ≤ 21032887895558 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1696 c22250R_78_15 (by norm_num)

theorem c22250R_78_13 : rowsJ2 78 79 44 340 ≤ 21091900700131 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1695 c22250R_78_14 (by norm_num)

theorem c22250R_78_12 : rowsJ2 78 79 43 340 ≤ 21091900700131 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1694 c22250R_78_13 (by norm_num)

theorem c22250R_78_11 : rowsJ2 78 79 42 340 ≤ 21091900700131 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1693 c22250R_78_12 (by norm_num)

theorem c22250R_78_10 : rowsJ2 78 79 40 340 ≤ 21091900700131 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1692 c22250R_78_11 (by norm_num)

theorem c22250R_78_9 : rowsJ2 78 79 38 340 ≤ 21091900700131 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1691 c22250R_78_10 (by norm_num)

theorem c22250R_78_8 : rowsJ2 78 79 35 340 ≤ 22298148982957 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1690 c22250R_78_9 (by norm_num)

theorem c22250R_78_7 : rowsJ2 78 79 31 340 ≤ 22494520136440 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1689 c22250R_78_8 (by norm_num)

theorem c22250R_78_6 : rowsJ2 78 79 28 340 ≤ 22494520136440 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1688 c22250R_78_7 (by norm_num)

theorem c22250R_78_5 : rowsJ2 78 79 26 340 ≤ 22494520136440 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1687 c22250R_78_6 (by norm_num)

theorem c22250R_78_4 : rowsJ2 78 79 24 340 ≤ 22494520136440 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1686 c22250R_78_5 (by norm_num)

theorem c22250R_78_3 : rowsJ2 78 79 22 340 ≤ 22495596429536 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1685 c22250R_78_4 (by norm_num)

theorem c22250R_78_2 : rowsJ2 78 79 20 340 ≤ 22503890171294 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1684 c22250R_78_3 (by norm_num)

theorem c22250R_78_1 : rowsJ2 78 79 18 340 ≤ 22519140321985 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1683 c22250R_78_2 (by norm_num)

theorem c22250R_78_0 : rowsJ2 78 79 0 340 ≤ 22690070375832 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1682 c22250R_78_1 (by norm_num)

theorem hr22250R_78 : rows2 78 79 ≤ 22690070375832 := rows2_le_of_rowsJ2 78 79 c22250R_78_0

theorem c22250R_79_39 : rowsJ2 79 80 75 340 ≤ 3409432599824 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1763 rows22250R_1764 (by norm_num)

theorem c22250R_79_38 : rowsJ2 79 80 72 340 ≤ 3409432599824 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1762 c22250R_79_39 (by norm_num)

theorem c22250R_79_37 : rowsJ2 79 80 70 340 ≤ 3409432599824 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1761 c22250R_79_38 (by norm_num)

theorem c22250R_79_36 : rowsJ2 79 80 68 340 ≤ 3409432599824 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1760 c22250R_79_37 (by norm_num)

theorem c22250R_79_35 : rowsJ2 79 80 66 340 ≤ 3409432599824 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1759 c22250R_79_36 (by norm_num)

theorem c22250R_79_34 : rowsJ2 79 80 65 340 ≤ 3409432599824 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1758 c22250R_79_35 (by norm_num)

theorem c22250R_79_33 : rowsJ2 79 80 64 340 ≤ 3409432599824 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1757 c22250R_79_34 (by norm_num)

theorem c22250R_79_32 : rowsJ2 79 80 63 340 ≤ 3471008360481 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1756 c22250R_79_33 (by norm_num)

theorem c22250R_79_31 : rowsJ2 79 80 62 340 ≤ 3592391907119 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1755 c22250R_79_32 (by norm_num)

theorem c22250R_79_30 : rowsJ2 79 80 61 340 ≤ 3774004045460 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1754 c22250R_79_31 (by norm_num)

theorem c22250R_79_29 : rowsJ2 79 80 60 340 ≤ 4014187358352 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1753 c22250R_79_30 (by norm_num)

theorem c22250R_79_28 : rowsJ2 79 80 59 340 ≤ 4313411130515 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1752 c22250R_79_29 (by norm_num)

theorem c22250R_79_27 : rowsJ2 79 80 58 340 ≤ 4670123734867 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1751 c22250R_79_28 (by norm_num)

theorem c22250R_79_26 : rowsJ2 79 80 57 340 ≤ 5084841953081 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1750 c22250R_79_27 (by norm_num)

theorem c22250R_79_25 : rowsJ2 79 80 56 340 ≤ 5615306572670 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1749 c22250R_79_26 (by norm_num)

theorem c22250R_79_24 : rowsJ2 79 80 55 340 ≤ 6262562586655 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1748 c22250R_79_25 (by norm_num)

theorem c22250R_79_23 : rowsJ2 79 80 54 340 ≤ 7084097809182 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1747 c22250R_79_24 (by norm_num)

theorem c22250R_79_22 : rowsJ2 79 80 53 340 ≤ 8081568595439 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1746 c22250R_79_23 (by norm_num)

theorem c22250R_79_21 : rowsJ2 79 80 52 340 ≤ 9250767781206 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1745 c22250R_79_22 (by norm_num)

theorem c22250R_79_20 : rowsJ2 79 80 51 340 ≤ 10593501190249 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1744 c22250R_79_21 (by norm_num)

theorem c22250R_79_19 : rowsJ2 79 80 50 340 ≤ 12105856966892 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1743 c22250R_79_20 (by norm_num)

theorem c22250R_79_18 : rowsJ2 79 80 49 340 ≤ 13552287367208 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1742 c22250R_79_19 (by norm_num)

theorem c22250R_79_17 : rowsJ2 79 80 48 340 ≤ 14935138163601 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1741 c22250R_79_18 (by norm_num)

theorem c22250R_79_16 : rowsJ2 79 80 47 340 ≤ 16085766931343 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1740 c22250R_79_17 (by norm_num)

theorem c22250R_79_15 : rowsJ2 79 80 46 340 ≤ 16771303369925 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1739 c22250R_79_16 (by norm_num)

theorem c22250R_79_14 : rowsJ2 79 80 45 340 ≤ 17001090938474 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1738 c22250R_79_15 (by norm_num)

theorem c22250R_79_13 : rowsJ2 79 80 44 340 ≤ 17059635506917 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1737 c22250R_79_14 (by norm_num)

theorem c22250R_79_12 : rowsJ2 79 80 43 340 ≤ 17059635506917 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1736 c22250R_79_13 (by norm_num)

theorem c22250R_79_11 : rowsJ2 79 80 42 340 ≤ 17059635506917 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1735 c22250R_79_12 (by norm_num)

theorem c22250R_79_10 : rowsJ2 79 80 41 340 ≤ 17059635506917 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1734 c22250R_79_11 (by norm_num)

theorem c22250R_79_9 : rowsJ2 79 80 39 340 ≤ 17059635506917 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1733 c22250R_79_10 (by norm_num)

theorem c22250R_79_8 : rowsJ2 79 80 36 340 ≤ 20342593974202 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1732 c22250R_79_9 (by norm_num)

theorem c22250R_79_7 : rowsJ2 79 80 32 340 ≤ 21208351731098 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1731 c22250R_79_8 (by norm_num)

theorem c22250R_79_6 : rowsJ2 79 80 29 340 ≤ 21208351731098 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1730 c22250R_79_7 (by norm_num)

theorem c22250R_79_5 : rowsJ2 79 80 26 340 ≤ 21208351731098 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1729 c22250R_79_6 (by norm_num)

theorem c22250R_79_4 : rowsJ2 79 80 24 340 ≤ 21208351731098 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1728 c22250R_79_5 (by norm_num)

theorem c22250R_79_3 : rowsJ2 79 80 22 340 ≤ 21208351731098 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1727 c22250R_79_4 (by norm_num)

theorem c22250R_79_2 : rowsJ2 79 80 20 340 ≤ 21214481422238 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1726 c22250R_79_3 (by norm_num)

theorem c22250R_79_1 : rowsJ2 79 80 18 340 ≤ 21229710903753 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1725 c22250R_79_2 (by norm_num)

theorem c22250R_79_0 : rowsJ2 79 80 0 340 ≤ 21359096370299 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1724 c22250R_79_1 (by norm_num)

theorem hr22250R_79 : rows2 79 80 ≤ 21359096370299 := rows2_le_of_rowsJ2 79 80 c22250R_79_0

theorem c22250R_80_41 : rowsJ2 80 81 79 340 ≤ 3762004026325 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1806 rows22250R_1807 (by norm_num)

theorem c22250R_80_40 : rowsJ2 80 81 77 340 ≤ 5147584775109 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1805 c22250R_80_41 (by norm_num)

theorem c22250R_80_39 : rowsJ2 80 81 74 340 ≤ 5272927891038 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1804 c22250R_80_40 (by norm_num)

theorem c22250R_80_38 : rowsJ2 80 81 71 340 ≤ 5272927891038 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1803 c22250R_80_39 (by norm_num)

theorem c22250R_80_37 : rowsJ2 80 81 69 340 ≤ 5272927891038 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1802 c22250R_80_38 (by norm_num)

theorem c22250R_80_36 : rowsJ2 80 81 67 340 ≤ 5272927891038 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1801 c22250R_80_37 (by norm_num)

theorem c22250R_80_35 : rowsJ2 80 81 65 340 ≤ 5272927891038 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1800 c22250R_80_36 (by norm_num)

theorem c22250R_80_34 : rowsJ2 80 81 64 340 ≤ 5272927891038 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1799 c22250R_80_35 (by norm_num)

theorem c22250R_80_33 : rowsJ2 80 81 63 340 ≤ 5272927891038 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1798 c22250R_80_34 (by norm_num)

theorem c22250R_80_32 : rowsJ2 80 81 62 340 ≤ 5272927891038 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1797 c22250R_80_33 (by norm_num)

theorem c22250R_80_31 : rowsJ2 80 81 61 340 ≤ 5332980379253 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1796 c22250R_80_32 (by norm_num)

theorem c22250R_80_30 : rowsJ2 80 81 60 340 ≤ 5392889391655 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1795 c22250R_80_31 (by norm_num)

theorem c22250R_80_29 : rowsJ2 80 81 59 340 ≤ 5511744908955 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1794 c22250R_80_30 (by norm_num)

theorem c22250R_80_28 : rowsJ2 80 81 58 340 ≤ 5630361260830 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1793 c22250R_80_29 (by norm_num)

theorem c22250R_80_27 : rowsJ2 80 81 57 340 ≤ 5806925435756 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1792 c22250R_80_28 (by norm_num)

theorem c22250R_80_26 : rowsJ2 80 81 56 340 ≤ 6041925710401 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1791 c22250R_80_27 (by norm_num)

theorem c22250R_80_25 : rowsJ2 80 81 55 340 ≤ 6393181193336 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1790 c22250R_80_26 (by norm_num)

theorem c22250R_80_24 : rowsJ2 80 81 54 340 ≤ 6861722113944 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1789 c22250R_80_25 (by norm_num)

theorem c22250R_80_23 : rowsJ2 80 81 53 340 ≤ 7505138291291 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1788 c22250R_80_24 (by norm_num)

theorem c22250R_80_22 : rowsJ2 80 81 52 340 ≤ 8263989730044 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1787 c22250R_80_23 (by norm_num)

theorem c22250R_80_21 : rowsJ2 80 81 51 340 ≤ 9195232916390 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1786 c22250R_80_22 (by norm_num)

theorem c22250R_80_20 : rowsJ2 80 81 50 340 ≤ 10240407390299 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1785 c22250R_80_21 (by norm_num)

theorem c22250R_80_19 : rowsJ2 80 81 49 340 ≤ 11396687693518 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1784 c22250R_80_20 (by norm_num)

theorem c22250R_80_18 : rowsJ2 80 81 48 340 ≤ 12549579622416 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1783 c22250R_80_19 (by norm_num)

theorem c22250R_80_17 : rowsJ2 80 81 47 340 ≤ 13582881442278 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1782 c22250R_80_18 (by norm_num)

theorem c22250R_80_16 : rowsJ2 80 81 46 340 ≤ 14209773570685 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1781 c22250R_80_17 (by norm_num)

theorem c22250R_80_15 : rowsJ2 80 81 45 340 ≤ 14437752246171 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1780 c22250R_80_16 (by norm_num)

theorem c22250R_80_14 : rowsJ2 80 81 44 340 ≤ 14495835950414 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1779 c22250R_80_15 (by norm_num)

theorem c22250R_80_13 : rowsJ2 80 81 43 340 ≤ 14495835950414 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1778 c22250R_80_14 (by norm_num)

theorem c22250R_80_12 : rowsJ2 80 81 42 340 ≤ 14495835950414 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1777 c22250R_80_13 (by norm_num)

theorem c22250R_80_11 : rowsJ2 80 81 41 340 ≤ 14495835950414 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1776 c22250R_80_12 (by norm_num)

theorem c22250R_80_10 : rowsJ2 80 81 40 340 ≤ 14495835950414 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1775 c22250R_80_11 (by norm_num)

theorem c22250R_80_9 : rowsJ2 80 81 38 340 ≤ 17805753718509 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1774 c22250R_80_10 (by norm_num)

theorem c22250R_80_8 : rowsJ2 80 81 35 340 ≤ 22043070986759 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1773 c22250R_80_9 (by norm_num)

theorem c22250R_80_7 : rowsJ2 80 81 31 340 ≤ 22723974633402 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1772 c22250R_80_8 (by norm_num)

theorem c22250R_80_6 : rowsJ2 80 81 28 340 ≤ 22723974633402 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1771 c22250R_80_7 (by norm_num)

theorem c22250R_80_5 : rowsJ2 80 81 25 340 ≤ 22723974633402 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1770 c22250R_80_6 (by norm_num)

theorem c22250R_80_4 : rowsJ2 80 81 23 340 ≤ 22723974633402 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1769 c22250R_80_5 (by norm_num)

theorem c22250R_80_3 : rowsJ2 80 81 21 340 ≤ 22723974633402 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1768 c22250R_80_4 (by norm_num)

theorem c22250R_80_2 : rowsJ2 80 81 19 340 ≤ 22730147713760 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1767 c22250R_80_3 (by norm_num)

theorem c22250R_80_1 : rowsJ2 80 81 17 340 ≤ 22741368326155 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1766 c22250R_80_2 (by norm_num)

theorem c22250R_80_0 : rowsJ2 80 81 0 340 ≤ 22830285563749 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1765 c22250R_80_1 (by norm_num)

theorem hr22250R_80 : rows2 80 81 ≤ 22830285563749 := rows2_le_of_rowsJ2 80 81 c22250R_80_0

theorem c22250R_81_40 : rowsJ2 81 82 80 340 ≤ 3853068595378 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1848 rows22250R_1849 (by norm_num)

theorem c22250R_81_39 : rowsJ2 81 82 78 340 ≤ 6178971796104 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1847 c22250R_81_40 (by norm_num)

theorem c22250R_81_38 : rowsJ2 81 82 76 340 ≤ 6568628812293 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1846 c22250R_81_39 (by norm_num)

theorem c22250R_81_37 : rowsJ2 81 82 73 340 ≤ 6586474407869 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1845 c22250R_81_38 (by norm_num)

theorem c22250R_81_36 : rowsJ2 81 82 70 340 ≤ 6586474407869 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1844 c22250R_81_37 (by norm_num)

theorem c22250R_81_35 : rowsJ2 81 82 68 340 ≤ 6586474407869 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1843 c22250R_81_36 (by norm_num)

theorem c22250R_81_34 : rowsJ2 81 82 66 340 ≤ 6586474407869 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1842 c22250R_81_35 (by norm_num)

theorem c22250R_81_33 : rowsJ2 81 82 64 340 ≤ 6586474407869 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1841 c22250R_81_34 (by norm_num)

theorem c22250R_81_32 : rowsJ2 81 82 63 340 ≤ 6586474407869 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1840 c22250R_81_33 (by norm_num)

theorem c22250R_81_31 : rowsJ2 81 82 62 340 ≤ 6586474407869 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1839 c22250R_81_32 (by norm_num)

theorem c22250R_81_30 : rowsJ2 81 82 61 340 ≤ 6586474407869 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1838 c22250R_81_31 (by norm_num)

theorem c22250R_81_29 : rowsJ2 81 82 60 340 ≤ 6586474407869 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1837 c22250R_81_30 (by norm_num)

theorem c22250R_81_28 : rowsJ2 81 82 59 340 ≤ 6586474407869 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1836 c22250R_81_29 (by norm_num)

theorem c22250R_81_27 : rowsJ2 81 82 58 340 ≤ 6586474407869 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1835 c22250R_81_28 (by norm_num)

theorem c22250R_81_26 : rowsJ2 81 82 57 340 ≤ 6586474407869 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1834 c22250R_81_27 (by norm_num)

theorem c22250R_81_25 : rowsJ2 81 82 56 340 ≤ 6644740543647 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1833 c22250R_81_26 (by norm_num)

theorem c22250R_81_24 : rowsJ2 81 82 55 340 ≤ 6761746568198 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1832 c22250R_81_25 (by norm_num)

theorem c22250R_81_23 : rowsJ2 81 82 54 340 ≤ 6995413006098 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1831 c22250R_81_24 (by norm_num)

theorem c22250R_81_22 : rowsJ2 81 82 53 340 ≤ 7346769355504 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1830 c22250R_81_23 (by norm_num)

theorem c22250R_81_21 : rowsJ2 81 82 52 340 ≤ 7812911223833 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1829 c22250R_81_22 (by norm_num)

theorem c22250R_81_20 : rowsJ2 81 82 51 340 ≤ 8394968913474 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1828 c22250R_81_21 (by norm_num)

theorem c22250R_81_19 : rowsJ2 81 82 50 340 ≤ 9090237401771 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1827 c22250R_81_20 (by norm_num)

theorem c22250R_81_18 : rowsJ2 81 82 49 340 ≤ 9899947774700 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1826 c22250R_81_19 (by norm_num)

theorem c22250R_81_17 : rowsJ2 81 82 48 340 ≤ 10821588866847 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1825 c22250R_81_18 (by norm_num)

theorem c22250R_81_16 : rowsJ2 81 82 47 340 ≤ 11683017648925 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1824 c22250R_81_17 (by norm_num)

theorem c22250R_81_15 : rowsJ2 81 82 46 340 ≤ 12251027199367 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1823 c22250R_81_16 (by norm_num)

theorem c22250R_81_14 : rowsJ2 81 82 45 340 ≤ 12477225238646 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1822 c22250R_81_15 (by norm_num)

theorem c22250R_81_13 : rowsJ2 81 82 44 340 ≤ 12534855277885 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1821 c22250R_81_14 (by norm_num)

theorem c22250R_81_12 : rowsJ2 81 82 43 340 ≤ 12534855277885 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1820 c22250R_81_13 (by norm_num)

theorem c22250R_81_11 : rowsJ2 81 82 42 340 ≤ 12534855277885 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1819 c22250R_81_12 (by norm_num)

theorem c22250R_81_10 : rowsJ2 81 82 41 340 ≤ 12534855277885 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1818 c22250R_81_11 (by norm_num)

theorem c22250R_81_9 : rowsJ2 81 82 39 340 ≤ 17051505759015 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1817 c22250R_81_10 (by norm_num)

theorem c22250R_81_8 : rowsJ2 81 82 36 340 ≤ 25499720125756 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1816 c22250R_81_9 (by norm_num)

theorem c22250R_81_7 : rowsJ2 81 82 32 340 ≤ 27396398161428 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1815 c22250R_81_8 (by norm_num)

theorem c22250R_81_6 : rowsJ2 81 82 28 340 ≤ 27396398161428 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1814 c22250R_81_7 (by norm_num)

theorem c22250R_81_5 : rowsJ2 81 82 25 340 ≤ 27396398161428 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1813 c22250R_81_6 (by norm_num)

theorem c22250R_81_4 : rowsJ2 81 82 23 340 ≤ 27396398161428 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1812 c22250R_81_5 (by norm_num)

theorem c22250R_81_3 : rowsJ2 81 82 21 340 ≤ 27396398161428 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1811 c22250R_81_4 (by norm_num)

theorem c22250R_81_2 : rowsJ2 81 82 19 340 ≤ 27398460777435 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1810 c22250R_81_3 (by norm_num)

theorem c22250R_81_1 : rowsJ2 81 82 17 340 ≤ 27407765572942 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1809 c22250R_81_2 (by norm_num)

theorem c22250R_81_0 : rowsJ2 81 82 0 340 ≤ 27469601855735 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1808 c22250R_81_1 (by norm_num)

theorem hr22250R_81 : rows2 81 82 ≤ 27469601855735 := rows2_le_of_rowsJ2 81 82 c22250R_81_0

theorem c22250R_82_40 : rowsJ2 82 83 81 340 ≤ 4204597325584 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1890 rows22250R_1891 (by norm_num)

theorem c22250R_82_39 : rowsJ2 82 83 80 340 ≤ 5819926913325 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1889 c22250R_82_40 (by norm_num)

theorem c22250R_82_38 : rowsJ2 82 83 79 340 ≤ 7036600538296 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1888 c22250R_82_39 (by norm_num)

theorem c22250R_82_37 : rowsJ2 82 83 76 340 ≤ 8298386255353 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1887 c22250R_82_38 (by norm_num)

theorem c22250R_82_36 : rowsJ2 82 83 72 340 ≤ 8316093547444 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1886 c22250R_82_37 (by norm_num)

theorem c22250R_82_35 : rowsJ2 82 83 69 340 ≤ 8316093547444 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1885 c22250R_82_36 (by norm_num)

theorem c22250R_82_34 : rowsJ2 82 83 67 340 ≤ 8316093547444 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1884 c22250R_82_35 (by norm_num)

theorem c22250R_82_33 : rowsJ2 82 83 65 340 ≤ 8316093547444 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1883 c22250R_82_34 (by norm_num)

theorem c22250R_82_32 : rowsJ2 82 83 63 340 ≤ 8316093547444 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1882 c22250R_82_33 (by norm_num)

theorem c22250R_82_31 : rowsJ2 82 83 62 340 ≤ 8316093547444 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1881 c22250R_82_32 (by norm_num)

theorem c22250R_82_30 : rowsJ2 82 83 61 340 ≤ 8316093547444 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1880 c22250R_82_31 (by norm_num)

theorem c22250R_82_29 : rowsJ2 82 83 60 340 ≤ 8316093547444 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1879 c22250R_82_30 (by norm_num)

theorem c22250R_82_28 : rowsJ2 82 83 59 340 ≤ 8316093547444 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1878 c22250R_82_29 (by norm_num)

theorem c22250R_82_27 : rowsJ2 82 83 58 340 ≤ 8316093547444 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1877 c22250R_82_28 (by norm_num)

theorem c22250R_82_26 : rowsJ2 82 83 57 340 ≤ 8316093547444 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1876 c22250R_82_27 (by norm_num)

theorem c22250R_82_25 : rowsJ2 82 83 56 340 ≤ 8316093547444 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1875 c22250R_82_26 (by norm_num)

theorem c22250R_82_24 : rowsJ2 82 83 55 340 ≤ 8374474751237 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1874 c22250R_82_25 (by norm_num)

theorem c22250R_82_23 : rowsJ2 82 83 54 340 ≤ 8491723109864 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1873 c22250R_82_24 (by norm_num)

theorem c22250R_82_22 : rowsJ2 82 83 53 340 ≤ 8725896441425 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1872 c22250R_82_23 (by norm_num)

theorem c22250R_82_21 : rowsJ2 82 83 52 340 ≤ 9017900425581 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1871 c22250R_82_22 (by norm_num)

theorem c22250R_82_20 : rowsJ2 82 83 51 340 ≤ 9425074741575 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1870 c22250R_82_21 (by norm_num)

theorem c22250R_82_19 : rowsJ2 82 83 50 340 ≤ 9889241932082 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1869 c22250R_82_20 (by norm_num)

theorem c22250R_82_18 : rowsJ2 82 83 49 340 ≤ 10467078356810 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1868 c22250R_82_19 (by norm_num)

theorem c22250R_82_17 : rowsJ2 82 83 48 340 ≤ 11101264955166 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1867 c22250R_82_18 (by norm_num)

theorem c22250R_82_16 : rowsJ2 82 83 47 340 ≤ 11789853523887 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1866 c22250R_82_17 (by norm_num)

theorem c22250R_82_15 : rowsJ2 82 83 46 340 ≤ 12244559939038 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1865 c22250R_82_16 (by norm_num)

theorem c22250R_82_14 : rowsJ2 82 83 45 340 ≤ 12469004941996 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1864 c22250R_82_15 (by norm_num)

theorem c22250R_82_13 : rowsJ2 82 83 44 340 ≤ 12526188348045 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1863 c22250R_82_14 (by norm_num)

theorem c22250R_82_12 : rowsJ2 82 83 43 340 ≤ 12526188348045 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1862 c22250R_82_13 (by norm_num)

theorem c22250R_82_11 : rowsJ2 82 83 42 340 ≤ 12526188348045 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1861 c22250R_82_12 (by norm_num)

theorem c22250R_82_10 : rowsJ2 82 83 41 340 ≤ 14564007538576 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1860 c22250R_82_11 (by norm_num)

theorem c22250R_82_9 : rowsJ2 82 83 40 340 ≤ 18077008499127 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1859 c22250R_82_10 (by norm_num)

theorem c22250R_82_8 : rowsJ2 82 83 38 340 ≤ 26659482901454 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1858 c22250R_82_9 (by norm_num)

theorem c22250R_82_7 : rowsJ2 82 83 35 340 ≤ 33761367869207 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1857 c22250R_82_8 (by norm_num)

theorem c22250R_82_6 : rowsJ2 82 83 31 340 ≤ 34725138823116 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1856 c22250R_82_7 (by norm_num)

theorem c22250R_82_5 : rowsJ2 82 83 27 340 ≤ 34725138823116 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1855 c22250R_82_6 (by norm_num)

theorem c22250R_82_4 : rowsJ2 82 83 24 340 ≤ 34725138823116 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1854 c22250R_82_5 (by norm_num)

theorem c22250R_82_3 : rowsJ2 82 83 22 340 ≤ 34725138823116 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1853 c22250R_82_4 (by norm_num)

theorem c22250R_82_2 : rowsJ2 82 83 20 340 ≤ 34725138823116 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1852 c22250R_82_3 (by norm_num)

theorem c22250R_82_1 : rowsJ2 82 83 17 340 ≤ 34731405075659 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1851 c22250R_82_2 (by norm_num)

theorem c22250R_82_0 : rowsJ2 82 83 0 340 ≤ 34771389045205 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1850 c22250R_82_1 (by norm_num)

theorem hr22250R_82 : rows2 82 83 ≤ 34771389045205 := rows2_le_of_rowsJ2 82 83 c22250R_82_0

theorem c22250R_83_39 : rowsJ2 83 84 82 340 ≤ 5419783409407 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1931 rows22250R_1932 (by norm_num)

theorem c22250R_83_38 : rowsJ2 83 84 81 340 ≤ 7142313270103 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1930 c22250R_83_39 (by norm_num)

theorem c22250R_83_37 : rowsJ2 83 84 80 340 ≤ 8507805247132 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1929 c22250R_83_38 (by norm_num)

theorem c22250R_83_36 : rowsJ2 83 84 78 340 ≤ 10244501603244 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1928 c22250R_83_37 (by norm_num)

theorem c22250R_83_35 : rowsJ2 83 84 75 340 ≤ 10645736493943 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1927 c22250R_83_36 (by norm_num)

theorem c22250R_83_34 : rowsJ2 83 84 71 340 ≤ 10645736493943 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1926 c22250R_83_35 (by norm_num)

theorem c22250R_83_33 : rowsJ2 83 84 68 340 ≤ 10645736493943 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1925 c22250R_83_34 (by norm_num)

theorem c22250R_83_32 : rowsJ2 83 84 66 340 ≤ 10645736493943 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1924 c22250R_83_33 (by norm_num)

theorem c22250R_83_31 : rowsJ2 83 84 64 340 ≤ 10645736493943 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1923 c22250R_83_32 (by norm_num)

theorem c22250R_83_30 : rowsJ2 83 84 62 340 ≤ 10645736493943 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1922 c22250R_83_31 (by norm_num)

theorem c22250R_83_29 : rowsJ2 83 84 61 340 ≤ 10645736493943 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1921 c22250R_83_30 (by norm_num)

theorem c22250R_83_28 : rowsJ2 83 84 60 340 ≤ 10645736493943 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1920 c22250R_83_29 (by norm_num)

theorem c22250R_83_27 : rowsJ2 83 84 59 340 ≤ 10645736493943 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1919 c22250R_83_28 (by norm_num)

theorem c22250R_83_26 : rowsJ2 83 84 58 340 ≤ 10645736493943 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1918 c22250R_83_27 (by norm_num)

theorem c22250R_83_25 : rowsJ2 83 84 57 340 ≤ 10645736493943 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1917 c22250R_83_26 (by norm_num)

theorem c22250R_83_24 : rowsJ2 83 84 56 340 ≤ 10645736493943 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1916 c22250R_83_25 (by norm_num)

theorem c22250R_83_23 : rowsJ2 83 84 55 340 ≤ 10645736493943 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1915 c22250R_83_24 (by norm_num)

theorem c22250R_83_22 : rowsJ2 83 84 54 340 ≤ 10704242126494 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1914 c22250R_83_23 (by norm_num)

theorem c22250R_83_21 : rowsJ2 83 84 53 340 ≤ 10821751890458 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1913 c22250R_83_22 (by norm_num)

theorem c22250R_83_20 : rowsJ2 83 84 52 340 ≤ 10996783587650 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1912 c22250R_83_21 (by norm_num)

theorem c22250R_83_19 : rowsJ2 83 84 51 340 ≤ 11229886588954 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1911 c22250R_83_20 (by norm_num)

theorem c22250R_83_18 : rowsJ2 83 84 50 340 ≤ 11519679624017 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1910 c22250R_83_19 (by norm_num)

theorem c22250R_83_17 : rowsJ2 83 84 49 340 ≤ 11866762799820 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1909 c22250R_83_18 (by norm_num)

theorem c22250R_83_16 : rowsJ2 83 84 48 340 ≤ 12269852840546 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1908 c22250R_83_17 (by norm_num)

theorem c22250R_83_15 : rowsJ2 83 84 47 340 ≤ 12729600913258 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1907 c22250R_83_16 (by norm_num)

theorem c22250R_83_14 : rowsJ2 83 84 46 340 ≤ 13070346257832 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1906 c22250R_83_15 (by norm_num)

theorem c22250R_83_13 : rowsJ2 83 84 45 340 ≤ 13238747892071 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1905 c22250R_83_14 (by norm_num)

theorem c22250R_83_12 : rowsJ2 83 84 44 340 ≤ 13295491534510 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1904 c22250R_83_13 (by norm_num)

theorem c22250R_83_11 : rowsJ2 83 84 43 340 ≤ 13295491534510 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1903 c22250R_83_12 (by norm_num)

theorem c22250R_83_10 : rowsJ2 83 84 42 340 ≤ 16112536871439 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1902 c22250R_83_11 (by norm_num)

theorem c22250R_83_9 : rowsJ2 83 84 41 340 ≤ 20579534340581 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1901 c22250R_83_10 (by norm_num)

theorem c22250R_83_8 : rowsJ2 83 84 39 340 ≤ 31978943719897 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1900 c22250R_83_9 (by norm_num)

theorem c22250R_83_7 : rowsJ2 83 84 37 340 ≤ 40743446186800 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1899 c22250R_83_8 (by norm_num)

theorem c22250R_83_6 : rowsJ2 83 84 34 340 ≤ 45606094237175 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1898 c22250R_83_7 (by norm_num)

theorem c22250R_83_5 : rowsJ2 83 84 29 340 ≤ 45996989057006 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1897 c22250R_83_6 (by norm_num)

theorem c22250R_83_4 : rowsJ2 83 84 25 340 ≤ 45996989057006 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1896 c22250R_83_5 (by norm_num)

theorem c22250R_83_3 : rowsJ2 83 84 22 340 ≤ 45996989057006 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1895 c22250R_83_4 (by norm_num)

theorem c22250R_83_2 : rowsJ2 83 84 20 340 ≤ 45996989057006 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1894 c22250R_83_3 (by norm_num)

theorem c22250R_83_1 : rowsJ2 83 84 17 340 ≤ 45999083381796 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1893 c22250R_83_2 (by norm_num)

theorem c22250R_83_0 : rowsJ2 83 84 0 340 ≤ 46023660017170 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_1892 c22250R_83_1 (by norm_num)

theorem hr22250R_83 : rows2 83 84 ≤ 46023660017170 := rows2_le_of_rowsJ2 83 84 c22250R_83_0

theorem c22250R_84_40 : rowsJ2 84 85 83 340 ≤ 7042505030505 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1973 rows22250R_1974 (by norm_num)

theorem c22250R_84_39 : rowsJ2 84 85 82 340 ≤ 9357125896675 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1972 c22250R_84_40 (by norm_num)

theorem c22250R_84_38 : rowsJ2 84 85 81 340 ≤ 11066509900363 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1971 c22250R_84_39 (by norm_num)

theorem c22250R_84_37 : rowsJ2 84 85 80 340 ≤ 12300026821075 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1970 c22250R_84_38 (by norm_num)

theorem c22250R_84_36 : rowsJ2 84 85 79 340 ≤ 13264425193365 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1969 c22250R_84_37 (by norm_num)

theorem c22250R_84_35 : rowsJ2 84 85 77 340 ≤ 14181448806221 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1968 c22250R_84_36 (by norm_num)

theorem c22250R_84_34 : rowsJ2 84 85 74 340 ≤ 14302965590388 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1967 c22250R_84_35 (by norm_num)

theorem c22250R_84_33 : rowsJ2 84 85 70 340 ≤ 14302965590388 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1966 c22250R_84_34 (by norm_num)

theorem c22250R_84_32 : rowsJ2 84 85 67 340 ≤ 14302965590388 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1965 c22250R_84_33 (by norm_num)

theorem c22250R_84_31 : rowsJ2 84 85 65 340 ≤ 14302965590388 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1964 c22250R_84_32 (by norm_num)

theorem c22250R_84_30 : rowsJ2 84 85 63 340 ≤ 14302965590388 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1963 c22250R_84_31 (by norm_num)

theorem c22250R_84_29 : rowsJ2 84 85 61 340 ≤ 14302965590388 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1962 c22250R_84_30 (by norm_num)

theorem c22250R_84_28 : rowsJ2 84 85 60 340 ≤ 14302965590388 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1961 c22250R_84_29 (by norm_num)

theorem c22250R_84_27 : rowsJ2 84 85 59 340 ≤ 14302965590388 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1960 c22250R_84_28 (by norm_num)

theorem c22250R_84_26 : rowsJ2 84 85 58 340 ≤ 14302965590388 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1959 c22250R_84_27 (by norm_num)

theorem c22250R_84_25 : rowsJ2 84 85 57 340 ≤ 14302965590388 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1958 c22250R_84_26 (by norm_num)

theorem c22250R_84_24 : rowsJ2 84 85 56 340 ≤ 14302965590388 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1957 c22250R_84_25 (by norm_num)

theorem c22250R_84_23 : rowsJ2 84 85 55 340 ≤ 14302965590388 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1956 c22250R_84_24 (by norm_num)

theorem c22250R_84_22 : rowsJ2 84 85 54 340 ≤ 14302965590388 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1955 c22250R_84_23 (by norm_num)

theorem c22250R_84_21 : rowsJ2 84 85 53 340 ≤ 14361605129388 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1954 c22250R_84_22 (by norm_num)

theorem c22250R_84_20 : rowsJ2 84 85 52 340 ≤ 14420163953376 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1953 c22250R_84_21 (by norm_num)

theorem c22250R_84_19 : rowsJ2 84 85 51 340 ≤ 14536475517462 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1952 c22250R_84_20 (by norm_num)

theorem c22250R_84_18 : rowsJ2 84 85 50 340 ≤ 14652673281667 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1951 c22250R_84_19 (by norm_num)

theorem c22250R_84_17 : rowsJ2 84 85 49 340 ≤ 14825841583448 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1950 c22250R_84_18 (by norm_num)

theorem c22250R_84_16 : rowsJ2 84 85 48 340 ≤ 14998909808112 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1949 c22250R_84_17 (by norm_num)

theorem c22250R_84_15 : rowsJ2 84 85 47 340 ≤ 15228268844821 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1948 c22250R_84_16 (by norm_num)

theorem c22250R_84_14 : rowsJ2 84 85 46 340 ≤ 15399229940189 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1947 c22250R_84_15 (by norm_num)

theorem c22250R_84_13 : rowsJ2 84 85 45 340 ≤ 15511252857409 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1946 c22250R_84_14 (by norm_num)

theorem c22250R_84_12 : rowsJ2 84 85 44 340 ≤ 15567563448540 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1945 c22250R_84_13 (by norm_num)

theorem c22250R_84_11 : rowsJ2 84 85 43 340 ≤ 18577437370798 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1944 c22250R_84_12 (by norm_num)

theorem c22250R_84_10 : rowsJ2 84 85 42 340 ≤ 24043868391654 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1943 c22250R_84_11 (by norm_num)

theorem c22250R_84_9 : rowsJ2 84 85 41 340 ≤ 30866973871669 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1942 c22250R_84_10 (by norm_num)

theorem c22250R_84_8 : rowsJ2 84 85 40 340 ≤ 38387773121775 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1941 c22250R_84_9 (by norm_num)

theorem c22250R_84_7 : rowsJ2 84 85 38 340 ≤ 49859803714141 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1940 c22250R_84_8 (by norm_num)

theorem c22250R_84_6 : rowsJ2 84 85 36 340 ≤ 57150322324936 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1939 c22250R_84_7 (by norm_num)

theorem c22250R_84_5 : rowsJ2 84 85 31 340 ≤ 60283057021245 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1938 c22250R_84_6 (by norm_num)

theorem c22250R_84_4 : rowsJ2 84 85 26 340 ≤ 60283057021245 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1937 c22250R_84_5 (by norm_num)

theorem c22250R_84_3 : rowsJ2 84 85 23 340 ≤ 60283057021245 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1936 c22250R_84_4 (by norm_num)

theorem c22250R_84_2 : rowsJ2 84 85 20 340 ≤ 60283057021245 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1935 c22250R_84_3 (by norm_num)

theorem c22250R_84_1 : rowsJ2 84 85 17 340 ≤ 60283057021245 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1934 c22250R_84_2 (by norm_num)

theorem c22250R_84_0 : rowsJ2 84 85 0 340 ≤ 60296482066060 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_1933 c22250R_84_1 (by norm_num)

theorem hr22250R_84 : rows2 84 85 ≤ 60296482066060 := rows2_le_of_rowsJ2 84 85 c22250R_84_0

theorem c22250R_85_40 : rowsJ2 85 86 84 340 ≤ 8983348421392 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2015 rows22250R_2016 (by norm_num)

theorem c22250R_85_39 : rowsJ2 85 86 83 340 ≤ 12037318257473 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2014 c22250R_85_40 (by norm_num)

theorem c22250R_85_38 : rowsJ2 85 86 82 340 ≤ 14335279443390 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2013 c22250R_85_39 (by norm_num)

theorem c22250R_85_37 : rowsJ2 85 86 81 340 ≤ 16031716721222 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2012 c22250R_85_38 (by norm_num)

theorem c22250R_85_36 : rowsJ2 85 86 80 340 ≤ 17255891092000 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2011 c22250R_85_37 (by norm_num)

theorem c22250R_85_35 : rowsJ2 85 86 79 340 ≤ 18091394660168 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2010 c22250R_85_36 (by norm_num)

theorem c22250R_85_34 : rowsJ2 85 86 77 340 ≤ 18878909807031 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2009 c22250R_85_35 (by norm_num)

theorem c22250R_85_33 : rowsJ2 85 86 73 340 ≤ 18999506233637 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2008 c22250R_85_34 (by norm_num)

theorem c22250R_85_32 : rowsJ2 85 86 69 340 ≤ 18999506233637 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2007 c22250R_85_33 (by norm_num)

theorem c22250R_85_31 : rowsJ2 85 86 66 340 ≤ 18999506233637 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2006 c22250R_85_32 (by norm_num)

theorem c22250R_85_30 : rowsJ2 85 86 64 340 ≤ 18999506233637 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2005 c22250R_85_31 (by norm_num)

theorem c22250R_85_29 : rowsJ2 85 86 62 340 ≤ 18999506233637 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2004 c22250R_85_30 (by norm_num)

theorem c22250R_85_28 : rowsJ2 85 86 60 340 ≤ 18999506233637 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2003 c22250R_85_29 (by norm_num)

theorem c22250R_85_27 : rowsJ2 85 86 59 340 ≤ 18999506233637 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2002 c22250R_85_28 (by norm_num)

theorem c22250R_85_26 : rowsJ2 85 86 58 340 ≤ 18999506233637 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2001 c22250R_85_27 (by norm_num)

theorem c22250R_85_25 : rowsJ2 85 86 57 340 ≤ 18999506233637 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2000 c22250R_85_26 (by norm_num)

theorem c22250R_85_24 : rowsJ2 85 86 56 340 ≤ 18999506233637 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1999 c22250R_85_25 (by norm_num)

theorem c22250R_85_23 : rowsJ2 85 86 55 340 ≤ 18999506233637 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1998 c22250R_85_24 (by norm_num)

theorem c22250R_85_22 : rowsJ2 85 86 54 340 ≤ 18999506233637 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1997 c22250R_85_23 (by norm_num)

theorem c22250R_85_21 : rowsJ2 85 86 53 340 ≤ 18999506233637 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1996 c22250R_85_22 (by norm_num)

theorem c22250R_85_20 : rowsJ2 85 86 52 340 ≤ 18999506233637 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1995 c22250R_85_21 (by norm_num)

theorem c22250R_85_19 : rowsJ2 85 86 51 340 ≤ 18999506233637 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1994 c22250R_85_20 (by norm_num)

theorem c22250R_85_18 : rowsJ2 85 86 50 340 ≤ 18999506233637 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1993 c22250R_85_19 (by norm_num)

theorem c22250R_85_17 : rowsJ2 85 86 49 340 ≤ 18999506233637 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1992 c22250R_85_18 (by norm_num)

theorem c22250R_85_16 : rowsJ2 85 86 48 340 ≤ 18999506233637 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1991 c22250R_85_17 (by norm_num)

theorem c22250R_85_15 : rowsJ2 85 86 47 340 ≤ 18999506233637 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1990 c22250R_85_16 (by norm_num)

theorem c22250R_85_14 : rowsJ2 85 86 46 340 ≤ 18999506233637 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1989 c22250R_85_15 (by norm_num)

theorem c22250R_85_13 : rowsJ2 85 86 45 340 ≤ 18999506233637 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1988 c22250R_85_14 (by norm_num)

theorem c22250R_85_12 : rowsJ2 85 86 44 340 ≤ 22792215865751 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1987 c22250R_85_13 (by norm_num)

theorem c22250R_85_11 : rowsJ2 85 86 43 340 ≤ 29176945740404 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1986 c22250R_85_12 (by norm_num)

theorem c22250R_85_10 : rowsJ2 85 86 42 340 ≤ 37658371947791 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1985 c22250R_85_11 (by norm_num)

theorem c22250R_85_9 : rowsJ2 85 86 41 340 ≤ 47142538568304 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1984 c22250R_85_10 (by norm_num)

theorem c22250R_85_8 : rowsJ2 85 86 40 340 ≤ 55291858082623 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1983 c22250R_85_9 (by norm_num)

theorem c22250R_85_7 : rowsJ2 85 86 38 340 ≤ 67766592098426 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1982 c22250R_85_8 (by norm_num)

theorem c22250R_85_6 : rowsJ2 85 86 36 340 ≤ 75708403968594 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1981 c22250R_85_7 (by norm_num)

theorem c22250R_85_5 : rowsJ2 85 86 32 340 ≤ 79616933180435 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1980 c22250R_85_6 (by norm_num)

theorem c22250R_85_4 : rowsJ2 85 86 27 340 ≤ 79616933180435 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1979 c22250R_85_5 (by norm_num)

theorem c22250R_85_3 : rowsJ2 85 86 23 340 ≤ 79616933180435 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1978 c22250R_85_4 (by norm_num)

theorem c22250R_85_2 : rowsJ2 85 86 20 340 ≤ 79616933180435 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1977 c22250R_85_3 (by norm_num)

theorem c22250R_85_1 : rowsJ2 85 86 17 340 ≤ 79616933180435 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1976 c22250R_85_2 (by norm_num)

theorem c22250R_85_0 : rowsJ2 85 86 0 340 ≤ 79622606256113 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_1975 c22250R_85_1 (by norm_num)

theorem hr22250R_85 : rows2 85 86 ≤ 79622606256113 := rows2_le_of_rowsJ2 85 86 c22250R_85_0

theorem c22250R_86_40 : rowsJ2 86 87 85 340 ≤ 11277748434684 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2057 rows22250R_2058 (by norm_num)

theorem c22250R_86_39 : rowsJ2 86 87 84 340 ≤ 15217525114924 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2056 c22250R_86_40 (by norm_num)

theorem c22250R_86_38 : rowsJ2 86 87 83 340 ≤ 18254732451967 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2055 c22250R_86_39 (by norm_num)

theorem c22250R_86_37 : rowsJ2 86 87 82 340 ≤ 20536437542770 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2054 c22250R_86_38 (by norm_num)

theorem c22250R_86_36 : rowsJ2 86 87 81 340 ≤ 22220122735309 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2053 c22250R_86_37 (by norm_num)

theorem c22250R_86_35 : rowsJ2 86 87 80 340 ≤ 23435095011679 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2052 c22250R_86_36 (by norm_num)

theorem c22250R_86_34 : rowsJ2 86 87 79 340 ≤ 24264318116133 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2051 c22250R_86_35 (by norm_num)

theorem c22250R_86_33 : rowsJ2 86 87 76 340 ≤ 25148428562323 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2050 c22250R_86_34 (by norm_num)

theorem c22250R_86_32 : rowsJ2 86 87 72 340 ≤ 25165603432963 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2049 c22250R_86_33 (by norm_num)

theorem c22250R_86_31 : rowsJ2 86 87 68 340 ≤ 25165603432963 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2048 c22250R_86_32 (by norm_num)

theorem c22250R_86_30 : rowsJ2 86 87 65 340 ≤ 25165603432963 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2047 c22250R_86_31 (by norm_num)

theorem c22250R_86_29 : rowsJ2 86 87 63 340 ≤ 25165603432963 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2046 c22250R_86_30 (by norm_num)

theorem c22250R_86_28 : rowsJ2 86 87 61 340 ≤ 25165603432963 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2045 c22250R_86_29 (by norm_num)

theorem c22250R_86_27 : rowsJ2 86 87 59 340 ≤ 25165603432963 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2044 c22250R_86_28 (by norm_num)

theorem c22250R_86_26 : rowsJ2 86 87 58 340 ≤ 25165603432963 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2043 c22250R_86_27 (by norm_num)

theorem c22250R_86_25 : rowsJ2 86 87 57 340 ≤ 25165603432963 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2042 c22250R_86_26 (by norm_num)

theorem c22250R_86_24 : rowsJ2 86 87 56 340 ≤ 25165603432963 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2041 c22250R_86_25 (by norm_num)

theorem c22250R_86_23 : rowsJ2 86 87 55 340 ≤ 25165603432963 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2040 c22250R_86_24 (by norm_num)

theorem c22250R_86_22 : rowsJ2 86 87 54 340 ≤ 25165603432963 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2039 c22250R_86_23 (by norm_num)

theorem c22250R_86_21 : rowsJ2 86 87 53 340 ≤ 25165603432963 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2038 c22250R_86_22 (by norm_num)

theorem c22250R_86_20 : rowsJ2 86 87 52 340 ≤ 25165603432963 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2037 c22250R_86_21 (by norm_num)

theorem c22250R_86_19 : rowsJ2 86 87 51 340 ≤ 25165603432963 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2036 c22250R_86_20 (by norm_num)

theorem c22250R_86_18 : rowsJ2 86 87 50 340 ≤ 25165603432963 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2035 c22250R_86_19 (by norm_num)

theorem c22250R_86_17 : rowsJ2 86 87 49 340 ≤ 25165603432963 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2034 c22250R_86_18 (by norm_num)

theorem c22250R_86_16 : rowsJ2 86 87 48 340 ≤ 25165603432963 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2033 c22250R_86_17 (by norm_num)

theorem c22250R_86_15 : rowsJ2 86 87 47 340 ≤ 25165603432963 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2032 c22250R_86_16 (by norm_num)

theorem c22250R_86_14 : rowsJ2 86 87 46 340 ≤ 25165603432963 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2031 c22250R_86_15 (by norm_num)

theorem c22250R_86_13 : rowsJ2 86 87 45 340 ≤ 29122331211849 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2030 c22250R_86_14 (by norm_num)

theorem c22250R_86_12 : rowsJ2 86 87 44 340 ≤ 36498595998181 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2029 c22250R_86_13 (by norm_num)

theorem c22250R_86_11 : rowsJ2 86 87 43 340 ≤ 46098545419494 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2028 c22250R_86_12 (by norm_num)

theorem c22250R_86_10 : rowsJ2 86 87 42 340 ≤ 57429778264011 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2027 c22250R_86_11 (by norm_num)

theorem c22250R_86_9 : rowsJ2 86 87 41 340 ≤ 67427644095630 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2026 c22250R_86_10 (by norm_num)

theorem c22250R_86_8 : rowsJ2 86 87 40 340 ≤ 76107418396878 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2025 c22250R_86_9 (by norm_num)

theorem c22250R_86_7 : rowsJ2 86 87 39 340 ≤ 83487442977117 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2024 c22250R_86_8 (by norm_num)

theorem c22250R_86_6 : rowsJ2 86 87 37 340 ≤ 94544327764404 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2023 c22250R_86_7 (by norm_num)

theorem c22250R_86_5 : rowsJ2 86 87 33 340 ≤ 102871712186918 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2022 c22250R_86_6 (by norm_num)

theorem c22250R_86_4 : rowsJ2 86 87 27 340 ≤ 102969340405996 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2021 c22250R_86_5 (by norm_num)

theorem c22250R_86_3 : rowsJ2 86 87 23 340 ≤ 102969340405996 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2020 c22250R_86_4 (by norm_num)

theorem c22250R_86_2 : rowsJ2 86 87 20 340 ≤ 102969340405996 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2019 c22250R_86_3 (by norm_num)

theorem c22250R_86_1 : rowsJ2 86 87 17 340 ≤ 102969340405996 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2018 c22250R_86_2 (by norm_num)

theorem c22250R_86_0 : rowsJ2 86 87 0 340 ≤ 102969340405996 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2017 c22250R_86_1 (by norm_num)

theorem hr22250R_86 : rows2 86 87 ≤ 102969340405996 := rows2_le_of_rowsJ2 86 87 c22250R_86_0

theorem c22250R_87_39 : rowsJ2 87 88 86 340 ≤ 13977740657754 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2098 rows22250R_2099 (by norm_num)

theorem c22250R_87_38 : rowsJ2 87 88 85 340 ≤ 18983461061166 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2097 c22250R_87_39 (by norm_num)

theorem c22250R_87_37 : rowsJ2 87 88 84 340 ≤ 22907903809415 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2096 c22250R_87_38 (by norm_num)

theorem c22250R_87_36 : rowsJ2 87 88 83 340 ≤ 25929031926726 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2095 c22250R_87_37 (by norm_num)

theorem c22250R_87_35 : rowsJ2 87 88 82 340 ≤ 28196249276427 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2094 c22250R_87_36 (by norm_num)

theorem c22250R_87_34 : rowsJ2 87 88 81 340 ≤ 29866007517061 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2093 c22250R_87_35 (by norm_num)

theorem c22250R_87_33 : rowsJ2 87 88 80 340 ≤ 31071915010772 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2092 c22250R_87_34 (by norm_num)

theorem c22250R_87_32 : rowsJ2 87 88 78 340 ≤ 32400251685070 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2091 c22250R_87_33 (by norm_num)

theorem c22250R_87_31 : rowsJ2 87 88 75 340 ≤ 32789512287470 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2090 c22250R_87_32 (by norm_num)

theorem c22250R_87_30 : rowsJ2 87 88 71 340 ≤ 32789512287470 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2089 c22250R_87_31 (by norm_num)

theorem c22250R_87_29 : rowsJ2 87 88 67 340 ≤ 32789512287470 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2088 c22250R_87_30 (by norm_num)

theorem c22250R_87_28 : rowsJ2 87 88 64 340 ≤ 32789512287470 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2087 c22250R_87_29 (by norm_num)

theorem c22250R_87_27 : rowsJ2 87 88 62 340 ≤ 32789512287470 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2086 c22250R_87_28 (by norm_num)

theorem c22250R_87_26 : rowsJ2 87 88 60 340 ≤ 32789512287470 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2085 c22250R_87_27 (by norm_num)

theorem c22250R_87_25 : rowsJ2 87 88 58 340 ≤ 32789512287470 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2084 c22250R_87_26 (by norm_num)

theorem c22250R_87_24 : rowsJ2 87 88 57 340 ≤ 32789512287470 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2083 c22250R_87_25 (by norm_num)

theorem c22250R_87_23 : rowsJ2 87 88 56 340 ≤ 32789512287470 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2082 c22250R_87_24 (by norm_num)

theorem c22250R_87_22 : rowsJ2 87 88 55 340 ≤ 32789512287470 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2081 c22250R_87_23 (by norm_num)

theorem c22250R_87_21 : rowsJ2 87 88 54 340 ≤ 32789512287470 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2080 c22250R_87_22 (by norm_num)

theorem c22250R_87_20 : rowsJ2 87 88 53 340 ≤ 32789512287470 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2079 c22250R_87_21 (by norm_num)

theorem c22250R_87_19 : rowsJ2 87 88 52 340 ≤ 32789512287470 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2078 c22250R_87_20 (by norm_num)

theorem c22250R_87_18 : rowsJ2 87 88 51 340 ≤ 32789512287470 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2077 c22250R_87_19 (by norm_num)

theorem c22250R_87_17 : rowsJ2 87 88 50 340 ≤ 32789512287470 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2076 c22250R_87_18 (by norm_num)

theorem c22250R_87_16 : rowsJ2 87 88 49 340 ≤ 32789512287470 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2075 c22250R_87_17 (by norm_num)

theorem c22250R_87_15 : rowsJ2 87 88 48 340 ≤ 32789512287470 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2074 c22250R_87_16 (by norm_num)

theorem c22250R_87_14 : rowsJ2 87 88 47 340 ≤ 32789512287470 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2073 c22250R_87_15 (by norm_num)

theorem c22250R_87_13 : rowsJ2 87 88 46 340 ≤ 37503023320273 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2072 c22250R_87_14 (by norm_num)

theorem c22250R_87_12 : rowsJ2 87 88 45 340 ≤ 45796021515856 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2071 c22250R_87_13 (by norm_num)

theorem c22250R_87_11 : rowsJ2 87 88 44 340 ≤ 57192312003871 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2070 c22250R_87_12 (by norm_num)

theorem c22250R_87_10 : rowsJ2 87 88 43 340 ≤ 70444626274059 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2069 c22250R_87_11 (by norm_num)

theorem c22250R_87_9 : rowsJ2 87 88 42 340 ≤ 82272506204682 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2068 c22250R_87_10 (by norm_num)

theorem c22250R_87_8 : rowsJ2 87 88 41 340 ≤ 92783569236116 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2067 c22250R_87_9 (by norm_num)

theorem c22250R_87_7 : rowsJ2 87 88 40 340 ≤ 101993128596143 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2066 c22250R_87_8 (by norm_num)

theorem c22250R_87_6 : rowsJ2 87 88 38 340 ≤ 116584516688422 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2065 c22250R_87_7 (by norm_num)

theorem c22250R_87_5 : rowsJ2 87 88 35 340 ≤ 128782784980781 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2064 c22250R_87_6 (by norm_num)

theorem c22250R_87_4 : rowsJ2 87 88 29 340 ≤ 131696057920019 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2063 c22250R_87_5 (by norm_num)

theorem c22250R_87_3 : rowsJ2 87 88 24 340 ≤ 131696057920019 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2062 c22250R_87_4 (by norm_num)

theorem c22250R_87_2 : rowsJ2 87 88 20 340 ≤ 131696057920019 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2061 c22250R_87_3 (by norm_num)

theorem c22250R_87_1 : rowsJ2 87 88 17 340 ≤ 131696057920019 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2060 c22250R_87_2 (by norm_num)

theorem c22250R_87_0 : rowsJ2 87 88 0 340 ≤ 131696057920019 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2059 c22250R_87_1 (by norm_num)

theorem hr22250R_87 : rows2 87 88 ≤ 131696057920019 := rows2_le_of_rowsJ2 87 88 c22250R_87_0

theorem c22250R_88_39 : rowsJ2 88 89 87 340 ≤ 16441740416292 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2139 rows22250R_2140 (by norm_num)

theorem c22250R_88_38 : rowsJ2 88 89 86 340 ≤ 22702040956885 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2138 c22250R_88_39 (by norm_num)

theorem c22250R_88_37 : rowsJ2 88 89 85 340 ≤ 27699220400133 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2137 c22250R_88_38 (by norm_num)

theorem c22250R_88_36 : rowsJ2 88 89 84 340 ≤ 31609548843636 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2136 c22250R_88_37 (by norm_num)

theorem c22250R_88_35 : rowsJ2 88 89 83 340 ≤ 34615295137136 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2135 c22250R_88_36 (by norm_num)

theorem c22250R_88_34 : rowsJ2 88 89 82 340 ≤ 36867015602206 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2134 c22250R_88_35 (by norm_num)

theorem c22250R_88_33 : rowsJ2 88 89 81 340 ≤ 38524458458650 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2133 c22250R_88_34 (by norm_num)

theorem c22250R_88_32 : rowsJ2 88 89 80 340 ≤ 39721435430811 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2132 c22250R_88_33 (by norm_num)

theorem c22250R_88_31 : rowsJ2 88 89 78 340 ≤ 41039934916640 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2131 c22250R_88_32 (by norm_num)

theorem c22250R_88_30 : rowsJ2 88 89 75 340 ≤ 41426312793607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2130 c22250R_88_31 (by norm_num)

theorem c22250R_88_29 : rowsJ2 88 89 70 340 ≤ 41426312793607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2129 c22250R_88_30 (by norm_num)

theorem c22250R_88_28 : rowsJ2 88 89 66 340 ≤ 41426312793607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2128 c22250R_88_29 (by norm_num)

theorem c22250R_88_27 : rowsJ2 88 89 63 340 ≤ 41426312793607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2127 c22250R_88_28 (by norm_num)

theorem c22250R_88_26 : rowsJ2 88 89 61 340 ≤ 41426312793607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2126 c22250R_88_27 (by norm_num)

theorem c22250R_88_25 : rowsJ2 88 89 59 340 ≤ 41426312793607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2125 c22250R_88_26 (by norm_num)

theorem c22250R_88_24 : rowsJ2 88 89 57 340 ≤ 41426312793607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2124 c22250R_88_25 (by norm_num)

theorem c22250R_88_23 : rowsJ2 88 89 56 340 ≤ 41426312793607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2123 c22250R_88_24 (by norm_num)

theorem c22250R_88_22 : rowsJ2 88 89 55 340 ≤ 41426312793607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2122 c22250R_88_23 (by norm_num)

theorem c22250R_88_21 : rowsJ2 88 89 54 340 ≤ 41426312793607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2121 c22250R_88_22 (by norm_num)

theorem c22250R_88_20 : rowsJ2 88 89 53 340 ≤ 41426312793607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2120 c22250R_88_21 (by norm_num)

theorem c22250R_88_19 : rowsJ2 88 89 52 340 ≤ 41426312793607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2119 c22250R_88_20 (by norm_num)

theorem c22250R_88_18 : rowsJ2 88 89 51 340 ≤ 41426312793607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2118 c22250R_88_19 (by norm_num)

theorem c22250R_88_17 : rowsJ2 88 89 50 340 ≤ 41426312793607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2117 c22250R_88_18 (by norm_num)

theorem c22250R_88_16 : rowsJ2 88 89 49 340 ≤ 41426312793607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2116 c22250R_88_17 (by norm_num)

theorem c22250R_88_15 : rowsJ2 88 89 48 340 ≤ 41426312793607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2115 c22250R_88_16 (by norm_num)

theorem c22250R_88_14 : rowsJ2 88 89 47 340 ≤ 45197846942492 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2114 c22250R_88_15 (by norm_num)

theorem c22250R_88_13 : rowsJ2 88 89 46 340 ≤ 53692782050662 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2113 c22250R_88_14 (by norm_num)

theorem c22250R_88_12 : rowsJ2 88 89 45 340 ≤ 66178144701871 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2112 c22250R_88_13 (by norm_num)

theorem c22250R_88_11 : rowsJ2 88 89 44 340 ≤ 81388446007921 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2111 c22250R_88_12 (by norm_num)

theorem c22250R_88_10 : rowsJ2 88 89 43 340 ≤ 95216724956382 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2110 c22250R_88_11 (by norm_num)

theorem c22250R_88_9 : rowsJ2 88 89 42 340 ≤ 107540455718296 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2109 c22250R_88_10 (by norm_num)

theorem c22250R_88_8 : rowsJ2 88 89 41 340 ≤ 118466131758487 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2108 c22250R_88_9 (by norm_num)

theorem c22250R_88_7 : rowsJ2 88 89 40 340 ≤ 128105600902440 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2107 c22250R_88_8 (by norm_num)

theorem c22250R_88_6 : rowsJ2 88 89 38 340 ≤ 143602661077696 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2106 c22250R_88_7 (by norm_num)

theorem c22250R_88_5 : rowsJ2 88 89 35 340 ≤ 156842922307043 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2105 c22250R_88_6 (by norm_num)

theorem c22250R_88_4 : rowsJ2 88 89 30 340 ≤ 160551770642765 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2104 c22250R_88_5 (by norm_num)

theorem c22250R_88_3 : rowsJ2 88 89 24 340 ≤ 160551770642765 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2103 c22250R_88_4 (by norm_num)

theorem c22250R_88_2 : rowsJ2 88 89 20 340 ≤ 160551770642765 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2102 c22250R_88_3 (by norm_num)

theorem c22250R_88_1 : rowsJ2 88 89 17 340 ≤ 160551770642765 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2101 c22250R_88_2 (by norm_num)

theorem c22250R_88_0 : rowsJ2 88 89 0 340 ≤ 160551770642765 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2100 c22250R_88_1 (by norm_num)

theorem hr22250R_88 : rows2 88 89 ≤ 160551770642765 := rows2_le_of_rowsJ2 88 89 c22250R_88_0

theorem c22250R_89_39 : rowsJ2 89 90 88 340 ≤ 14296853608656 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2180 rows22250R_2181 (by norm_num)

theorem c22250R_89_38 : rowsJ2 89 90 87 340 ≤ 21747448051293 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2179 c22250R_89_39 (by norm_num)

theorem c22250R_89_37 : rowsJ2 89 90 86 340 ≤ 28010215405064 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2178 c22250R_89_38 (by norm_num)

theorem c22250R_89_36 : rowsJ2 89 90 85 340 ≤ 33000839412263 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2177 c22250R_89_37 (by norm_num)

theorem c22250R_89_35 : rowsJ2 89 90 84 340 ≤ 36899670977055 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2176 c22250R_89_36 (by norm_num)

theorem c22250R_89_34 : rowsJ2 89 90 83 340 ≤ 39889408289362 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2175 c22250R_89_35 (by norm_num)

theorem c22250R_89_33 : rowsJ2 89 90 82 340 ≤ 42126036980184 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2174 c22250R_89_34 (by norm_num)

theorem c22250R_89_32 : rowsJ2 89 90 81 340 ≤ 43771345917379 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2173 c22250R_89_33 (by norm_num)

theorem c22250R_89_31 : rowsJ2 89 90 80 340 ≤ 44959523668155 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2172 c22250R_89_32 (by norm_num)

theorem c22250R_89_30 : rowsJ2 89 90 78 340 ≤ 46268330595859 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2171 c22250R_89_31 (by norm_num)

theorem c22250R_89_29 : rowsJ2 89 90 75 340 ≤ 46651868130398 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2170 c22250R_89_30 (by norm_num)

theorem c22250R_89_28 : rowsJ2 89 90 70 340 ≤ 46651868130398 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2169 c22250R_89_29 (by norm_num)

theorem c22250R_89_27 : rowsJ2 89 90 65 340 ≤ 46651868130398 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2168 c22250R_89_28 (by norm_num)

theorem c22250R_89_26 : rowsJ2 89 90 62 340 ≤ 46651868130398 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2167 c22250R_89_27 (by norm_num)

theorem c22250R_89_25 : rowsJ2 89 90 60 340 ≤ 46651868130398 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2166 c22250R_89_26 (by norm_num)

theorem c22250R_89_24 : rowsJ2 89 90 58 340 ≤ 46651868130398 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2165 c22250R_89_25 (by norm_num)

theorem c22250R_89_23 : rowsJ2 89 90 56 340 ≤ 46651868130398 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2164 c22250R_89_24 (by norm_num)

theorem c22250R_89_22 : rowsJ2 89 90 55 340 ≤ 46651868130398 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2163 c22250R_89_23 (by norm_num)

theorem c22250R_89_21 : rowsJ2 89 90 54 340 ≤ 46651868130398 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2162 c22250R_89_22 (by norm_num)

theorem c22250R_89_20 : rowsJ2 89 90 53 340 ≤ 46651868130398 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2161 c22250R_89_21 (by norm_num)

theorem c22250R_89_19 : rowsJ2 89 90 52 340 ≤ 46651868130398 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2160 c22250R_89_20 (by norm_num)

theorem c22250R_89_18 : rowsJ2 89 90 51 340 ≤ 46651868130398 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2159 c22250R_89_19 (by norm_num)

theorem c22250R_89_17 : rowsJ2 89 90 50 340 ≤ 46651868130398 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2158 c22250R_89_18 (by norm_num)

theorem c22250R_89_16 : rowsJ2 89 90 49 340 ≤ 46651868130398 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2157 c22250R_89_17 (by norm_num)

theorem c22250R_89_15 : rowsJ2 89 90 48 340 ≤ 50017199506539 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2156 c22250R_89_16 (by norm_num)

theorem c22250R_89_14 : rowsJ2 89 90 47 340 ≤ 57166379747027 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2155 c22250R_89_15 (by norm_num)

theorem c22250R_89_13 : rowsJ2 89 90 46 340 ≤ 69049363633505 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2154 c22250R_89_14 (by norm_num)

theorem c22250R_89_12 : rowsJ2 89 90 45 340 ≤ 86022539059386 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2153 c22250R_89_13 (by norm_num)

theorem c22250R_89_11 : rowsJ2 89 90 44 340 ≤ 101873754498438 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2152 c22250R_89_12 (by norm_num)

theorem c22250R_89_10 : rowsJ2 89 90 43 340 ≤ 116320247784265 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2151 c22250R_89_11 (by norm_num)

theorem c22250R_89_9 : rowsJ2 89 90 42 340 ≤ 129238266722495 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2150 c22250R_89_10 (by norm_num)

theorem c22250R_89_8 : rowsJ2 89 90 41 340 ≤ 140676560805273 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2149 c22250R_89_9 (by norm_num)

theorem c22250R_89_7 : rowsJ2 89 90 40 340 ≤ 150745789511997 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2148 c22250R_89_8 (by norm_num)

theorem c22250R_89_6 : rowsJ2 89 90 38 340 ≤ 167147764041676 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2147 c22250R_89_7 (by norm_num)

theorem c22250R_89_5 : rowsJ2 89 90 36 340 ≤ 178205666659212 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2146 c22250R_89_6 (by norm_num)

theorem c22250R_89_4 : rowsJ2 89 90 32 340 ≤ 185934638788457 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2145 c22250R_89_5 (by norm_num)

theorem c22250R_89_3 : rowsJ2 89 90 25 340 ≤ 186035102983775 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2144 c22250R_89_4 (by norm_num)

theorem c22250R_89_2 : rowsJ2 89 90 20 340 ≤ 186035102983775 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2143 c22250R_89_3 (by norm_num)

theorem c22250R_89_1 : rowsJ2 89 90 16 340 ≤ 186035102983775 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2142 c22250R_89_2 (by norm_num)

theorem c22250R_89_0 : rowsJ2 89 90 0 340 ≤ 186035102983775 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2141 c22250R_89_1 (by norm_num)

theorem hr22250R_89 : rows2 89 90 ≤ 186035102983775 := rows2_le_of_rowsJ2 89 90 c22250R_89_0

theorem c22250R_90_40 : rowsJ2 90 91 89 340 ≤ 10718927634761 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2222 rows22250R_2223 (by norm_num)

theorem c22250R_90_39 : rowsJ2 90 91 88 340 ≤ 17098670049391 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2221 c22250R_90_40 (by norm_num)

theorem c22250R_90_38 : rowsJ2 90 91 87 340 ≤ 24266924712622 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2220 c22250R_90_39 (by norm_num)

theorem c22250R_90_37 : rowsJ2 90 91 86 340 ≤ 30436790807591 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2219 c22250R_90_38 (by norm_num)

theorem c22250R_90_36 : rowsJ2 90 91 85 340 ≤ 35422944958421 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2218 c22250R_90_37 (by norm_num)

theorem c22250R_90_35 : rowsJ2 90 91 84 340 ≤ 39310203835482 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2217 c22250R_90_36 (by norm_num)

theorem c22250R_90_34 : rowsJ2 90 91 83 340 ≤ 42286078741986 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2216 c22250R_90_35 (by norm_num)

theorem c22250R_90_33 : rowsJ2 90 91 82 340 ≤ 44508022648627 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2215 c22250R_90_34 (by norm_num)

theorem c22250R_90_32 : rowsJ2 90 91 81 340 ≤ 46140021193188 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2214 c22250R_90_33 (by norm_num)

theorem c22250R_90_31 : rowsJ2 90 91 80 340 ≤ 47319528148229 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2213 c22250R_90_32 (by norm_num)

theorem c22250R_90_30 : rowsJ2 90 91 78 340 ≤ 48618783981813 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2212 c22250R_90_31 (by norm_num)

theorem c22250R_90_29 : rowsJ2 90 91 74 340 ≤ 48999522629050 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2211 c22250R_90_30 (by norm_num)

theorem c22250R_90_28 : rowsJ2 90 91 69 340 ≤ 48999522629050 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2210 c22250R_90_29 (by norm_num)

theorem c22250R_90_27 : rowsJ2 90 91 64 340 ≤ 48999522629050 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2209 c22250R_90_28 (by norm_num)

theorem c22250R_90_26 : rowsJ2 90 91 61 340 ≤ 48999522629050 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2208 c22250R_90_27 (by norm_num)

theorem c22250R_90_25 : rowsJ2 90 91 59 340 ≤ 48999522629050 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2207 c22250R_90_26 (by norm_num)

theorem c22250R_90_24 : rowsJ2 90 91 57 340 ≤ 48999522629050 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2206 c22250R_90_25 (by norm_num)

theorem c22250R_90_23 : rowsJ2 90 91 55 340 ≤ 48999522629050 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2205 c22250R_90_24 (by norm_num)

theorem c22250R_90_22 : rowsJ2 90 91 54 340 ≤ 48999522629050 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2204 c22250R_90_23 (by norm_num)

theorem c22250R_90_21 : rowsJ2 90 91 53 340 ≤ 48999522629050 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2203 c22250R_90_22 (by norm_num)

theorem c22250R_90_20 : rowsJ2 90 91 52 340 ≤ 48999522629050 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2202 c22250R_90_21 (by norm_num)

theorem c22250R_90_19 : rowsJ2 90 91 51 340 ≤ 48999522629050 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2201 c22250R_90_20 (by norm_num)

theorem c22250R_90_18 : rowsJ2 90 91 50 340 ≤ 48999522629050 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2200 c22250R_90_19 (by norm_num)

theorem c22250R_90_17 : rowsJ2 90 91 49 340 ≤ 51390442895817 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2199 c22250R_90_18 (by norm_num)

theorem c22250R_90_16 : rowsJ2 90 91 48 340 ≤ 57093210661879 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2198 c22250R_90_17 (by norm_num)

theorem c22250R_90_15 : rowsJ2 90 91 47 340 ≤ 66587205072117 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2197 c22250R_90_16 (by norm_num)

theorem c22250R_90_14 : rowsJ2 90 91 46 340 ≤ 80762103079640 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2196 c22250R_90_15 (by norm_num)

theorem c22250R_90_13 : rowsJ2 90 91 45 340 ≤ 96743330112217 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2195 c22250R_90_14 (by norm_num)

theorem c22250R_90_12 : rowsJ2 90 91 44 340 ≤ 113078831952145 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2194 c22250R_90_13 (by norm_num)

theorem c22250R_90_11 : rowsJ2 90 91 43 340 ≤ 128145599010039 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2193 c22250R_90_12 (by norm_num)

theorem c22250R_90_10 : rowsJ2 90 91 42 340 ≤ 141658728931794 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2192 c22250R_90_11 (by norm_num)

theorem c22250R_90_9 : rowsJ2 90 91 41 340 ≤ 153608831956165 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2191 c22250R_90_10 (by norm_num)

theorem c22250R_90_8 : rowsJ2 90 91 40 340 ≤ 164105425537496 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2190 c22250R_90_9 (by norm_num)

theorem c22250R_90_7 : rowsJ2 90 91 39 340 ≤ 173263581620712 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2189 c22250R_90_8 (by norm_num)

theorem c22250R_90_6 : rowsJ2 90 91 38 340 ≤ 181204433260933 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2188 c22250R_90_7 (by norm_num)

theorem c22250R_90_5 : rowsJ2 90 91 36 340 ≤ 193118188127513 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2187 c22250R_90_6 (by norm_num)

theorem c22250R_90_4 : rowsJ2 90 91 32 340 ≤ 201829764021853 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2186 c22250R_90_5 (by norm_num)

theorem c22250R_90_3 : rowsJ2 90 91 25 340 ≤ 202031832268735 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2185 c22250R_90_4 (by norm_num)

theorem c22250R_90_2 : rowsJ2 90 91 20 340 ≤ 202031832268735 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2184 c22250R_90_3 (by norm_num)

theorem c22250R_90_1 : rowsJ2 90 91 16 340 ≤ 202031832268735 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2183 c22250R_90_2 (by norm_num)

theorem c22250R_90_0 : rowsJ2 90 91 0 340 ≤ 202031832268735 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2182 c22250R_90_1 (by norm_num)

theorem hr22250R_90 : rows2 90 91 ≤ 202031832268735 := rows2_le_of_rowsJ2 90 91 c22250R_90_0

theorem c22250R_91_41 : rowsJ2 91 92 90 340 ≤ 8890701645987 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2265 rows22250R_2266 (by norm_num)

theorem c22250R_91_40 : rowsJ2 91 92 89 340 ≤ 13601285536345 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2264 c22250R_91_41 (by norm_num)

theorem c22250R_91_39 : rowsJ2 91 92 88 340 ≤ 18926708204892 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2263 c22250R_91_40 (by norm_num)

theorem c22250R_91_38 : rowsJ2 91 92 87 340 ≤ 24956993598317 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2262 c22250R_91_39 (by norm_num)

theorem c22250R_91_37 : rowsJ2 91 92 86 340 ≤ 30937135985673 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2261 c22250R_91_38 (by norm_num)

theorem c22250R_91_36 : rowsJ2 91 92 85 340 ≤ 35919699052520 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2260 c22250R_91_37 (by norm_num)

theorem c22250R_91_35 : rowsJ2 91 92 84 340 ≤ 39796754802955 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2259 c22250R_91_36 (by norm_num)

theorem c22250R_91_34 : rowsJ2 91 92 83 340 ≤ 42759521308772 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2258 c22250R_91_35 (by norm_num)

theorem c22250R_91_33 : rowsJ2 91 92 82 340 ≤ 44967203049143 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2257 c22250R_91_34 (by norm_num)

theorem c22250R_91_32 : rowsJ2 91 92 81 340 ≤ 46586124228492 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2256 c22250R_91_33 (by norm_num)

theorem c22250R_91_31 : rowsJ2 91 92 80 340 ≤ 47757086022239 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2255 c22250R_91_32 (by norm_num)

theorem c22250R_91_30 : rowsJ2 91 92 79 340 ≤ 48556271808366 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2254 c22250R_91_31 (by norm_num)

theorem c22250R_91_29 : rowsJ2 91 92 77 340 ≤ 49309555140369 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2253 c22250R_91_30 (by norm_num)

theorem c22250R_91_28 : rowsJ2 91 92 73 340 ≤ 49424909465202 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2252 c22250R_91_29 (by norm_num)

theorem c22250R_91_27 : rowsJ2 91 92 68 340 ≤ 49424909465202 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2251 c22250R_91_28 (by norm_num)

theorem c22250R_91_26 : rowsJ2 91 92 63 340 ≤ 49424909465202 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2250 c22250R_91_27 (by norm_num)

theorem c22250R_91_25 : rowsJ2 91 92 60 340 ≤ 49424909465202 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2249 c22250R_91_26 (by norm_num)

theorem c22250R_91_24 : rowsJ2 91 92 58 340 ≤ 49424909465202 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2248 c22250R_91_25 (by norm_num)

theorem c22250R_91_23 : rowsJ2 91 92 56 340 ≤ 49424909465202 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2247 c22250R_91_24 (by norm_num)

theorem c22250R_91_22 : rowsJ2 91 92 54 340 ≤ 49424909465202 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2246 c22250R_91_23 (by norm_num)

theorem c22250R_91_21 : rowsJ2 91 92 53 340 ≤ 49424909465202 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2245 c22250R_91_22 (by norm_num)

theorem c22250R_91_20 : rowsJ2 91 92 52 340 ≤ 49424909465202 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2244 c22250R_91_21 (by norm_num)

theorem c22250R_91_19 : rowsJ2 91 92 51 340 ≤ 49424909465202 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2243 c22250R_91_20 (by norm_num)

theorem c22250R_91_18 : rowsJ2 91 92 50 340 ≤ 51495249735149 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2242 c22250R_91_19 (by norm_num)

theorem c22250R_91_17 : rowsJ2 91 92 49 340 ≤ 55964317079582 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2241 c22250R_91_18 (by norm_num)

theorem c22250R_91_16 : rowsJ2 91 92 48 340 ≤ 63751828748765 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2240 c22250R_91_17 (by norm_num)

theorem c22250R_91_15 : rowsJ2 91 92 47 340 ≤ 75279310524414 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2239 c22250R_91_16 (by norm_num)

theorem c22250R_91_14 : rowsJ2 91 92 46 340 ≤ 88530766985691 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2238 c22250R_91_15 (by norm_num)

theorem c22250R_91_13 : rowsJ2 91 92 45 340 ≤ 103525674574976 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2237 c22250R_91_14 (by norm_num)

theorem c22250R_91_12 : rowsJ2 91 92 44 340 ≤ 120343659907442 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2236 c22250R_91_13 (by norm_num)

theorem c22250R_91_11 : rowsJ2 91 92 43 340 ≤ 135971959745106 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2235 c22250R_91_12 (by norm_num)

theorem c22250R_91_10 : rowsJ2 91 92 42 340 ≤ 150182927071579 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2234 c22250R_91_11 (by norm_num)

theorem c22250R_91_9 : rowsJ2 91 92 41 340 ≤ 162746995565500 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2233 c22250R_91_10 (by norm_num)

theorem c22250R_91_8 : rowsJ2 91 92 40 340 ≤ 173772615665221 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2232 c22250R_91_9 (by norm_num)

theorem c22250R_91_7 : rowsJ2 91 92 39 340 ≤ 183373649648264 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2231 c22250R_91_8 (by norm_num)

theorem c22250R_91_6 : rowsJ2 91 92 38 340 ≤ 191669874459305 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2230 c22250R_91_7 (by norm_num)

theorem c22250R_91_5 : rowsJ2 91 92 36 340 ≤ 204332730980204 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2229 c22250R_91_6 (by norm_num)

theorem c22250R_91_4 : rowsJ2 91 92 33 340 ≤ 212917421046949 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2228 c22250R_91_5 (by norm_num)

theorem c22250R_91_3 : rowsJ2 91 92 26 340 ≤ 214433609262792 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2227 c22250R_91_4 (by norm_num)

theorem c22250R_91_2 : rowsJ2 91 92 20 340 ≤ 214433609262792 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2226 c22250R_91_3 (by norm_num)

theorem c22250R_91_1 : rowsJ2 91 92 16 340 ≤ 214433609262792 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2225 c22250R_91_2 (by norm_num)

theorem c22250R_91_0 : rowsJ2 91 92 0 340 ≤ 214433609262792 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2224 c22250R_91_1 (by norm_num)

theorem hr22250R_91 : rows2 91 92 ≤ 214433609262792 := rows2_le_of_rowsJ2 91 92 c22250R_91_0

theorem c22250R_92_40 : rowsJ2 92 93 91 340 ≤ 7879248367038 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2307 rows22250R_2308 (by norm_num)

theorem c22250R_92_39 : rowsJ2 92 93 90 340 ≤ 11884489946689 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2306 c22250R_92_40 (by norm_num)

theorem c22250R_92_38 : rowsJ2 92 93 89 340 ≤ 16045132949686 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2305 c22250R_92_39 (by norm_num)

theorem c22250R_92_37 : rowsJ2 92 93 88 340 ≤ 20429552085463 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2304 c22250R_92_38 (by norm_num)

theorem c22250R_92_36 : rowsJ2 92 93 87 340 ≤ 25429415402620 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2303 c22250R_92_37 (by norm_num)

theorem c22250R_92_35 : rowsJ2 92 93 86 340 ≤ 31117267557655 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2302 c22250R_92_36 (by norm_num)

theorem c22250R_92_34 : rowsJ2 92 93 85 340 ≤ 36001303023643 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2301 c22250R_92_35 (by norm_num)

theorem c22250R_92_33 : rowsJ2 92 93 84 340 ≤ 39869587662612 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2300 c22250R_92_34 (by norm_num)

theorem c22250R_92_32 : rowsJ2 92 93 83 340 ≤ 42818693813057 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2299 c22250R_92_33 (by norm_num)

theorem c22250R_92_31 : rowsJ2 92 93 82 340 ≤ 45012527140516 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2298 c22250R_92_32 (by norm_num)

theorem c22250R_92_30 : rowsJ2 92 93 81 340 ≤ 46619955259001 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2297 c22250R_92_31 (by norm_num)

theorem c22250R_92_29 : rowsJ2 92 93 80 340 ≤ 47781139228695 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2296 c22250R_92_30 (by norm_num)

theorem c22250R_92_28 : rowsJ2 92 93 79 340 ≤ 48574576806171 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2295 c22250R_92_29 (by norm_num)

theorem c22250R_92_27 : rowsJ2 92 93 77 340 ≤ 49322442086654 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2294 c22250R_92_28 (by norm_num)

theorem c22250R_92_26 : rowsJ2 92 93 73 340 ≤ 49436966716141 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2293 c22250R_92_27 (by norm_num)

theorem c22250R_92_25 : rowsJ2 92 93 67 340 ≤ 49436966716141 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2292 c22250R_92_26 (by norm_num)

theorem c22250R_92_24 : rowsJ2 92 93 62 340 ≤ 49436966716141 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2291 c22250R_92_25 (by norm_num)

theorem c22250R_92_23 : rowsJ2 92 93 59 340 ≤ 49436966716141 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2290 c22250R_92_24 (by norm_num)

theorem c22250R_92_22 : rowsJ2 92 93 57 340 ≤ 49436966716141 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2289 c22250R_92_23 (by norm_num)

theorem c22250R_92_21 : rowsJ2 92 93 55 340 ≤ 49436966716141 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2288 c22250R_92_22 (by norm_num)

theorem c22250R_92_20 : rowsJ2 92 93 53 340 ≤ 49436966716141 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2287 c22250R_92_21 (by norm_num)

theorem c22250R_92_19 : rowsJ2 92 93 52 340 ≤ 49436966716141 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2286 c22250R_92_20 (by norm_num)

theorem c22250R_92_18 : rowsJ2 92 93 51 340 ≤ 50825505535271 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2285 c22250R_92_19 (by norm_num)

theorem c22250R_92_17 : rowsJ2 92 93 50 340 ≤ 54287383049232 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2284 c22250R_92_18 (by norm_num)

theorem c22250R_92_16 : rowsJ2 92 93 49 340 ≤ 60152539744091 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2283 c22250R_92_17 (by norm_num)

theorem c22250R_92_15 : rowsJ2 92 93 48 340 ≤ 69278531616436 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2282 c22250R_92_16 (by norm_num)

theorem c22250R_92_14 : rowsJ2 92 93 47 340 ≤ 79950120805785 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2281 c22250R_92_15 (by norm_num)

theorem c22250R_92_13 : rowsJ2 92 93 46 340 ≤ 92282930427230 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2280 c22250R_92_14 (by norm_num)

theorem c22250R_92_12 : rowsJ2 92 93 45 340 ≤ 106355563894991 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2279 c22250R_92_13 (by norm_num)

theorem c22250R_92_11 : rowsJ2 92 93 44 340 ≤ 122188190615587 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2278 c22250R_92_12 (by norm_num)

theorem c22250R_92_10 : rowsJ2 92 93 43 340 ≤ 138376777585838 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2277 c22250R_92_11 (by norm_num)

theorem c22250R_92_9 : rowsJ2 92 93 42 340 ≤ 153227131625263 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2276 c22250R_92_10 (by norm_num)

theorem c22250R_92_8 : rowsJ2 92 93 41 340 ≤ 166509517559755 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2275 c22250R_92_9 (by norm_num)

theorem c22250R_92_7 : rowsJ2 92 93 40 340 ≤ 178167949217362 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2274 c22250R_92_8 (by norm_num)

theorem c22250R_92_6 : rowsJ2 92 93 39 340 ≤ 188315155494162 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2273 c22250R_92_7 (by norm_num)

theorem c22250R_92_5 : rowsJ2 92 93 37 340 ≤ 204556176426251 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2272 c22250R_92_6 (by norm_num)

theorem c22250R_92_4 : rowsJ2 92 93 34 340 ≤ 217872947055544 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2271 c22250R_92_5 (by norm_num)

theorem c22250R_92_3 : rowsJ2 92 93 29 340 ≤ 221874574740920 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2270 c22250R_92_4 (by norm_num)

theorem c22250R_92_2 : rowsJ2 92 93 21 340 ≤ 221874574740920 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2269 c22250R_92_3 (by norm_num)

theorem c22250R_92_1 : rowsJ2 92 93 16 340 ≤ 221874574740920 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2268 c22250R_92_2 (by norm_num)

theorem c22250R_92_0 : rowsJ2 92 93 0 340 ≤ 221874574740920 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2267 c22250R_92_1 (by norm_num)

theorem hr22250R_92 : rows2 92 93 ≤ 221874574740920 := rows2_le_of_rowsJ2 92 93 c22250R_92_0

theorem c22250R_93_40 : rowsJ2 93 94 92 340 ≤ 7405697018876 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2349 rows22250R_2350 (by norm_num)

theorem c22250R_93_39 : rowsJ2 93 94 91 340 ≤ 10970670499587 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2348 c22250R_93_40 (by norm_num)

theorem c22250R_93_38 : rowsJ2 93 94 90 340 ≤ 14550084720645 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2347 c22250R_93_39 (by norm_num)

theorem c22250R_93_37 : rowsJ2 93 94 89 340 ≤ 18233559140497 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2346 c22250R_93_38 (by norm_num)

theorem c22250R_93_36 : rowsJ2 93 94 88 340 ≤ 22091351589563 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2345 c22250R_93_37 (by norm_num)

theorem c22250R_93_35 : rowsJ2 93 94 87 340 ≤ 26173417985915 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2344 c22250R_93_36 (by norm_num)

theorem c22250R_93_34 : rowsJ2 93 94 86 340 ≤ 30854132770901 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2343 c22250R_93_35 (by norm_num)

theorem c22250R_93_33 : rowsJ2 93 94 85 340 ≤ 35540407608093 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2342 c22250R_93_34 (by norm_num)

theorem c22250R_93_32 : rowsJ2 93 94 84 340 ≤ 39401448005124 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2341 c22250R_93_33 (by norm_num)

theorem c22250R_93_31 : rowsJ2 93 94 83 340 ≤ 42337759778130 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2340 c22250R_93_32 (by norm_num)

theorem c22250R_93_30 : rowsJ2 93 94 82 340 ≤ 44518163302598 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2339 c22250R_93_31 (by norm_num)

theorem c22250R_93_29 : rowsJ2 93 94 81 340 ≤ 46112920075226 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2338 c22250R_93_30 (by norm_num)

theorem c22250R_93_28 : rowsJ2 93 94 80 340 ≤ 47265862189547 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2337 c22250R_93_29 (by norm_num)

theorem c22250R_93_27 : rowsJ2 93 94 79 340 ≤ 48053633656794 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2336 c22250R_93_28 (by norm_num)

theorem c22250R_93_26 : rowsJ2 93 94 77 340 ≤ 48796158268729 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2335 c22250R_93_27 (by norm_num)

theorem c22250R_93_25 : rowsJ2 93 94 72 340 ≤ 48909865052940 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2334 c22250R_93_26 (by norm_num)

theorem c22250R_93_24 : rowsJ2 93 94 66 340 ≤ 48909865052940 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2333 c22250R_93_25 (by norm_num)

theorem c22250R_93_23 : rowsJ2 93 94 61 340 ≤ 48909865052940 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2332 c22250R_93_24 (by norm_num)

theorem c22250R_93_22 : rowsJ2 93 94 58 340 ≤ 48909865052940 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2331 c22250R_93_23 (by norm_num)

theorem c22250R_93_21 : rowsJ2 93 94 56 340 ≤ 48909865052940 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2330 c22250R_93_22 (by norm_num)

theorem c22250R_93_20 : rowsJ2 93 94 54 340 ≤ 48909865052940 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2329 c22250R_93_21 (by norm_num)

theorem c22250R_93_19 : rowsJ2 93 94 52 340 ≤ 50059384892364 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2328 c22250R_93_20 (by norm_num)

theorem c22250R_93_18 : rowsJ2 93 94 51 340 ≤ 52602081486873 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2327 c22250R_93_19 (by norm_num)

theorem c22250R_93_17 : rowsJ2 93 94 50 340 ≤ 57158891347618 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2326 c22250R_93_18 (by norm_num)

theorem c22250R_93_16 : rowsJ2 93 94 49 340 ≤ 64124253541637 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2325 c22250R_93_17 (by norm_num)

theorem c22250R_93_15 : rowsJ2 93 94 48 340 ≤ 72461500488985 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2324 c22250R_93_16 (by norm_num)

theorem c22250R_93_14 : rowsJ2 93 94 47 340 ≤ 82281195806851 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2323 c22250R_93_15 (by norm_num)

theorem c22250R_93_13 : rowsJ2 93 94 46 340 ≤ 93759561196381 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2322 c22250R_93_14 (by norm_num)

theorem c22250R_93_12 : rowsJ2 93 94 45 340 ≤ 106914799719793 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2321 c22250R_93_13 (by norm_num)

theorem c22250R_93_11 : rowsJ2 93 94 44 340 ≤ 121826415299896 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2320 c22250R_93_12 (by norm_num)

theorem c22250R_93_10 : rowsJ2 93 94 43 340 ≤ 138515299452115 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2319 c22250R_93_11 (by norm_num)

theorem c22250R_93_9 : rowsJ2 93 94 42 340 ≤ 154004348577877 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2318 c22250R_93_10 (by norm_num)

theorem c22250R_93_8 : rowsJ2 93 94 41 340 ≤ 168004659599296 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2317 c22250R_93_9 (by norm_num)

theorem c22250R_93_7 : rowsJ2 93 94 40 340 ≤ 180401952173711 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2316 c22250R_93_8 (by norm_num)

theorem c22250R_93_6 : rowsJ2 93 94 39 340 ≤ 191200816729487 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2315 c22250R_93_7 (by norm_num)

theorem c22250R_93_5 : rowsJ2 93 94 37 340 ≤ 208478578727101 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2314 c22250R_93_6 (by norm_num)

theorem c22250R_93_4 : rowsJ2 93 94 35 340 ≤ 219565925283150 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2313 c22250R_93_5 (by norm_num)

theorem c22250R_93_3 : rowsJ2 93 94 30 340 ≤ 227466188277473 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2312 c22250R_93_4 (by norm_num)

theorem c22250R_93_2 : rowsJ2 93 94 21 340 ≤ 227466188277473 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2311 c22250R_93_3 (by norm_num)

theorem c22250R_93_1 : rowsJ2 93 94 16 340 ≤ 227466188277473 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2310 c22250R_93_2 (by norm_num)

theorem c22250R_93_0 : rowsJ2 93 94 0 340 ≤ 227466188277473 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2309 c22250R_93_1 (by norm_num)

theorem hr22250R_93 : rows2 93 94 ≤ 227466188277473 := rows2_le_of_rowsJ2 93 94 c22250R_93_0

theorem c22250R_94_41 : rowsJ2 94 95 93 340 ≤ 7425391400957 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2392 rows22250R_2393 (by norm_num)

theorem c22250R_94_40 : rowsJ2 94 95 92 340 ≤ 10777385212405 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2391 c22250R_94_41 (by norm_num)

theorem c22250R_94_39 : rowsJ2 94 95 91 340 ≤ 14011587051823 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2390 c22250R_94_40 (by norm_num)

theorem c22250R_94_38 : rowsJ2 94 95 90 340 ≤ 17203981867041 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2389 c22250R_94_39 (by norm_num)

theorem c22250R_94_37 : rowsJ2 94 95 89 340 ≤ 20447486879447 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2388 c22250R_94_38 (by norm_num)

theorem c22250R_94_36 : rowsJ2 94 95 88 340 ≤ 23814341332442 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2387 c22250R_94_37 (by norm_num)

theorem c22250R_94_35 : rowsJ2 94 95 87 340 ≤ 27392433548679 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2386 c22250R_94_36 (by norm_num)

theorem c22250R_94_34 : rowsJ2 94 95 86 340 ≤ 31177979959523 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2385 c22250R_94_35 (by norm_num)

theorem c22250R_94_33 : rowsJ2 94 95 85 340 ≤ 35562815835517 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2384 c22250R_94_34 (by norm_num)

theorem c22250R_94_32 : rowsJ2 94 95 84 340 ≤ 39319440105947 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2383 c22250R_94_33 (by norm_num)

theorem c22250R_94_31 : rowsJ2 94 95 83 340 ≤ 42245199773566 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2382 c22250R_94_32 (by norm_num)

theorem c22250R_94_30 : rowsJ2 94 95 82 340 ≤ 44411265970454 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2381 c22250R_94_31 (by norm_num)

theorem c22250R_94_29 : rowsJ2 94 95 81 340 ≤ 45993572286823 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2380 c22250R_94_30 (by norm_num)

theorem c22250R_94_28 : rowsJ2 94 95 80 340 ≤ 47138389828640 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2379 c22250R_94_29 (by norm_num)

theorem c22250R_94_27 : rowsJ2 94 95 79 340 ≤ 47920575537696 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2378 c22250R_94_28 (by norm_num)

theorem c22250R_94_26 : rowsJ2 94 95 76 340 ≤ 48754535122898 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2377 c22250R_94_27 (by norm_num)

theorem c22250R_94_25 : rowsJ2 94 95 71 340 ≤ 48770735754908 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2376 c22250R_94_26 (by norm_num)

theorem c22250R_94_24 : rowsJ2 94 95 65 340 ≤ 48770735754908 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2375 c22250R_94_25 (by norm_num)

theorem c22250R_94_23 : rowsJ2 94 95 60 340 ≤ 48770735754908 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2374 c22250R_94_24 (by norm_num)

theorem c22250R_94_22 : rowsJ2 94 95 57 340 ≤ 48770735754908 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2373 c22250R_94_23 (by norm_num)

theorem c22250R_94_21 : rowsJ2 94 95 55 340 ≤ 48770735754908 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2372 c22250R_94_22 (by norm_num)

theorem c22250R_94_20 : rowsJ2 94 95 53 340 ≤ 49447682982662 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2371 c22250R_94_21 (by norm_num)

theorem c22250R_94_19 : rowsJ2 94 95 51 340 ≤ 54360880278849 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2370 c22250R_94_20 (by norm_num)

theorem c22250R_94_18 : rowsJ2 94 95 50 340 ≤ 59465270614360 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2369 c22250R_94_19 (by norm_num)

theorem c22250R_94_17 : rowsJ2 94 95 49 340 ≤ 65708829108698 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2368 c22250R_94_18 (by norm_num)

theorem c22250R_94_16 : rowsJ2 94 95 48 340 ≤ 73260590761664 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2367 c22250R_94_17 (by norm_num)

theorem c22250R_94_15 : rowsJ2 94 95 47 340 ≤ 82292839714399 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2366 c22250R_94_16 (by norm_num)

theorem c22250R_94_14 : rowsJ2 94 95 46 340 ≤ 92920854205350 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2365 c22250R_94_15 (by norm_num)

theorem c22250R_94_13 : rowsJ2 94 95 45 340 ≤ 105223212328991 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2364 c22250R_94_14 (by norm_num)

theorem c22250R_94_12 : rowsJ2 94 95 44 340 ≤ 119218789365454 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2363 c22250R_94_13 (by norm_num)

theorem c22250R_94_11 : rowsJ2 94 95 43 340 ≤ 134988029546418 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2362 c22250R_94_12 (by norm_num)

theorem c22250R_94_10 : rowsJ2 94 95 42 340 ≤ 151056142768845 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2361 c22250R_94_11 (by norm_num)

theorem c22250R_94_9 : rowsJ2 94 95 41 340 ≤ 165774239306831 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2360 c22250R_94_10 (by norm_num)

theorem c22250R_94_8 : rowsJ2 94 95 40 340 ≤ 178910071709504 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2359 c22250R_94_9 (by norm_num)

theorem c22250R_94_7 : rowsJ2 94 95 39 340 ≤ 190468416099911 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2358 c22250R_94_8 (by norm_num)

theorem c22250R_94_6 : rowsJ2 94 95 38 340 ≤ 200456659273539 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2357 c22250R_94_7 (by norm_num)

theorem c22250R_94_5 : rowsJ2 94 95 37 340 ≤ 208996963784389 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2356 c22250R_94_6 (by norm_num)

theorem c22250R_94_4 : rowsJ2 94 95 35 340 ≤ 220854454925067 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2355 c22250R_94_5 (by norm_num)

theorem c22250R_94_3 : rowsJ2 94 95 31 340 ≤ 229339984390375 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2354 c22250R_94_4 (by norm_num)

theorem c22250R_94_2 : rowsJ2 94 95 22 340 ≤ 229760409300402 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2353 c22250R_94_3 (by norm_num)

theorem c22250R_94_1 : rowsJ2 94 95 16 340 ≤ 229760409300402 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2352 c22250R_94_2 (by norm_num)

theorem c22250R_94_0 : rowsJ2 94 95 0 340 ≤ 229760409300402 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2351 c22250R_94_1 (by norm_num)

theorem hr22250R_94 : rows2 94 95 ≤ 229760409300402 := rows2_le_of_rowsJ2 94 95 c22250R_94_0

theorem c22250R_95_40 : rowsJ2 95 96 94 340 ≤ 7998584154994 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2434 rows22250R_2435 (by norm_num)

theorem c22250R_95_39 : rowsJ2 95 96 93 340 ≤ 11430117418418 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2433 c22250R_95_40 (by norm_num)

theorem c22250R_95_38 : rowsJ2 95 96 92 340 ≤ 14586868278433 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2432 c22250R_95_39 (by norm_num)

theorem c22250R_95_37 : rowsJ2 95 96 91 340 ≤ 17567061001858 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2431 c22250R_95_38 (by norm_num)

theorem c22250R_95_36 : rowsJ2 95 96 90 340 ≤ 20449026036745 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2430 c22250R_95_37 (by norm_num)

theorem c22250R_95_35 : rowsJ2 95 96 89 340 ≤ 23326386520350 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2429 c22250R_95_36 (by norm_num)

theorem c22250R_95_34 : rowsJ2 95 96 88 340 ≤ 26274796255343 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2428 c22250R_95_35 (by norm_num)

theorem c22250R_95_33 : rowsJ2 95 96 87 340 ≤ 29383994978389 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2427 c22250R_95_34 (by norm_num)

theorem c22250R_95_32 : rowsJ2 95 96 86 340 ≤ 32687707216760 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2426 c22250R_95_33 (by norm_num)

theorem c22250R_95_31 : rowsJ2 95 96 85 340 ≤ 36199326386119 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2425 c22250R_95_32 (by norm_num)

theorem c22250R_95_30 : rowsJ2 95 96 84 340 ≤ 39751379360738 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2424 c22250R_95_31 (by norm_num)

theorem c22250R_95_29 : rowsJ2 95 96 83 340 ≤ 42666139619865 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2423 c22250R_95_30 (by norm_num)

theorem c22250R_95_28 : rowsJ2 95 96 82 340 ≤ 44819705462307 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2422 c22250R_95_29 (by norm_num)

theorem c22250R_95_27 : rowsJ2 95 96 81 340 ≤ 46389778197902 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2421 c22250R_95_28 (by norm_num)

theorem c22250R_95_26 : rowsJ2 95 96 80 340 ≤ 47525240309920 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2420 c22250R_95_27 (by norm_num)

theorem c22250R_95_25 : rowsJ2 95 96 79 340 ≤ 48301918915633 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2419 c22250R_95_26 (by norm_num)

theorem c22250R_95_24 : rowsJ2 95 96 76 340 ≤ 49130006875249 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2418 c22250R_95_25 (by norm_num)

theorem c22250R_95_23 : rowsJ2 95 96 71 340 ≤ 49146093444124 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2417 c22250R_95_24 (by norm_num)

theorem c22250R_95_22 : rowsJ2 95 96 64 340 ≤ 49146093444124 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2416 c22250R_95_23 (by norm_num)

theorem c22250R_95_21 : rowsJ2 95 96 59 340 ≤ 49146093444124 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2415 c22250R_95_22 (by norm_num)

theorem c22250R_95_20 : rowsJ2 95 96 56 340 ≤ 49146093444124 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2414 c22250R_95_21 (by norm_num)

theorem c22250R_95_19 : rowsJ2 95 96 54 340 ≤ 49663460290221 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2413 c22250R_95_20 (by norm_num)

theorem c22250R_95_18 : rowsJ2 95 96 52 340 ≤ 53140603036919 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2412 c22250R_95_19 (by norm_num)

theorem c22250R_95_17 : rowsJ2 95 96 50 340 ≤ 61265245419161 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2411 c22250R_95_18 (by norm_num)

theorem c22250R_95_16 : rowsJ2 95 96 49 340 ≤ 66852936527799 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2410 c22250R_95_17 (by norm_num)

theorem c22250R_95_15 : rowsJ2 95 96 48 340 ≤ 73684014528885 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2409 c22250R_95_16 (by norm_num)

theorem c22250R_95_14 : rowsJ2 95 96 47 340 ≤ 81932161159005 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2408 c22250R_95_15 (by norm_num)

theorem c22250R_95_13 : rowsJ2 95 96 46 340 ≤ 91774594101640 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2407 c22250R_95_14 (by norm_num)

theorem c22250R_95_12 : rowsJ2 95 96 45 340 ≤ 103228268738316 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2406 c22250R_95_13 (by norm_num)

theorem c22250R_95_11 : rowsJ2 95 96 44 340 ≤ 116372653891446 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2405 c22250R_95_12 (by norm_num)

theorem c22250R_95_10 : rowsJ2 95 96 43 340 ≤ 131227325572563 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2404 c22250R_95_11 (by norm_num)

theorem c22250R_95_9 : rowsJ2 95 96 42 340 ≤ 147873710015594 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2403 c22250R_95_10 (by norm_num)

theorem c22250R_95_8 : rowsJ2 95 96 41 340 ≤ 163250306182006 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2402 c22250R_95_9 (by norm_num)

theorem c22250R_95_7 : rowsJ2 95 96 40 340 ≤ 177124618940962 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2401 c22250R_95_8 (by norm_num)

theorem c22250R_95_6 : rowsJ2 95 96 39 340 ≤ 189442209020406 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2400 c22250R_95_7 (by norm_num)

theorem c22250R_95_5 : rowsJ2 95 96 38 340 ≤ 200210638387338 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2399 c22250R_95_6 (by norm_num)

theorem c22250R_95_4 : rowsJ2 95 96 36 340 ≤ 216610577032186 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2398 c22250R_95_5 (by norm_num)

theorem c22250R_95_3 : rowsJ2 95 96 33 340 ≤ 228927556047075 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2397 c22250R_95_4 (by norm_num)

theorem c22250R_95_2 : rowsJ2 95 96 25 340 ≤ 232187963470651 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2396 c22250R_95_3 (by norm_num)

theorem c22250R_95_1 : rowsJ2 95 96 17 340 ≤ 232187963470651 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2395 c22250R_95_2 (by norm_num)

theorem c22250R_95_0 : rowsJ2 95 96 0 340 ≤ 232187963470651 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2394 c22250R_95_1 (by norm_num)

theorem hr22250R_95 : rows2 95 96 ≤ 232187963470651 := rows2_le_of_rowsJ2 95 96 c22250R_95_0

theorem c22250R_96_40 : rowsJ2 96 97 95 340 ≤ 8948483851066 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2476 rows22250R_2477 (by norm_num)

theorem c22250R_96_39 : rowsJ2 96 97 94 340 ≤ 12672614977944 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2475 c22250R_96_40 (by norm_num)

theorem c22250R_96_38 : rowsJ2 96 97 93 340 ≤ 16017036133240 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2474 c22250R_96_39 (by norm_num)

theorem c22250R_96_37 : rowsJ2 96 97 92 340 ≤ 19022039999342 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2473 c22250R_96_38 (by norm_num)

theorem c22250R_96_36 : rowsJ2 96 97 91 340 ≤ 21789665408942 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2472 c22250R_96_37 (by norm_num)

theorem c22250R_96_35 : rowsJ2 96 97 90 340 ≤ 24400714479130 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2471 c22250R_96_36 (by norm_num)

theorem c22250R_96_34 : rowsJ2 96 97 89 340 ≤ 26951020491832 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2470 c22250R_96_35 (by norm_num)

theorem c22250R_96_33 : rowsJ2 96 97 88 340 ≤ 29517053098089 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2469 c22250R_96_34 (by norm_num)

theorem c22250R_96_32 : rowsJ2 96 97 87 340 ≤ 32191834253867 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2468 c22250R_96_33 (by norm_num)

theorem c22250R_96_31 : rowsJ2 96 97 86 340 ≤ 35048208825419 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2467 c22250R_96_32 (by norm_num)

theorem c22250R_96_30 : rowsJ2 96 97 85 340 ≤ 38099523257516 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2466 c22250R_96_31 (by norm_num)

theorem c22250R_96_29 : rowsJ2 96 97 84 340 ≤ 41342306199984 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2465 c22250R_96_30 (by norm_num)

theorem c22250R_96_28 : rowsJ2 96 97 83 340 ≤ 44148164888624 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2464 c22250R_96_29 (by norm_num)

theorem c22250R_96_27 : rowsJ2 96 97 82 340 ≤ 46289670916234 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2463 c22250R_96_28 (by norm_num)

theorem c22250R_96_26 : rowsJ2 96 97 81 340 ≤ 47847735941840 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2462 c22250R_96_27 (by norm_num)

theorem c22250R_96_25 : rowsJ2 96 97 80 340 ≤ 48974013801776 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2461 c22250R_96_26 (by norm_num)

theorem c22250R_96_24 : rowsJ2 96 97 78 340 ≤ 50218767656637 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2460 c22250R_96_25 (by norm_num)

theorem c22250R_96_23 : rowsJ2 96 97 75 340 ≤ 50583534846126 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2459 c22250R_96_24 (by norm_num)

theorem c22250R_96_22 : rowsJ2 96 97 70 340 ≤ 50583534846126 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2458 c22250R_96_23 (by norm_num)

theorem c22250R_96_21 : rowsJ2 96 97 63 340 ≤ 50583534846126 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2457 c22250R_96_22 (by norm_num)

theorem c22250R_96_20 : rowsJ2 96 97 58 340 ≤ 50583534846126 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2456 c22250R_96_21 (by norm_num)

theorem c22250R_96_19 : rowsJ2 96 97 55 340 ≤ 50760644809834 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2455 c22250R_96_20 (by norm_num)

theorem c22250R_96_18 : rowsJ2 96 97 53 340 ≤ 52755544071042 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2454 c22250R_96_19 (by norm_num)

theorem c22250R_96_17 : rowsJ2 96 97 51 340 ≤ 58134821124418 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2453 c22250R_96_18 (by norm_num)

theorem c22250R_96_16 : rowsJ2 96 97 49 340 ≤ 66944847238490 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2452 c22250R_96_17 (by norm_num)

theorem c22250R_96_15 : rowsJ2 96 97 48 340 ≤ 73028340872440 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2451 c22250R_96_16 (by norm_num)

theorem c22250R_96_14 : rowsJ2 96 97 47 340 ≤ 80463377815052 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2450 c22250R_96_15 (by norm_num)

theorem c22250R_96_13 : rowsJ2 96 97 46 340 ≤ 89428555199964 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2449 c22250R_96_14 (by norm_num)

theorem c22250R_96_12 : rowsJ2 96 97 45 340 ≤ 100002492259917 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2448 c22250R_96_13 (by norm_num)

theorem c22250R_96_11 : rowsJ2 96 97 44 340 ≤ 112202773660615 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2447 c22250R_96_12 (by norm_num)

theorem c22250R_96_10 : rowsJ2 96 97 43 340 ≤ 126109774859948 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2446 c22250R_96_11 (by norm_num)

theorem c22250R_96_9 : rowsJ2 96 97 42 340 ≤ 141743778505935 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2445 c22250R_96_10 (by norm_num)

theorem c22250R_96_8 : rowsJ2 96 97 41 340 ≤ 157678179300736 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2444 c22250R_96_9 (by norm_num)

theorem c22250R_96_7 : rowsJ2 96 97 40 340 ≤ 172189486814651 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2443 c22250R_96_8 (by norm_num)

theorem c22250R_96_6 : rowsJ2 96 97 39 340 ≤ 185163487024428 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2442 c22250R_96_7 (by norm_num)

theorem c22250R_96_5 : rowsJ2 96 97 38 340 ≤ 196607889696867 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2441 c22250R_96_6 (by norm_num)

theorem c22250R_96_4 : rowsJ2 96 97 36 340 ≤ 214296914424596 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2440 c22250R_96_5 (by norm_num)

theorem c22250R_96_3 : rowsJ2 96 97 33 340 ≤ 227814688137599 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2439 c22250R_96_4 (by norm_num)

theorem c22250R_96_2 : rowsJ2 96 97 26 340 ≤ 231481160932583 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2438 c22250R_96_3 (by norm_num)

theorem c22250R_96_1 : rowsJ2 96 97 17 340 ≤ 231481160932583 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2437 c22250R_96_2 (by norm_num)

theorem c22250R_96_0 : rowsJ2 96 97 0 340 ≤ 231481160932583 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2436 c22250R_96_1 (by norm_num)

theorem hr22250R_96 : rows2 96 97 ≤ 231481160932583 := rows2_le_of_rowsJ2 96 97 c22250R_96_0

theorem c22250R_97_40 : rowsJ2 97 98 96 340 ≤ 10370613284798 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2518 rows22250R_2519 (by norm_num)

theorem c22250R_97_39 : rowsJ2 97 98 95 340 ≤ 14621473975997 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2517 c22250R_97_40 (by norm_num)

theorem c22250R_97_38 : rowsJ2 97 98 94 340 ≤ 18363093714113 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2516 c22250R_97_39 (by norm_num)

theorem c22250R_97_37 : rowsJ2 97 98 93 340 ≤ 21657487034119 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2515 c22250R_97_38 (by norm_num)

theorem c22250R_97_36 : rowsJ2 97 98 92 340 ≤ 24592649383033 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2514 c22250R_97_37 (by norm_num)

theorem c22250R_97_35 : rowsJ2 97 98 91 340 ≤ 27226380679976 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2513 c22250R_97_36 (by norm_num)

theorem c22250R_97_34 : rowsJ2 97 98 90 340 ≤ 29643409836459 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2512 c22250R_97_35 (by norm_num)

theorem c22250R_97_33 : rowsJ2 97 98 89 340 ≤ 31941911443767 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2511 c22250R_97_34 (by norm_num)

theorem c22250R_97_32 : rowsJ2 97 98 88 340 ≤ 34200677366028 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2510 c22250R_97_33 (by norm_num)

theorem c22250R_97_31 : rowsJ2 97 98 87 340 ≤ 36513417307023 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2509 c22250R_97_32 (by norm_num)

theorem c22250R_97_30 : rowsJ2 97 98 86 340 ≤ 38956370981914 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2508 c22250R_97_31 (by norm_num)

theorem c22250R_97_29 : rowsJ2 97 98 85 340 ≤ 41581317507330 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2507 c22250R_97_30 (by norm_num)

theorem c22250R_97_28 : rowsJ2 97 98 84 340 ≤ 44384856898306 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2506 c22250R_97_29 (by norm_num)

theorem c22250R_97_27 : rowsJ2 97 98 83 340 ≤ 46980846495588 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2505 c22250R_97_28 (by norm_num)

theorem c22250R_97_26 : rowsJ2 97 98 82 340 ≤ 49109420566146 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2504 c22250R_97_27 (by norm_num)

theorem c22250R_97_25 : rowsJ2 97 98 81 340 ≤ 50655687298036 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2503 c22250R_97_26 (by norm_num)

theorem c22250R_97_24 : rowsJ2 97 98 80 340 ≤ 51774297369765 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2502 c22250R_97_25 (by norm_num)

theorem c22250R_97_23 : rowsJ2 97 98 78 340 ≤ 53009060906406 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2501 c22250R_97_24 (by norm_num)

theorem c22250R_97_22 : rowsJ2 97 98 75 340 ≤ 53371295555777 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2500 c22250R_97_23 (by norm_num)

theorem c22250R_97_21 : rowsJ2 97 98 69 340 ≤ 53371295555777 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2499 c22250R_97_22 (by norm_num)

theorem c22250R_97_20 : rowsJ2 97 98 62 340 ≤ 53371295555777 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2498 c22250R_97_21 (by norm_num)

theorem c22250R_97_19 : rowsJ2 97 98 57 340 ≤ 53371295555777 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2497 c22250R_97_20 (by norm_num)

theorem c22250R_97_18 : rowsJ2 97 98 54 340 ≤ 54429425215704 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2496 c22250R_97_19 (by norm_num)

theorem c22250R_97_17 : rowsJ2 97 98 52 340 ≤ 57656045342609 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2495 c22250R_97_18 (by norm_num)

theorem c22250R_97_16 : rowsJ2 97 98 50 340 ≤ 63616347821786 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2494 c22250R_97_17 (by norm_num)

theorem c22250R_97_15 : rowsJ2 97 98 48 340 ≤ 73315706781027 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2493 c22250R_97_16 (by norm_num)

theorem c22250R_97_14 : rowsJ2 97 98 47 340 ≤ 80004204928663 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2492 c22250R_97_15 (by norm_num)

theorem c22250R_97_13 : rowsJ2 97 98 46 340 ≤ 88157601059706 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2491 c22250R_97_14 (by norm_num)

theorem c22250R_97_12 : rowsJ2 97 98 45 340 ≤ 97855391170579 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2490 c22250R_97_13 (by norm_num)

theorem c22250R_97_11 : rowsJ2 97 98 44 340 ≤ 109177052852627 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2489 c22250R_97_12 (by norm_num)

theorem c22250R_97_10 : rowsJ2 97 98 43 340 ≤ 122140826463785 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2488 c22250R_97_11 (by norm_num)

theorem c22250R_97_9 : rowsJ2 97 98 42 340 ≤ 136828033775413 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2487 c22250R_97_10 (by norm_num)

theorem c22250R_97_8 : rowsJ2 97 98 41 340 ≤ 153363804776387 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2486 c22250R_97_9 (by norm_num)

theorem c22250R_97_7 : rowsJ2 97 98 40 340 ≤ 168512588617374 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2485 c22250R_97_8 (by norm_num)

theorem c22250R_97_6 : rowsJ2 97 98 39 340 ≤ 182143319341811 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2484 c22250R_97_7 (by norm_num)

theorem c22250R_97_5 : rowsJ2 97 98 38 340 ≤ 194263855013842 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2483 c22250R_97_6 (by norm_num)

theorem c22250R_97_4 : rowsJ2 97 98 36 340 ≤ 213246453331218 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2482 c22250R_97_5 (by norm_num)

theorem c22250R_97_3 : rowsJ2 97 98 33 340 ≤ 228071639821648 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2481 c22250R_97_4 (by norm_num)

theorem c22250R_97_2 : rowsJ2 97 98 27 340 ≤ 232248536315474 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2480 c22250R_97_3 (by norm_num)

theorem c22250R_97_1 : rowsJ2 97 98 17 340 ≤ 232248536315474 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2479 c22250R_97_2 (by norm_num)

theorem c22250R_97_0 : rowsJ2 97 98 0 340 ≤ 232248536315474 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2478 c22250R_97_1 (by norm_num)

theorem hr22250R_97 : rows2 97 98 ≤ 232248536315474 := rows2_le_of_rowsJ2 97 98 c22250R_97_0

theorem c22250R_98_41 : rowsJ2 98 99 97 340 ≤ 12217459286015 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2561 rows22250R_2562 (by norm_num)

theorem c22250R_98_40 : rowsJ2 98 99 96 340 ≤ 17187615334815 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2560 c22250R_98_41 (by norm_num)

theorem c22250R_98_39 : rowsJ2 98 99 95 340 ≤ 21529890743639 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2559 c22250R_98_40 (by norm_num)

theorem c22250R_98_38 : rowsJ2 98 99 94 340 ≤ 25291902891584 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2558 c22250R_98_39 (by norm_num)

theorem c22250R_98_37 : rowsJ2 98 99 93 340 ≤ 28583112834688 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2557 c22250R_98_38 (by norm_num)

theorem c22250R_98_36 : rowsJ2 98 99 92 340 ≤ 31448048080418 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2556 c22250R_98_37 (by norm_num)

theorem c22250R_98_35 : rowsJ2 98 99 91 340 ≤ 33992086412789 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2555 c22250R_98_36 (by norm_num)

theorem c22250R_98_34 : rowsJ2 98 99 90 340 ≤ 36255811937267 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2554 c22250R_98_35 (by norm_num)

theorem c22250R_98_33 : rowsJ2 98 99 89 340 ≤ 38341193237958 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2553 c22250R_98_34 (by norm_num)

theorem c22250R_98_32 : rowsJ2 98 99 88 340 ≤ 40329469328535 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2552 c22250R_98_33 (by norm_num)

theorem c22250R_98_31 : rowsJ2 98 99 87 340 ≤ 42316541648040 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2551 c22250R_98_32 (by norm_num)

theorem c22250R_98_30 : rowsJ2 98 99 86 340 ≤ 44379442706859 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2550 c22250R_98_31 (by norm_num)

theorem c22250R_98_29 : rowsJ2 98 99 85 340 ≤ 46611402418606 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2549 c22250R_98_30 (by norm_num)

theorem c22250R_98_28 : rowsJ2 98 99 84 340 ≤ 49009097282474 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2548 c22250R_98_29 (by norm_num)

theorem c22250R_98_27 : rowsJ2 98 99 83 340 ≤ 51585769617923 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2547 c22250R_98_28 (by norm_num)

theorem c22250R_98_26 : rowsJ2 98 99 82 340 ≤ 53602904068623 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2546 c22250R_98_27 (by norm_num)

theorem c22250R_98_25 : rowsJ2 98 99 81 340 ≤ 55137578265434 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2545 c22250R_98_26 (by norm_num)

theorem c22250R_98_24 : rowsJ2 98 99 80 340 ≤ 56247290976668 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2544 c22250R_98_25 (by norm_num)

theorem c22250R_98_23 : rowsJ2 98 99 78 340 ≤ 57473591443993 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2543 c22250R_98_24 (by norm_num)

theorem c22250R_98_22 : rowsJ2 98 99 75 340 ≤ 57833328477088 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2542 c22250R_98_23 (by norm_num)

theorem c22250R_98_21 : rowsJ2 98 99 69 340 ≤ 57833328477088 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2541 c22250R_98_22 (by norm_num)

theorem c22250R_98_20 : rowsJ2 98 99 61 340 ≤ 57833328477088 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2540 c22250R_98_21 (by norm_num)

theorem c22250R_98_19 : rowsJ2 98 99 56 340 ≤ 57833328477088 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2539 c22250R_98_20 (by norm_num)

theorem c22250R_98_18 : rowsJ2 98 99 53 340 ≤ 59524634886098 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2538 c22250R_98_19 (by norm_num)

theorem c22250R_98_17 : rowsJ2 98 99 51 340 ≤ 63138557908377 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2537 c22250R_98_18 (by norm_num)

theorem c22250R_98_16 : rowsJ2 98 99 49 340 ≤ 69597790894465 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2536 c22250R_98_17 (by norm_num)

theorem c22250R_98_15 : rowsJ2 98 99 47 340 ≤ 80208758378027 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2535 c22250R_98_16 (by norm_num)

theorem c22250R_98_14 : rowsJ2 98 99 46 340 ≤ 87519536960268 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2534 c22250R_98_15 (by norm_num)

theorem c22250R_98_13 : rowsJ2 98 99 45 340 ≤ 96308183168724 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2533 c22250R_98_14 (by norm_num)

theorem c22250R_98_12 : rowsJ2 98 99 44 340 ≤ 106655018982924 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2532 c22250R_98_13 (by norm_num)

theorem c22250R_98_11 : rowsJ2 98 99 43 340 ≤ 118640393688465 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2531 c22250R_98_12 (by norm_num)

theorem c22250R_98_10 : rowsJ2 98 99 42 340 ≤ 132283206339391 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2530 c22250R_98_11 (by norm_num)

theorem c22250R_98_9 : rowsJ2 98 99 41 340 ≤ 147770321385537 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2529 c22250R_98_10 (by norm_num)

theorem c22250R_98_8 : rowsJ2 98 99 40 340 ≤ 163497699830638 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2528 c22250R_98_9 (by norm_num)

theorem c22250R_98_7 : rowsJ2 98 99 39 340 ≤ 177680020151952 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2527 c22250R_98_8 (by norm_num)

theorem c22250R_98_6 : rowsJ2 98 99 38 340 ≤ 190370150365213 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2526 c22250R_98_7 (by norm_num)

theorem c22250R_98_5 : rowsJ2 98 99 37 340 ≤ 201578892649483 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2525 c22250R_98_6 (by norm_num)

theorem c22250R_98_4 : rowsJ2 98 99 35 340 ≤ 217601642529001 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2524 c22250R_98_5 (by norm_num)

theorem c22250R_98_3 : rowsJ2 98 99 33 340 ≤ 226786703048140 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2523 c22250R_98_4 (by norm_num)

theorem c22250R_98_2 : rowsJ2 98 99 28 340 ≤ 231692362298053 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2522 c22250R_98_3 (by norm_num)

theorem c22250R_98_1 : rowsJ2 98 99 17 340 ≤ 231692362298053 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2521 c22250R_98_2 (by norm_num)

theorem c22250R_98_0 : rowsJ2 98 99 0 340 ≤ 231692362298053 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2520 c22250R_98_1 (by norm_num)

theorem hr22250R_98 : rows2 98 99 ≤ 231692362298053 := rows2_le_of_rowsJ2 98 99 c22250R_98_0

theorem c22250R_99_41 : rowsJ2 99 100 98 340 ≤ 14586786577397 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2604 rows22250R_2605 (by norm_num)

theorem c22250R_99_40 : rowsJ2 99 100 97 340 ≤ 20534451553156 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2603 c22250R_99_41 (by norm_num)

theorem c22250R_99_39 : rowsJ2 99 100 96 340 ≤ 25710715334755 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2602 c22250R_99_40 (by norm_num)

theorem c22250R_99_38 : rowsJ2 99 100 95 340 ≤ 30184351169300 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2601 c22250R_99_39 (by norm_num)

theorem c22250R_99_37 : rowsJ2 99 100 94 340 ≤ 34051796765672 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2600 c22250R_99_38 (by norm_num)

theorem c22250R_99_36 : rowsJ2 99 100 93 340 ≤ 37378061696781 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2599 c22250R_99_37 (by norm_num)

theorem c22250R_99_35 : rowsJ2 99 100 92 340 ≤ 40255237939316 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2598 c22250R_99_36 (by norm_num)

theorem c22250R_99_34 : rowsJ2 99 100 91 340 ≤ 42745092486836 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2597 c22250R_99_35 (by norm_num)

theorem c22250R_99_33 : rowsJ2 99 100 90 340 ≤ 44935910409783 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2596 c22250R_99_34 (by norm_num)

theorem c22250R_99_32 : rowsJ2 99 100 89 340 ≤ 46885370862497 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2595 c22250R_99_33 (by norm_num)

theorem c22250R_99_31 : rowsJ2 99 100 88 340 ≤ 48678615006406 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2594 c22250R_99_32 (by norm_num)

theorem c22250R_99_30 : rowsJ2 99 100 87 340 ≤ 50413866126062 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2593 c22250R_99_31 (by norm_num)

theorem c22250R_99_29 : rowsJ2 99 100 86 340 ≤ 52170456301999 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2592 c22250R_99_30 (by norm_num)

theorem c22250R_99_28 : rowsJ2 99 100 85 340 ≤ 54042284802332 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2591 c22250R_99_29 (by norm_num)

theorem c22250R_99_27 : rowsJ2 99 100 84 340 ≤ 56067001482730 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2590 c22250R_99_28 (by norm_num)

theorem c22250R_99_26 : rowsJ2 99 100 83 340 ≤ 58257811583845 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2589 c22250R_99_27 (by norm_num)

theorem c22250R_99_25 : rowsJ2 99 100 82 340 ≤ 60260671332600 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2588 c22250R_99_26 (by norm_num)

theorem c22250R_99_24 : rowsJ2 99 100 81 340 ≤ 61782629792739 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2587 c22250R_99_25 (by norm_num)

theorem c22250R_99_23 : rowsJ2 99 100 80 340 ≤ 62883608438087 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2586 c22250R_99_24 (by norm_num)

theorem c22250R_99_22 : rowsJ2 99 100 78 340 ≤ 64101562152126 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2585 c22250R_99_23 (by norm_num)

theorem c22250R_99_21 : rowsJ2 99 100 74 340 ≤ 64458835775335 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2584 c22250R_99_22 (by norm_num)

theorem c22250R_99_20 : rowsJ2 99 100 68 340 ≤ 64458835775335 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2583 c22250R_99_21 (by norm_num)

theorem c22250R_99_19 : rowsJ2 99 100 60 340 ≤ 64458835775335 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2582 c22250R_99_20 (by norm_num)

theorem c22250R_99_18 : rowsJ2 99 100 55 340 ≤ 64549823439003 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2581 c22250R_99_19 (by norm_num)

theorem c22250R_99_17 : rowsJ2 99 100 52 340 ≤ 66807272875100 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2580 c22250R_99_18 (by norm_num)

theorem c22250R_99_16 : rowsJ2 99 100 50 340 ≤ 70816751261076 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2579 c22250R_99_17 (by norm_num)

theorem c22250R_99_15 : rowsJ2 99 100 48 340 ≤ 77977205935617 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2578 c22250R_99_16 (by norm_num)

theorem c22250R_99_14 : rowsJ2 99 100 46 340 ≤ 89721735064776 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2577 c22250R_99_15 (by norm_num)

theorem c22250R_99_13 : rowsJ2 99 100 45 340 ≤ 97668476272522 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2576 c22250R_99_14 (by norm_num)

theorem c22250R_99_12 : rowsJ2 99 100 44 340 ≤ 107106624429946 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2575 c22250R_99_13 (by norm_num)

theorem c22250R_99_11 : rowsJ2 99 100 43 340 ≤ 118117363104069 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2574 c22250R_99_12 (by norm_num)

theorem c22250R_99_10 : rowsJ2 99 100 42 340 ≤ 130781950851029 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2573 c22250R_99_11 (by norm_num)

theorem c22250R_99_9 : rowsJ2 99 100 41 340 ≤ 145225044960871 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2572 c22250R_99_10 (by norm_num)

theorem c22250R_99_8 : rowsJ2 99 100 40 340 ≤ 161639440261294 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2571 c22250R_99_9 (by norm_num)

theorem c22250R_99_7 : rowsJ2 99 100 39 340 ≤ 176481631495300 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2570 c22250R_99_8 (by norm_num)

theorem c22250R_99_6 : rowsJ2 99 100 38 340 ≤ 189741974531474 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2569 c22250R_99_7 (by norm_num)

theorem c22250R_99_5 : rowsJ2 99 100 37 340 ≤ 201538893671700 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2568 c22250R_99_6 (by norm_num)

theorem c22250R_99_4 : rowsJ2 99 100 36 340 ≤ 211213450367177 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2567 c22250R_99_5 (by norm_num)

theorem c22250R_99_3 : rowsJ2 99 100 34 340 ≤ 224471385149883 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2566 c22250R_99_4 (by norm_num)

theorem c22250R_99_2 : rowsJ2 99 100 30 340 ≤ 234083875365987 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2565 c22250R_99_3 (by norm_num)

theorem c22250R_99_1 : rowsJ2 99 100 18 340 ≤ 234511822229042 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2564 c22250R_99_2 (by norm_num)

theorem c22250R_99_0 : rowsJ2 99 100 0 340 ≤ 234511822229042 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2563 c22250R_99_1 (by norm_num)

theorem hr22250R_99 : rows2 99 100 ≤ 234511822229042 := rows2_le_of_rowsJ2 99 100 c22250R_99_0

theorem c22250R_100_41 : rowsJ2 100 101 99 340 ≤ 17436889599030 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2647 rows22250R_2648 (by norm_num)

theorem c22250R_100_40 : rowsJ2 100 101 98 340 ≤ 24580038476088 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2646 c22250R_100_41 (by norm_num)

theorem c22250R_100_39 : rowsJ2 100 101 97 340 ≤ 30817529872089 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2645 c22250R_100_40 (by norm_num)

theorem c22250R_100_38 : rowsJ2 100 101 96 340 ≤ 36204618790404 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2644 c22250R_100_39 (by norm_num)

theorem c22250R_100_37 : rowsJ2 100 101 95 340 ≤ 40860102662710 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2643 c22250R_100_38 (by norm_num)

theorem c22250R_100_36 : rowsJ2 100 101 94 340 ≤ 44835190547506 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2642 c22250R_100_37 (by norm_num)

theorem c22250R_100_35 : rowsJ2 100 101 93 340 ≤ 48243585693915 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2641 c22250R_100_36 (by norm_num)

theorem c22250R_100_34 : rowsJ2 100 101 92 340 ≤ 51133017822804 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2640 c22250R_100_35 (by norm_num)

theorem c22250R_100_33 : rowsJ2 100 101 91 340 ≤ 53612699435112 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2639 c22250R_100_34 (by norm_num)

theorem c22250R_100_32 : rowsJ2 100 101 90 340 ≤ 55727389940278 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2638 c22250R_100_33 (by norm_num)

theorem c22250R_100_31 : rowsJ2 100 101 89 340 ≤ 57582358444353 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2637 c22250R_100_32 (by norm_num)

theorem c22250R_100_30 : rowsJ2 100 101 88 340 ≤ 59218536961914 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2636 c22250R_100_31 (by norm_num)

theorem c22250R_100_29 : rowsJ2 100 101 87 340 ≤ 60737923110617 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2635 c22250R_100_30 (by norm_num)

theorem c22250R_100_28 : rowsJ2 100 101 86 340 ≤ 62222272255236 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2634 c22250R_100_29 (by norm_num)

theorem c22250R_100_27 : rowsJ2 100 101 85 340 ≤ 63767657360557 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2633 c22250R_100_28 (by norm_num)

theorem c22250R_100_26 : rowsJ2 100 101 84 340 ≤ 65451758818126 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2632 c22250R_100_27 (by norm_num)

theorem c22250R_100_25 : rowsJ2 100 101 83 340 ≤ 67289079925427 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2631 c22250R_100_26 (by norm_num)

theorem c22250R_100_24 : rowsJ2 100 101 82 340 ≤ 69276591954975 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2630 c22250R_100_25 (by norm_num)

theorem c22250R_100_23 : rowsJ2 100 101 81 340 ≤ 70787431655245 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2629 c22250R_100_24 (by norm_num)

theorem c22250R_100_22 : rowsJ2 100 101 80 340 ≤ 71879836858290 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2628 c22250R_100_23 (by norm_num)

theorem c22250R_100_21 : rowsJ2 100 101 78 340 ≤ 73088218400275 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2627 c22250R_100_22 (by norm_num)

theorem c22250R_100_20 : rowsJ2 100 101 74 340 ≤ 73443062122053 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2626 c22250R_100_21 (by norm_num)

theorem c22250R_100_19 : rowsJ2 100 101 68 340 ≤ 73443062122053 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2625 c22250R_100_20 (by norm_num)

theorem c22250R_100_18 : rowsJ2 100 101 59 340 ≤ 73443062122053 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2624 c22250R_100_19 (by norm_num)

theorem c22250R_100_17 : rowsJ2 100 101 54 340 ≤ 73628176426479 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2623 c22250R_100_18 (by norm_num)

theorem c22250R_100_16 : rowsJ2 100 101 51 340 ≤ 76180254331425 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2622 c22250R_100_17 (by norm_num)

theorem c22250R_100_15 : rowsJ2 100 101 49 340 ≤ 80495191198949 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2621 c22250R_100_16 (by norm_num)

theorem c22250R_100_14 : rowsJ2 100 101 47 340 ≤ 88372099749951 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2620 c22250R_100_15 (by norm_num)

theorem c22250R_100_13 : rowsJ2 100 101 45 340 ≤ 101176085915905 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2619 c22250R_100_14 (by norm_num)

theorem c22250R_100_12 : rowsJ2 100 101 44 340 ≤ 109670410778138 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2618 c22250R_100_13 (by norm_num)

theorem c22250R_100_11 : rowsJ2 100 101 43 340 ≤ 119669134195334 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2617 c22250R_100_12 (by norm_num)

theorem c22250R_100_10 : rowsJ2 100 101 42 340 ≤ 131254312930190 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2616 c22250R_100_11 (by norm_num)

theorem c22250R_100_9 : rowsJ2 100 101 41 340 ≤ 144613711985181 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2615 c22250R_100_10 (by norm_num)

theorem c22250R_100_8 : rowsJ2 100 101 40 340 ≤ 159877617883113 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2614 c22250R_100_9 (by norm_num)

theorem c22250R_100_7 : rowsJ2 100 101 39 340 ≤ 175381850692301 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2613 c22250R_100_8 (by norm_num)

theorem c22250R_100_6 : rowsJ2 100 101 38 340 ≤ 189212579695434 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2612 c22250R_100_7 (by norm_num)

theorem c22250R_100_5 : rowsJ2 100 101 37 340 ≤ 201487088599004 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2611 c22250R_100_6 (by norm_num)

theorem c22250R_100_4 : rowsJ2 100 101 36 340 ≤ 211764209841095 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2610 c22250R_100_5 (by norm_num)

theorem c22250R_100_3 : rowsJ2 100 101 34 340 ≤ 226150526664387 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2609 c22250R_100_4 (by norm_num)

theorem c22250R_100_2 : rowsJ2 100 101 30 340 ≤ 237123876027681 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2608 c22250R_100_3 (by norm_num)

theorem c22250R_100_1 : rowsJ2 100 101 18 340 ≤ 237548912324078 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2607 c22250R_100_2 (by norm_num)

theorem c22250R_100_0 : rowsJ2 100 101 0 340 ≤ 237548912324078 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2606 c22250R_100_1 (by norm_num)

theorem hr22250R_100 : rows2 100 101 ≤ 237548912324078 := rows2_le_of_rowsJ2 100 101 c22250R_100_0

theorem c22250R_101_42 : rowsJ2 101 102 100 340 ≤ 20873058941027 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2691 rows22250R_2692 (by norm_num)

theorem c22250R_101_41 : rowsJ2 101 102 99 340 ≤ 29498731278850 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2690 c22250R_101_42 (by norm_num)

theorem c22250R_101_40 : rowsJ2 101 102 98 340 ≤ 37057810965758 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2689 c22250R_101_41 (by norm_num)

theorem c22250R_101_39 : rowsJ2 101 102 97 340 ≤ 43627668993867 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2688 c22250R_101_40 (by norm_num)

theorem c22250R_101_38 : rowsJ2 101 102 96 340 ≤ 49315111869418 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2687 c22250R_101_39 (by norm_num)

theorem c22250R_101_37 : rowsJ2 101 102 95 340 ≤ 54192668799990 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2686 c22250R_101_38 (by norm_num)

theorem c22250R_101_36 : rowsJ2 101 102 94 340 ≤ 58361685445741 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2685 c22250R_101_37 (by norm_num)

theorem c22250R_101_35 : rowsJ2 101 102 93 340 ≤ 61890491377553 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2684 c22250R_101_36 (by norm_num)

theorem c22250R_101_34 : rowsJ2 101 102 92 340 ≤ 64875627585851 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2683 c22250R_101_35 (by norm_num)

theorem c22250R_101_33 : rowsJ2 101 102 91 340 ≤ 67381798434588 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2682 c22250R_101_34 (by norm_num)

theorem c22250R_101_32 : rowsJ2 101 102 90 340 ≤ 69501331377582 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2681 c22250R_101_33 (by norm_num)

theorem c22250R_101_31 : rowsJ2 101 102 89 340 ≤ 71295822898642 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2680 c22250R_101_32 (by norm_num)

theorem c22250R_101_30 : rowsJ2 101 102 88 340 ≤ 72853922988172 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2679 c22250R_101_31 (by norm_num)

theorem c22250R_101_29 : rowsJ2 101 102 87 340 ≤ 74233271048155 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2678 c22250R_101_30 (by norm_num)

theorem c22250R_101_28 : rowsJ2 101 102 86 340 ≤ 75519501160059 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2677 c22250R_101_29 (by norm_num)

theorem c22250R_101_27 : rowsJ2 101 102 85 340 ≤ 76810989079205 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2676 c22250R_101_28 (by norm_num)

theorem c22250R_101_26 : rowsJ2 101 102 84 340 ≤ 78187692793381 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2675 c22250R_101_27 (by norm_num)

theorem c22250R_101_25 : rowsJ2 101 102 83 340 ≤ 79703415994563 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2674 c22250R_101_26 (by norm_num)

theorem c22250R_101_24 : rowsJ2 101 102 82 340 ≤ 81356539910273 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2673 c22250R_101_25 (by norm_num)

theorem c22250R_101_23 : rowsJ2 101 102 81 340 ≤ 82856456111739 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2672 c22250R_101_24 (by norm_num)

theorem c22250R_101_22 : rowsJ2 101 102 80 340 ≤ 83940458863683 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2671 c22250R_101_23 (by norm_num)

theorem c22250R_101_21 : rowsJ2 101 102 79 340 ≤ 84681926159931 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2670 c22250R_101_22 (by norm_num)

theorem c22250R_101_20 : rowsJ2 101 102 77 340 ≤ 85384323022330 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2669 c22250R_101_21 (by norm_num)

theorem c22250R_101_19 : rowsJ2 101 102 73 340 ≤ 85491884828604 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2668 c22250R_101_20 (by norm_num)

theorem c22250R_101_18 : rowsJ2 101 102 67 340 ≤ 85491884828604 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2667 c22250R_101_19 (by norm_num)

theorem c22250R_101_17 : rowsJ2 101 102 58 340 ≤ 85491884828604 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2666 c22250R_101_18 (by norm_num)

theorem c22250R_101_16 : rowsJ2 101 102 53 340 ≤ 85867590356632 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2665 c22250R_101_17 (by norm_num)

theorem c22250R_101_15 : rowsJ2 101 102 50 340 ≤ 88720657760258 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2664 c22250R_101_16 (by norm_num)

theorem c22250R_101_14 : rowsJ2 101 102 48 340 ≤ 93541586655664 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2663 c22250R_101_15 (by norm_num)

theorem c22250R_101_13 : rowsJ2 101 102 46 340 ≤ 102355156623614 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2662 c22250R_101_14 (by norm_num)

theorem c22250R_101_12 : rowsJ2 101 102 44 340 ≤ 116242379530955 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2661 c22250R_101_13 (by norm_num)

theorem c22250R_101_11 : rowsJ2 101 102 43 340 ≤ 125296957455538 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2660 c22250R_101_12 (by norm_num)

theorem c22250R_101_10 : rowsJ2 101 102 42 340 ≤ 135869491602762 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2659 c22250R_101_11 (by norm_num)

theorem c22250R_101_9 : rowsJ2 101 102 41 340 ≤ 148149068221369 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2658 c22250R_101_10 (by norm_num)

theorem c22250R_101_8 : rowsJ2 101 102 40 340 ≤ 162329369144863 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2657 c22250R_101_9 (by norm_num)

theorem c22250R_101_7 : rowsJ2 101 102 39 340 ≤ 178546680546133 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2656 c22250R_101_8 (by norm_num)

theorem c22250R_101_6 : rowsJ2 101 102 38 340 ≤ 193060509470961 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2655 c22250R_101_7 (by norm_num)

theorem c22250R_101_5 : rowsJ2 101 102 37 340 ≤ 205924604140849 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2654 c22250R_101_6 (by norm_num)

theorem c22250R_101_4 : rowsJ2 101 102 36 340 ≤ 216693028342294 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2653 c22250R_101_5 (by norm_num)

theorem c22250R_101_3 : rowsJ2 101 102 34 340 ≤ 232211020614101 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2652 c22250R_101_4 (by norm_num)

theorem c22250R_101_2 : rowsJ2 101 102 31 340 ≤ 243399333738334 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2651 c22250R_101_3 (by norm_num)

theorem c22250R_101_1 : rowsJ2 101 102 19 340 ≤ 245187892082066 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2650 c22250R_101_2 (by norm_num)

theorem c22250R_101_0 : rowsJ2 101 102 0 340 ≤ 245187892082066 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2649 c22250R_101_1 (by norm_num)

theorem hr22250R_101 : rows2 101 102 ≤ 245187892082066 := rows2_le_of_rowsJ2 101 102 c22250R_101_0

theorem c22250R_102_39 : rowsJ2 102 103 101 340 ≤ 24861033999356 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2732 rows22250R_2733 (by norm_num)

theorem c22250R_102_38 : rowsJ2 102 103 100 340 ≤ 35219379966613 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2731 c22250R_102_39 (by norm_num)

theorem c22250R_102_37 : rowsJ2 102 103 99 340 ≤ 44357420332690 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2730 c22250R_102_38 (by norm_num)

theorem c22250R_102_36 : rowsJ2 102 103 98 340 ≤ 52340108088279 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2729 c22250R_102_37 (by norm_num)

theorem c22250R_102_35 : rowsJ2 102 103 97 340 ≤ 59297740787868 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2728 c22250R_102_36 (by norm_num)

theorem c22250R_102_34 : rowsJ2 102 103 96 340 ≤ 65290021389559 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2727 c22250R_102_35 (by norm_num)

theorem c22250R_102_33 : rowsJ2 102 103 95 340 ≤ 70440901433141 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2726 c22250R_102_34 (by norm_num)

theorem c22250R_102_32 : rowsJ2 102 103 93 340 ≤ 78502286865203 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2725 c22250R_102_33 (by norm_num)

theorem c22250R_102_31 : rowsJ2 102 103 91 340 ≤ 84159236557771 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2724 c22250R_102_32 (by norm_num)

theorem c22250R_102_30 : rowsJ2 102 103 89 340 ≤ 88055949203753 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2723 c22250R_102_31 (by norm_num)

theorem c22250R_102_29 : rowsJ2 102 103 88 340 ≤ 89529917772647 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2722 c22250R_102_30 (by norm_num)

theorem c22250R_102_28 : rowsJ2 102 103 87 340 ≤ 90807904214687 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2721 c22250R_102_29 (by norm_num)

theorem c22250R_102_27 : rowsJ2 102 103 86 340 ≤ 91931251076370 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2720 c22250R_102_28 (by norm_num)

theorem c22250R_102_26 : rowsJ2 102 103 85 340 ≤ 93002089741346 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2719 c22250R_102_27 (by norm_num)

theorem c22250R_102_25 : rowsJ2 102 103 84 340 ≤ 94102778293942 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2718 c22250R_102_26 (by norm_num)

theorem c22250R_102_24 : rowsJ2 102 103 83 340 ≤ 95329670806973 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2717 c22250R_102_25 (by norm_num)

theorem c22250R_102_23 : rowsJ2 102 103 82 340 ≤ 96679844293907 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2716 c22250R_102_24 (by norm_num)

theorem c22250R_102_22 : rowsJ2 102 103 81 340 ≤ 98167711614367 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2715 c22250R_102_23 (by norm_num)

theorem c22250R_102_21 : rowsJ2 102 103 80 340 ≤ 99243467657882 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2714 c22250R_102_22 (by norm_num)

theorem c22250R_102_20 : rowsJ2 102 103 79 340 ≤ 99980112492039 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2713 c22250R_102_21 (by norm_num)

theorem c22250R_102_19 : rowsJ2 102 103 76 340 ≤ 100767962768306 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2712 c22250R_102_20 (by norm_num)

theorem c22250R_102_18 : rowsJ2 102 103 72 340 ≤ 100783293755350 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2711 c22250R_102_19 (by norm_num)

theorem c22250R_102_17 : rowsJ2 102 103 66 340 ≤ 100783293755350 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2710 c22250R_102_18 (by norm_num)

theorem c22250R_102_16 : rowsJ2 102 103 57 340 ≤ 100783293755350 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2709 c22250R_102_17 (by norm_num)

theorem c22250R_102_15 : rowsJ2 102 103 52 340 ≤ 101160237152815 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2708 c22250R_102_16 (by norm_num)

theorem c22250R_102_14 : rowsJ2 102 103 49 340 ≤ 104119662073847 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2707 c22250R_102_15 (by norm_num)

theorem c22250R_102_13 : rowsJ2 102 103 47 340 ≤ 109454362122428 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2706 c22250R_102_14 (by norm_num)

theorem c22250R_102_12 : rowsJ2 102 103 45 340 ≤ 119121707703410 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2705 c22250R_102_13 (by norm_num)

theorem c22250R_102_11 : rowsJ2 102 103 43 340 ≤ 133904511059597 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2704 c22250R_102_12 (by norm_num)

theorem c22250R_102_10 : rowsJ2 102 103 42 340 ≤ 143424538051908 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2703 c22250R_102_11 (by norm_num)

theorem c22250R_102_9 : rowsJ2 102 103 41 340 ≤ 154582117252634 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2702 c22250R_102_10 (by norm_num)

theorem c22250R_102_8 : rowsJ2 102 103 40 340 ≤ 167572226640352 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2701 c22250R_102_9 (by norm_num)

theorem c22250R_102_7 : rowsJ2 102 103 39 340 ≤ 182594819593502 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2700 c22250R_102_8 (by norm_num)

theorem c22250R_102_6 : rowsJ2 102 103 38 340 ≤ 197794082119095 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2699 c22250R_102_7 (by norm_num)

theorem c22250R_102_5 : rowsJ2 102 103 37 340 ≤ 211247946507972 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2698 c22250R_102_6 (by norm_num)

theorem c22250R_102_4 : rowsJ2 102 103 36 340 ≤ 222508396735523 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2697 c22250R_102_5 (by norm_num)

theorem c22250R_102_3 : rowsJ2 102 103 34 340 ≤ 239161687856211 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2696 c22250R_102_4 (by norm_num)

theorem c22250R_102_2 : rowsJ2 102 103 31 340 ≤ 251393650855319 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2695 c22250R_102_3 (by norm_num)

theorem c22250R_102_1 : rowsJ2 102 103 20 340 ≤ 253833709888787 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2694 c22250R_102_2 (by norm_num)

theorem c22250R_102_0 : rowsJ2 102 103 0 340 ≤ 253833709888787 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2693 c22250R_102_1 (by norm_num)

theorem hr22250R_102 : rows2 102 103 ≤ 253833709888787 := rows2_le_of_rowsJ2 102 103 c22250R_102_0

theorem c22250R_103_36 : rowsJ2 103 104 101 340 ≤ 176341309396435 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2770 rows22250R_2771 (by norm_num)

theorem c22250R_103_35 : rowsJ2 103 104 100 340 ≤ 187352871178679 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2769 c22250R_103_36 (by norm_num)

theorem c22250R_103_34 : rowsJ2 103 104 99 340 ≤ 197049741517320 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2768 c22250R_103_35 (by norm_num)

theorem c22250R_103_33 : rowsJ2 103 104 98 340 ≤ 205551511319941 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2767 c22250R_103_34 (by norm_num)

theorem c22250R_103_32 : rowsJ2 103 104 97 340 ≤ 212940282311615 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2766 c22250R_103_33 (by norm_num)

theorem c22250R_103_31 : rowsJ2 103 104 96 340 ≤ 219328789885970 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2765 c22250R_103_32 (by norm_num)

theorem c22250R_103_30 : rowsJ2 103 104 94 340 ≤ 229441808051444 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2764 c22250R_103_31 (by norm_num)

theorem c22250R_103_29 : rowsJ2 103 104 92 340 ≤ 236604763352793 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2763 c22250R_103_30 (by norm_num)

theorem c22250R_103_28 : rowsJ2 103 104 90 340 ≤ 241494399349054 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2762 c22250R_103_29 (by norm_num)

theorem c22250R_103_27 : rowsJ2 103 104 88 340 ≤ 244754890332216 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2761 c22250R_103_28 (by norm_num)

theorem c22250R_103_26 : rowsJ2 103 104 86 340 ≤ 247002249647984 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2760 c22250R_103_27 (by norm_num)

theorem c22250R_103_25 : rowsJ2 103 104 85 340 ≤ 247926989892072 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2759 c22250R_103_26 (by norm_num)

theorem c22250R_103_24 : rowsJ2 103 104 84 340 ≤ 248824547153368 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2758 c22250R_103_25 (by norm_num)

theorem c22250R_103_23 : rowsJ2 103 104 83 340 ≤ 249793559694918 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2757 c22250R_103_24 (by norm_num)

theorem c22250R_103_22 : rowsJ2 103 104 82 340 ≤ 250873117559121 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2756 c22250R_103_23 (by norm_num)

theorem c22250R_103_21 : rowsJ2 103 104 81 340 ≤ 252076221466535 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2755 c22250R_103_22 (by norm_num)

theorem c22250R_103_20 : rowsJ2 103 104 80 340 ≤ 253143884114627 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2754 c22250R_103_21 (by norm_num)

theorem c22250R_103_19 : rowsJ2 103 104 78 340 ≤ 254324571150071 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2753 c22250R_103_20 (by norm_num)

theorem c22250R_103_18 : rowsJ2 103 104 76 340 ≤ 254657090715653 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2752 c22250R_103_19 (by norm_num)

theorem c22250R_103_17 : rowsJ2 103 104 72 340 ≤ 254672319518015 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2751 c22250R_103_18 (by norm_num)

theorem c22250R_103_16 : rowsJ2 103 104 66 340 ≤ 254672319518015 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2750 c22250R_103_17 (by norm_num)

theorem c22250R_103_15 : rowsJ2 103 104 56 340 ≤ 254672319518015 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2749 c22250R_103_16 (by norm_num)

theorem c22250R_103_14 : rowsJ2 103 104 51 340 ≤ 255050560266166 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2748 c22250R_103_15 (by norm_num)

theorem c22250R_103_13 : rowsJ2 103 104 48 340 ≤ 258315095349439 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2747 c22250R_103_14 (by norm_num)

theorem c22250R_103_12 : rowsJ2 103 104 46 340 ≤ 264381918015094 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2746 c22250R_103_13 (by norm_num)

theorem c22250R_103_11 : rowsJ2 103 104 44 340 ≤ 274922352867158 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2745 c22250R_103_12 (by norm_num)

theorem c22250R_103_10 : rowsJ2 103 104 42 340 ≤ 290621862239892 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2744 c22250R_103_11 (by norm_num)

theorem c22250R_103_9 : rowsJ2 103 104 41 340 ≤ 300725920972655 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2743 c22250R_103_10 (by norm_num)

theorem c22250R_103_8 : rowsJ2 103 104 40 340 ≤ 312593251588349 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2742 c22250R_103_9 (by norm_num)

theorem c22250R_103_7 : rowsJ2 103 104 39 340 ≤ 326425106811027 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2741 c22250R_103_8 (by norm_num)

theorem c22250R_103_6 : rowsJ2 103 104 38 340 ≤ 342428122641634 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2740 c22250R_103_7 (by norm_num)

theorem c22250R_103_5 : rowsJ2 103 104 37 340 ≤ 356589181765694 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2739 c22250R_103_6 (by norm_num)

theorem c22250R_103_4 : rowsJ2 103 104 36 340 ≤ 368339797882659 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2738 c22250R_103_5 (by norm_num)

theorem c22250R_103_3 : rowsJ2 103 104 34 340 ≤ 386016352727755 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2737 c22250R_103_4 (by norm_num)

theorem c22250R_103_2 : rowsJ2 103 104 31 340 ≤ 399405959523263 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2736 c22250R_103_3 (by norm_num)

theorem c22250R_103_1 : rowsJ2 103 104 21 340 ≤ 402610193476700 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2735 c22250R_103_2 (by norm_num)

theorem c22250R_103_0 : rowsJ2 103 104 0 340 ≤ 402610193476700 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2734 c22250R_103_1 (by norm_num)

theorem hr22250R_103 : rows2 103 104 ≤ 402610193476700 := rows2_le_of_rowsJ2 103 104 c22250R_103_0

theorem c22250R_104_34 : rowsJ2 104 105 101 340 ≤ 290840349740506 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2806 rows22250R_2807 (by norm_num)

theorem c22250R_104_33 : rowsJ2 104 105 100 340 ≤ 302482028722948 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2805 c22250R_104_34 (by norm_num)

theorem c22250R_104_32 : rowsJ2 104 105 99 340 ≤ 312782256968476 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2804 c22250R_104_33 (by norm_num)

theorem c22250R_104_31 : rowsJ2 104 105 98 340 ≤ 321811137038444 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2803 c22250R_104_32 (by norm_num)

theorem c22250R_104_30 : rowsJ2 104 105 97 340 ≤ 329687871974357 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2802 c22250R_104_31 (by norm_num)

theorem c22250R_104_29 : rowsJ2 104 105 96 340 ≤ 336477077177445 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2801 c22250R_104_30 (by norm_num)

theorem c22250R_104_28 : rowsJ2 104 105 94 340 ≤ 347241237780277 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2800 c22250R_104_29 (by norm_num)

theorem c22250R_104_27 : rowsJ2 104 105 92 340 ≤ 354837178667530 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2799 c22250R_104_28 (by norm_num)

theorem c22250R_104_26 : rowsJ2 104 105 90 340 ≤ 359958968262021 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2798 c22250R_104_27 (by norm_num)

theorem c22250R_104_25 : rowsJ2 104 105 88 340 ≤ 363266316740437 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2797 c22250R_104_26 (by norm_num)

theorem c22250R_104_24 : rowsJ2 104 105 86 340 ≤ 365389197172889 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2796 c22250R_104_25 (by norm_num)

theorem c22250R_104_23 : rowsJ2 104 105 84 340 ≤ 366930713842455 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2795 c22250R_104_24 (by norm_num)

theorem c22250R_104_22 : rowsJ2 104 105 83 340 ≤ 367672395839313 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2794 c22250R_104_23 (by norm_num)

theorem c22250R_104_21 : rowsJ2 104 105 82 340 ≤ 368511873913418 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2793 c22250R_104_22 (by norm_num)

theorem c22250R_104_20 : rowsJ2 104 105 81 340 ≤ 369462135400071 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2792 c22250R_104_21 (by norm_num)

theorem c22250R_104_19 : rowsJ2 104 105 80 340 ≤ 370520535087272 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2791 c22250R_104_20 (by norm_num)

theorem c22250R_104_18 : rowsJ2 104 105 78 340 ≤ 371692326909678 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2790 c22250R_104_19 (by norm_num)

theorem c22250R_104_17 : rowsJ2 104 105 76 340 ≤ 372022644827640 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2789 c22250R_104_18 (by norm_num)

theorem c22250R_104_16 : rowsJ2 104 105 72 340 ≤ 372037772798472 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2788 c22250R_104_17 (by norm_num)

theorem c22250R_104_15 : rowsJ2 104 105 65 340 ≤ 372037772798472 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2787 c22250R_104_16 (by norm_num)

theorem c22250R_104_14 : rowsJ2 104 105 55 340 ≤ 372037772798472 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2786 c22250R_104_15 (by norm_num)

theorem c22250R_104_13 : rowsJ2 104 105 50 340 ≤ 372417371524808 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2785 c22250R_104_14 (by norm_num)

theorem c22250R_104_12 : rowsJ2 104 105 47 340 ≤ 376294173365482 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2784 c22250R_104_13 (by norm_num)

theorem c22250R_104_11 : rowsJ2 104 105 45 340 ≤ 383215081885695 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2783 c22250R_104_12 (by norm_num)

theorem c22250R_104_10 : rowsJ2 104 105 43 340 ≤ 394648839795500 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2782 c22250R_104_11 (by norm_num)

theorem c22250R_104_9 : rowsJ2 104 105 41 340 ≤ 411395036054074 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2781 c22250R_104_10 (by norm_num)

theorem c22250R_104_8 : rowsJ2 104 105 40 340 ≤ 422208449060965 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2780 c22250R_104_9 (by norm_num)

theorem c22250R_104_7 : rowsJ2 104 105 39 340 ≤ 434917386354616 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2779 c22250R_104_8 (by norm_num)

theorem c22250R_104_6 : rowsJ2 104 105 38 340 ≤ 449729787650551 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2778 c22250R_104_7 (by norm_num)

theorem c22250R_104_5 : rowsJ2 104 105 37 340 ≤ 464718459599158 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2777 c22250R_104_6 (by norm_num)

theorem c22250R_104_4 : rowsJ2 104 105 36 340 ≤ 477075128200173 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2776 c22250R_104_5 (by norm_num)

theorem c22250R_104_3 : rowsJ2 104 105 34 340 ≤ 495660555628144 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2775 c22250R_104_4 (by norm_num)

theorem c22250R_104_2 : rowsJ2 104 105 31 340 ≤ 510212665576592 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2774 c22250R_104_3 (by norm_num)

theorem c22250R_104_1 : rowsJ2 104 105 23 340 ≤ 514297936669473 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2773 c22250R_104_2 (by norm_num)

theorem c22250R_104_0 : rowsJ2 104 105 0 340 ≤ 514297936669473 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_2772 c22250R_104_1 (by norm_num)

theorem hr22250R_104 : rows2 104 105 ≤ 514297936669473 := rows2_le_of_rowsJ2 104 105 c22250R_104_0

theorem c22250R_105_31 : rowsJ2 105 106 100 340 ≤ 513517558158981 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2839 rows22250R_2840 (by norm_num)

theorem c22250R_105_30 : rowsJ2 105 106 99 340 ≤ 524434285256495 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2838 c22250R_105_31 (by norm_num)

theorem c22250R_105_29 : rowsJ2 105 106 98 340 ≤ 534053868756021 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2837 c22250R_105_30 (by norm_num)

theorem c22250R_105_28 : rowsJ2 105 106 97 340 ≤ 542445983534470 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2836 c22250R_105_29 (by norm_num)

theorem c22250R_105_27 : rowsJ2 105 106 96 340 ≤ 549729466726818 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2835 c22250R_105_28 (by norm_num)

theorem c22250R_105_26 : rowsJ2 105 106 94 340 ≤ 561275903114133 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2834 c22250R_105_27 (by norm_num)

theorem c22250R_105_25 : rowsJ2 105 106 92 340 ≤ 569430003078009 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2833 c22250R_105_26 (by norm_num)

theorem c22250R_105_24 : rowsJ2 105 106 90 340 ≤ 574904003790171 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2832 c22250R_105_25 (by norm_num)

theorem c22250R_105_23 : rowsJ2 105 106 88 340 ≤ 578373895640238 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2831 c22250R_105_24 (by norm_num)

theorem c22250R_105_22 : rowsJ2 105 106 86 340 ≤ 580484271088719 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2830 c22250R_105_23 (by norm_num)

theorem c22250R_105_21 : rowsJ2 105 106 84 340 ≤ 581852710297350 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2829 c22250R_105_22 (by norm_num)

theorem c22250R_105_20 : rowsJ2 105 106 82 340 ≤ 583069980266966 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2828 c22250R_105_21 (by norm_num)

theorem c22250R_105_19 : rowsJ2 105 106 81 340 ≤ 583797538017920 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2827 c22250R_105_20 (by norm_num)

theorem c22250R_105_18 : rowsJ2 105 106 80 340 ≤ 584620547956025 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2826 c22250R_105_19 (by norm_num)

theorem c22250R_105_17 : rowsJ2 105 106 78 340 ≤ 585782269213590 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2825 c22250R_105_18 (by norm_num)

theorem c22250R_105_16 : rowsJ2 105 106 75 340 ≤ 586125442912609 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2824 c22250R_105_17 (by norm_num)

theorem c22250R_105_15 : rowsJ2 105 106 71 340 ≤ 586125442912609 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2823 c22250R_105_16 (by norm_num)

theorem c22250R_105_14 : rowsJ2 105 106 64 340 ≤ 586125442912609 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2822 c22250R_105_15 (by norm_num)

theorem c22250R_105_13 : rowsJ2 105 106 54 340 ≤ 586125442912609 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2821 c22250R_105_14 (by norm_num)

theorem c22250R_105_12 : rowsJ2 105 106 49 340 ≤ 586604698160142 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2820 c22250R_105_13 (by norm_num)

theorem c22250R_105_11 : rowsJ2 105 106 46 340 ≤ 591417903524982 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2819 c22250R_105_12 (by norm_num)

theorem c22250R_105_10 : rowsJ2 105 106 44 340 ≤ 599212398570243 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2818 c22250R_105_11 (by norm_num)

theorem c22250R_105_9 : rowsJ2 105 106 42 340 ≤ 611560679138765 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2817 c22250R_105_10 (by norm_num)

theorem c22250R_105_8 : rowsJ2 105 106 40 340 ≤ 629599356426042 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2816 c22250R_105_9 (by norm_num)

theorem c22250R_105_7 : rowsJ2 105 106 39 340 ≤ 641254668431435 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2815 c22250R_105_8 (by norm_num)

theorem c22250R_105_6 : rowsJ2 105 106 38 340 ≤ 654944730824747 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2814 c22250R_105_7 (by norm_num)

theorem c22250R_105_5 : rowsJ2 105 106 37 340 ≤ 670761958954452 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2813 c22250R_105_6 (by norm_num)

theorem c22250R_105_4 : rowsJ2 105 106 36 340 ≤ 683843463542122 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2812 c22250R_105_5 (by norm_num)

theorem c22250R_105_3 : rowsJ2 105 106 34 340 ≤ 703336530522927 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2811 c22250R_105_4 (by norm_num)

theorem c22250R_105_2 : rowsJ2 105 106 31 340 ≤ 719164932148416 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2810 c22250R_105_3 (by norm_num)

theorem c22250R_105_1 : rowsJ2 105 106 24 340 ≤ 724133302072778 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2809 c22250R_105_2 (by norm_num)

theorem c22250R_105_0 : rowsJ2 105 106 0 340 ≤ 724133302072778 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_2808 c22250R_105_1 (by norm_num)

theorem hr22250R_105 : rows2 105 106 ≤ 724133302072778 := rows2_le_of_rowsJ2 105 106 c22250R_105_0

theorem c22250R_106_30 : rowsJ2 106 107 100 340 ≤ 617791074617841 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2871 rows22250R_2872 (by norm_num)

theorem c22250R_106_29 : rowsJ2 106 107 99 340 ≤ 629353647813545 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2870 c22250R_106_30 (by norm_num)

theorem c22250R_106_28 : rowsJ2 106 107 98 340 ≤ 639538116425994 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2869 c22250R_106_29 (by norm_num)

theorem c22250R_106_27 : rowsJ2 106 107 97 340 ≤ 648470033960278 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2868 c22250R_106_28 (by norm_num)

theorem c22250R_106_26 : rowsJ2 106 107 96 340 ≤ 656218661222879 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2867 c22250R_106_27 (by norm_num)

theorem c22250R_106_25 : rowsJ2 106 107 94 340 ≤ 668585466995700 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2866 c22250R_106_26 (by norm_num)

theorem c22250R_106_24 : rowsJ2 106 107 92 340 ≤ 677345095049826 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2865 c22250R_106_25 (by norm_num)

theorem c22250R_106_23 : rowsJ2 106 107 90 340 ≤ 683212083010064 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2864 c22250R_106_24 (by norm_num)

theorem c22250R_106_22 : rowsJ2 106 107 88 340 ≤ 686879452812334 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2863 c22250R_106_23 (by norm_num)

theorem c22250R_106_21 : rowsJ2 106 107 86 340 ≤ 689007075342545 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2862 c22250R_106_22 (by norm_num)

theorem c22250R_106_20 : rowsJ2 106 107 84 340 ≤ 690226264930387 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2861 c22250R_106_21 (by norm_num)

theorem c22250R_106_19 : rowsJ2 106 107 82 340 ≤ 691142631004947 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2860 c22250R_106_20 (by norm_num)

theorem c22250R_106_18 : rowsJ2 106 107 80 340 ≤ 692294635401780 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2859 c22250R_106_19 (by norm_num)

theorem c22250R_106_17 : rowsJ2 106 107 78 340 ≤ 693446514239686 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2858 c22250R_106_18 (by norm_num)

theorem c22250R_106_16 : rowsJ2 106 107 75 340 ≤ 693787445444516 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2857 c22250R_106_17 (by norm_num)

theorem c22250R_106_15 : rowsJ2 106 107 71 340 ≤ 693787445444516 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2856 c22250R_106_16 (by norm_num)

theorem c22250R_106_14 : rowsJ2 106 107 64 340 ≤ 693787445444516 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2855 c22250R_106_15 (by norm_num)

theorem c22250R_106_13 : rowsJ2 106 107 53 340 ≤ 693813153002746 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2854 c22250R_106_14 (by norm_num)

theorem c22250R_106_12 : rowsJ2 106 107 48 340 ≤ 694594754783005 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2853 c22250R_106_13 (by norm_num)

theorem c22250R_106_11 : rowsJ2 106 107 45 340 ≤ 700576700632357 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2852 c22250R_106_12 (by norm_num)

theorem c22250R_106_10 : rowsJ2 106 107 43 340 ≤ 709265226234956 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2851 c22250R_106_11 (by norm_num)

theorem c22250R_106_9 : rowsJ2 106 107 41 340 ≤ 722659389830803 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2850 c22250R_106_10 (by norm_num)

theorem c22250R_106_8 : rowsJ2 106 107 39 340 ≤ 742250524666690 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2849 c22250R_106_9 (by norm_num)

theorem c22250R_106_7 : rowsJ2 106 107 38 340 ≤ 754888022507916 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2848 c22250R_106_8 (by norm_num)

theorem c22250R_106_6 : rowsJ2 106 107 37 340 ≤ 769583624798156 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2847 c22250R_106_7 (by norm_num)

theorem c22250R_106_5 : rowsJ2 106 107 36 340 ≤ 783511826963769 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2846 c22250R_106_6 (by norm_num)

theorem c22250R_106_4 : rowsJ2 106 107 35 340 ≤ 794834400100912 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2845 c22250R_106_5 (by norm_num)

theorem c22250R_106_3 : rowsJ2 106 107 33 340 ≤ 811463112693871 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2844 c22250R_106_4 (by norm_num)

theorem c22250R_106_2 : rowsJ2 106 107 31 340 ≤ 821136661071673 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2843 c22250R_106_3 (by norm_num)

theorem c22250R_106_1 : rowsJ2 106 107 25 340 ≤ 826993712490246 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2842 c22250R_106_2 (by norm_num)

theorem c22250R_106_0 : rowsJ2 106 107 0 340 ≤ 826993712490246 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_2841 c22250R_106_1 (by norm_num)

theorem hr22250R_106 : rows2 106 107 ≤ 826993712490246 := rows2_le_of_rowsJ2 106 107 c22250R_106_0

theorem c22250R_107_29 : rowsJ2 107 108 99 340 ≤ 828394855887673 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2902 rows22250R_2903 (by norm_num)

theorem c22250R_107_28 : rowsJ2 107 108 98 340 ≤ 839210846829250 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2901 c22250R_107_29 (by norm_num)

theorem c22250R_107_27 : rowsJ2 107 108 97 340 ≤ 848694324351583 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2900 c22250R_107_28 (by norm_num)

theorem c22250R_107_26 : rowsJ2 107 108 96 340 ≤ 856970419773671 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2899 c22250R_107_27 (by norm_num)

theorem c22250R_107_25 : rowsJ2 107 108 95 340 ≤ 864107997535503 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2898 c22250R_107_26 (by norm_num)

theorem c22250R_107_24 : rowsJ2 107 108 93 340 ≤ 875385743504620 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2897 c22250R_107_25 (by norm_num)

theorem c22250R_107_23 : rowsJ2 107 108 91 340 ≤ 883231966560803 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2896 c22250R_107_24 (by norm_num)

theorem c22250R_107_22 : rowsJ2 107 108 89 340 ≤ 888327426364466 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2895 c22250R_107_23 (by norm_num)

theorem c22250R_107_21 : rowsJ2 107 108 87 340 ≤ 891364868875770 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2894 c22250R_107_22 (by norm_num)

theorem c22250R_107_20 : rowsJ2 107 108 85 340 ≤ 893004508965764 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2893 c22250R_107_21 (by norm_num)

theorem c22250R_107_19 : rowsJ2 107 108 83 340 ≤ 893878613597142 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2892 c22250R_107_20 (by norm_num)

theorem c22250R_107_18 : rowsJ2 107 108 81 340 ≤ 894594347133154 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2891 c22250R_107_19 (by norm_num)

theorem c22250R_107_17 : rowsJ2 107 108 79 340 ≤ 895559579882041 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2890 c22250R_107_18 (by norm_num)

theorem c22250R_107_16 : rowsJ2 107 108 77 340 ≤ 896229738402088 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2889 c22250R_107_17 (by norm_num)

theorem c22250R_107_15 : rowsJ2 107 108 74 340 ≤ 896333110363239 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2888 c22250R_107_16 (by norm_num)

theorem c22250R_107_14 : rowsJ2 107 108 70 340 ≤ 896333110363239 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2887 c22250R_107_15 (by norm_num)

theorem c22250R_107_13 : rowsJ2 107 108 63 340 ≤ 896333110363239 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2886 c22250R_107_14 (by norm_num)

theorem c22250R_107_12 : rowsJ2 107 108 52 340 ≤ 896513861043225 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2885 c22250R_107_13 (by norm_num)

theorem c22250R_107_11 : rowsJ2 107 108 47 340 ≤ 897911525734631 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2884 c22250R_107_12 (by norm_num)

theorem c22250R_107_10 : rowsJ2 107 108 44 340 ≤ 905196890279227 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2883 c22250R_107_11 (by norm_num)

theorem c22250R_107_9 : rowsJ2 107 108 42 340 ≤ 914800881405434 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2882 c22250R_107_10 (by norm_num)

theorem c22250R_107_8 : rowsJ2 107 108 40 340 ≤ 929489599170110 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2881 c22250R_107_9 (by norm_num)

theorem c22250R_107_7 : rowsJ2 107 108 38 340 ≤ 950908369717677 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2880 c22250R_107_8 (by norm_num)

theorem c22250R_107_6 : rowsJ2 107 108 37 340 ≤ 964552628792255 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2879 c22250R_107_7 (by norm_num)

theorem c22250R_107_5 : rowsJ2 107 108 36 340 ≤ 979328662884340 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2878 c22250R_107_6 (by norm_num)

theorem c22250R_107_4 : rowsJ2 107 108 35 340 ≤ 991393588439303 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2877 c22250R_107_5 (by norm_num)

theorem c22250R_107_3 : rowsJ2 107 108 33 340 ≤ 1008957076929712 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2876 c22250R_107_4 (by norm_num)

theorem c22250R_107_2 : rowsJ2 107 108 31 340 ≤ 1019493498159616 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2875 c22250R_107_3 (by norm_num)

theorem c22250R_107_1 : rowsJ2 107 108 26 340 ≤ 1026239038821926 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2874 c22250R_107_2 (by norm_num)

theorem c22250R_107_0 : rowsJ2 107 108 0 340 ≤ 1026239038821926 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_2873 c22250R_107_1 (by norm_num)

theorem hr22250R_107 : rows2 107 108 ≤ 1026239038821926 := rows2_le_of_rowsJ2 107 108 c22250R_107_0

theorem c22250R_108_27 : rowsJ2 108 109 99 340 ≤ 922899668974421 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2931 rows22250R_2932 (by norm_num)

theorem c22250R_108_26 : rowsJ2 108 109 98 340 ≤ 934322247994551 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2930 c22250R_108_27 (by norm_num)

theorem c22250R_108_25 : rowsJ2 108 109 97 340 ≤ 944383783696366 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2929 c22250R_108_26 (by norm_num)

theorem c22250R_108_24 : rowsJ2 108 109 96 340 ≤ 953158709044394 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2928 c22250R_108_25 (by norm_num)

theorem c22250R_108_23 : rowsJ2 108 109 95 340 ≤ 960771751942297 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2927 c22250R_108_24 (by norm_num)

theorem c22250R_108_22 : rowsJ2 108 109 93 340 ≤ 972835498392817 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2926 c22250R_108_23 (by norm_num)

theorem c22250R_108_21 : rowsJ2 108 109 91 340 ≤ 981298991307577 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2925 c22250R_108_22 (by norm_num)

theorem c22250R_108_20 : rowsJ2 108 109 89 340 ≤ 986844512632106 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2924 c22250R_108_21 (by norm_num)

theorem c22250R_108_19 : rowsJ2 108 109 86 340 ≤ 991137052603612 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2923 c22250R_108_20 (by norm_num)

theorem c22250R_108_18 : rowsJ2 108 109 83 340 ≤ 992618529914612 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2922 c22250R_108_19 (by norm_num)

theorem c22250R_108_17 : rowsJ2 108 109 81 340 ≤ 993081747969876 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2921 c22250R_108_18 (by norm_num)

theorem c22250R_108_16 : rowsJ2 108 109 79 340 ≤ 993739946242616 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2920 c22250R_108_17 (by norm_num)

theorem c22250R_108_15 : rowsJ2 108 109 77 340 ≤ 994404659662166 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2919 c22250R_108_16 (by norm_num)

theorem c22250R_108_14 : rowsJ2 108 109 74 340 ≤ 994507364845724 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2918 c22250R_108_15 (by norm_num)

theorem c22250R_108_13 : rowsJ2 108 109 70 340 ≤ 994507364845724 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2917 c22250R_108_14 (by norm_num)

theorem c22250R_108_12 : rowsJ2 108 109 62 340 ≤ 994611415154129 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2916 c22250R_108_13 (by norm_num)

theorem c22250R_108_11 : rowsJ2 108 109 51 340 ≤ 994948178375476 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2915 c22250R_108_12 (by norm_num)

theorem c22250R_108_10 : rowsJ2 108 109 46 340 ≤ 996985275589405 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2914 c22250R_108_11 (by norm_num)

theorem c22250R_108_9 : rowsJ2 108 109 43 340 ≤ 1005286588758634 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2913 c22250R_108_10 (by norm_num)

theorem c22250R_108_8 : rowsJ2 108 109 41 340 ≤ 1015720974443998 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2912 c22250R_108_9 (by norm_num)

theorem c22250R_108_7 : rowsJ2 108 109 39 340 ≤ 1031744293106638 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2911 c22250R_108_8 (by norm_num)

theorem c22250R_108_6 : rowsJ2 108 109 37 340 ≤ 1054929040170124 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2910 c22250R_108_7 (by norm_num)

theorem c22250R_108_5 : rowsJ2 108 109 36 340 ≤ 1068648555097430 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2909 c22250R_108_6 (by norm_num)

theorem c22250R_108_4 : rowsJ2 108 109 35 340 ≤ 1081579226361888 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2908 c22250R_108_5 (by norm_num)

theorem c22250R_108_3 : rowsJ2 108 109 33 340 ≤ 1100197004175029 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2907 c22250R_108_4 (by norm_num)

theorem c22250R_108_2 : rowsJ2 108 109 31 340 ≤ 1111598357034906 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2906 c22250R_108_3 (by norm_num)

theorem c22250R_108_1 : rowsJ2 108 109 26 340 ≤ 1119350736750777 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2905 c22250R_108_2 (by norm_num)

theorem c22250R_108_0 : rowsJ2 108 109 0 340 ≤ 1119350736750777 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_2904 c22250R_108_1 (by norm_num)

theorem hr22250R_108 : rows2 108 109 ≤ 1119350736750777 := rows2_le_of_rowsJ2 108 109 c22250R_108_0

theorem c22250R_109_25 : rowsJ2 109 110 98 340 ≤ 1121905269946171 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2958 rows22250R_2959 (by norm_num)

theorem c22250R_109_24 : rowsJ2 109 110 97 340 ≤ 1132558289396194 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2957 c22250R_109_25 (by norm_num)

theorem c22250R_109_23 : rowsJ2 109 110 96 340 ≤ 1141897244197957 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2956 c22250R_109_24 (by norm_num)

theorem c22250R_109_22 : rowsJ2 109 110 95 340 ≤ 1149996105765795 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2955 c22250R_109_23 (by norm_num)

theorem c22250R_109_21 : rowsJ2 109 110 93 340 ≤ 1162914710909911 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2954 c22250R_109_22 (by norm_num)

theorem c22250R_109_20 : rowsJ2 109 110 91 340 ≤ 1172058634808727 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2953 c22250R_109_21 (by norm_num)

theorem c22250R_109_19 : rowsJ2 109 110 89 340 ≤ 1178128431896246 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2952 c22250R_109_20 (by norm_num)

theorem c22250R_109_18 : rowsJ2 109 110 86 340 ≤ 1182915063388517 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2951 c22250R_109_19 (by norm_num)

theorem c22250R_109_17 : rowsJ2 109 110 83 340 ≤ 1184463827754318 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2950 c22250R_109_18 (by norm_num)

theorem c22250R_109_16 : rowsJ2 109 110 80 340 ≤ 1184956140085973 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2949 c22250R_109_17 (by norm_num)

theorem c22250R_109_15 : rowsJ2 109 110 78 340 ≤ 1185477522836826 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2948 c22250R_109_16 (by norm_num)

theorem c22250R_109_14 : rowsJ2 109 110 76 340 ≤ 1185796036557551 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2947 c22250R_109_15 (by norm_num)

theorem c22250R_109_13 : rowsJ2 109 110 73 340 ≤ 1185810679757419 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2946 c22250R_109_14 (by norm_num)

theorem c22250R_109_12 : rowsJ2 109 110 68 340 ≤ 1185810679757419 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2945 c22250R_109_13 (by norm_num)

theorem c22250R_109_11 : rowsJ2 109 110 61 340 ≤ 1186461467552886 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2944 c22250R_109_12 (by norm_num)

theorem c22250R_109_10 : rowsJ2 109 110 50 340 ≤ 1186800962265414 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2943 c22250R_109_11 (by norm_num)

theorem c22250R_109_9 : rowsJ2 109 110 45 340 ≤ 1189812112823875 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2942 c22250R_109_10 (by norm_num)

theorem c22250R_109_8 : rowsJ2 109 110 42 340 ≤ 1199153926195085 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2941 c22250R_109_9 (by norm_num)

theorem c22250R_109_7 : rowsJ2 109 110 40 340 ≤ 1210665272956181 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2940 c22250R_109_8 (by norm_num)

theorem c22250R_109_6 : rowsJ2 109 110 38 340 ≤ 1228296285628184 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2939 c22250R_109_7 (by norm_num)

theorem c22250R_109_5 : rowsJ2 109 110 36 340 ≤ 1252445185713549 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2938 c22250R_109_6 (by norm_num)

theorem c22250R_109_4 : rowsJ2 109 110 35 340 ≤ 1266242946877461 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2937 c22250R_109_5 (by norm_num)

theorem c22250R_109_3 : rowsJ2 109 110 33 340 ≤ 1286154023415253 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2936 c22250R_109_4 (by norm_num)

theorem c22250R_109_2 : rowsJ2 109 110 31 340 ≤ 1298421574911842 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2935 c22250R_109_3 (by norm_num)

theorem c22250R_109_1 : rowsJ2 109 110 27 340 ≤ 1306948456575055 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2934 c22250R_109_2 (by norm_num)

theorem c22250R_109_0 : rowsJ2 109 110 0 340 ≤ 1307179948428130 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_2933 c22250R_109_1 (by norm_num)

theorem hr22250R_109 : rows2 109 110 ≤ 1307179948428130 := rows2_le_of_rowsJ2 109 110 c22250R_109_0

theorem c22250R_110_24 : rowsJ2 110 111 98 340 ≤ 1207065267953419 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2984 rows22250R_2985 (by norm_num)

theorem c22250R_110_23 : rowsJ2 110 111 97 340 ≤ 1218338588224905 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2983 c22250R_110_24 (by norm_num)

theorem c22250R_110_22 : rowsJ2 110 111 96 340 ≤ 1228213571135387 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2982 c22250R_110_23 (by norm_num)

theorem c22250R_110_21 : rowsJ2 110 111 95 340 ≤ 1236821812987966 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2981 c22250R_110_22 (by norm_num)

theorem c22250R_110_20 : rowsJ2 110 111 93 340 ≤ 1250582632708322 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2980 c22250R_110_21 (by norm_num)

theorem c22250R_110_19 : rowsJ2 110 111 91 340 ≤ 1260387164071260 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2979 c22250R_110_20 (by norm_num)

theorem c22250R_110_18 : rowsJ2 110 111 89 340 ≤ 1266955112722518 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2978 c22250R_110_19 (by norm_num)

theorem c22250R_110_17 : rowsJ2 110 111 87 340 ≤ 1270965967708478 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2977 c22250R_110_18 (by norm_num)

theorem c22250R_110_16 : rowsJ2 110 111 84 340 ≤ 1273583968465478 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2976 c22250R_110_17 (by norm_num)

theorem c22250R_110_15 : rowsJ2 110 111 81 340 ≤ 1274063535948530 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2975 c22250R_110_16 (by norm_num)

theorem c22250R_110_14 : rowsJ2 110 111 78 340 ≤ 1274456567120074 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2974 c22250R_110_15 (by norm_num)

theorem c22250R_110_13 : rowsJ2 110 111 76 340 ≤ 1274771771814467 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2973 c22250R_110_14 (by norm_num)

theorem c22250R_110_12 : rowsJ2 110 111 72 340 ≤ 1274786321764639 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2972 c22250R_110_13 (by norm_num)

theorem c22250R_110_11 : rowsJ2 110 111 67 340 ≤ 1274786321764639 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2971 c22250R_110_12 (by norm_num)

theorem c22250R_110_10 : rowsJ2 110 111 60 340 ≤ 1276302800633184 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2970 c22250R_110_11 (by norm_num)

theorem c22250R_110_9 : rowsJ2 110 111 49 340 ≤ 1276514472224567 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2969 c22250R_110_10 (by norm_num)

theorem c22250R_110_8 : rowsJ2 110 111 44 340 ≤ 1280309976116919 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2968 c22250R_110_9 (by norm_num)

theorem c22250R_110_7 : rowsJ2 110 111 41 340 ≤ 1290494685818630 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2967 c22250R_110_8 (by norm_num)

theorem c22250R_110_6 : rowsJ2 110 111 39 340 ≤ 1303114084363538 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2966 c22250R_110_7 (by norm_num)

theorem c22250R_110_5 : rowsJ2 110 111 37 340 ≤ 1322280514758057 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2965 c22250R_110_6 (by norm_num)

theorem c22250R_110_4 : rowsJ2 110 111 35 340 ≤ 1346566458510743 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2964 c22250R_110_5 (by norm_num)

theorem c22250R_110_3 : rowsJ2 110 111 33 340 ≤ 1368016074638339 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2963 c22250R_110_4 (by norm_num)

theorem c22250R_110_2 : rowsJ2 110 111 31 340 ≤ 1381151399274654 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2962 c22250R_110_3 (by norm_num)

theorem c22250R_110_1 : rowsJ2 110 111 27 340 ≤ 1390568907281036 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2961 c22250R_110_2 (by norm_num)

theorem c22250R_110_0 : rowsJ2 110 111 0 340 ≤ 1391037038365850 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_2960 c22250R_110_1 (by norm_num)

theorem hr22250R_110 : rows2 110 111 ≤ 1391037038365850 := rows2_le_of_rowsJ2 110 111 c22250R_110_0

theorem c22250R_111_22 : rowsJ2 111 112 97 340 ≤ 1394912914221059 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3008 rows22250R_3009 (by norm_num)

theorem c22250R_111_21 : rowsJ2 111 112 96 340 ≤ 1405392276689933 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3007 c22250R_111_22 (by norm_num)

theorem c22250R_111_20 : rowsJ2 111 112 95 340 ≤ 1414521728627176 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3006 c22250R_111_21 (by norm_num)

theorem c22250R_111_19 : rowsJ2 111 112 93 340 ≤ 1429197452225148 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3005 c22250R_111_20 (by norm_num)

theorem c22250R_111_18 : rowsJ2 111 112 91 340 ≤ 1439728916785008 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3004 c22250R_111_19 (by norm_num)

theorem c22250R_111_17 : rowsJ2 111 112 89 340 ≤ 1446855951013382 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3003 c22250R_111_18 (by norm_num)

theorem c22250R_111_16 : rowsJ2 111 112 86 340 ≤ 1452684645569294 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3002 c22250R_111_17 (by norm_num)

theorem c22250R_111_15 : rowsJ2 111 112 83 340 ≤ 1454606151796470 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3001 c22250R_111_16 (by norm_num)

theorem c22250R_111_14 : rowsJ2 111 112 80 340 ≤ 1454792342742696 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3000 c22250R_111_15 (by norm_num)

theorem c22250R_111_13 : rowsJ2 111 112 77 340 ≤ 1455066247497829 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_2999 c22250R_111_14 (by norm_num)

theorem c22250R_111_12 : rowsJ2 111 112 74 340 ≤ 1455167002979651 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_2998 c22250R_111_13 (by norm_num)

theorem c22250R_111_11 : rowsJ2 111 112 70 340 ≤ 1455167002979651 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_2997 c22250R_111_12 (by norm_num)

theorem c22250R_111_10 : rowsJ2 111 112 64 340 ≤ 1455801830904259 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_2996 c22250R_111_11 (by norm_num)

theorem c22250R_111_9 : rowsJ2 111 112 55 340 ≤ 1458088946801421 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_2995 c22250R_111_10 (by norm_num)

theorem c22250R_111_8 : rowsJ2 111 112 46 340 ≤ 1458630429090894 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_2994 c22250R_111_9 (by norm_num)

theorem c22250R_111_7 : rowsJ2 111 112 42 340 ≤ 1465657754422258 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_2993 c22250R_111_8 (by norm_num)

theorem c22250R_111_6 : rowsJ2 111 112 39 340 ≤ 1480390428056142 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_2992 c22250R_111_7 (by norm_num)

theorem c22250R_111_5 : rowsJ2 111 112 37 340 ≤ 1497661877555630 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_2991 c22250R_111_6 (by norm_num)

theorem c22250R_111_4 : rowsJ2 111 112 35 340 ≤ 1519847039558558 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_2990 c22250R_111_5 (by norm_num)

theorem c22250R_111_3 : rowsJ2 111 112 33 340 ≤ 1542843282384597 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_2989 c22250R_111_4 (by norm_num)

theorem c22250R_111_2 : rowsJ2 111 112 31 340 ≤ 1556965996868561 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_2988 c22250R_111_3 (by norm_num)

theorem c22250R_111_1 : rowsJ2 111 112 27 340 ≤ 1567390660318961 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_2987 c22250R_111_2 (by norm_num)

theorem c22250R_111_0 : rowsJ2 111 112 0 340 ≤ 1568095720548569 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_2986 c22250R_111_1 (by norm_num)

theorem hr22250R_111 : rows2 111 112 ≤ 1568095720548569 := rows2_le_of_rowsJ2 111 112 c22250R_111_0

theorem c22250R_112_22 : rowsJ2 112 113 97 340 ≤ 1471118456766406 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3032 rows22250R_3033 (by norm_num)

theorem c22250R_112_21 : rowsJ2 112 113 96 340 ≤ 1482175003795701 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3031 c22250R_112_22 (by norm_num)

theorem c22250R_112_20 : rowsJ2 112 113 94 340 ≤ 1500226470903125 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3030 c22250R_112_21 (by norm_num)

theorem c22250R_112_19 : rowsJ2 112 113 92 340 ≤ 1513538365990629 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3029 c22250R_112_20 (by norm_num)

theorem c22250R_112_18 : rowsJ2 112 113 90 340 ≤ 1522896595121566 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3028 c22250R_112_19 (by norm_num)

theorem c22250R_112_17 : rowsJ2 112 113 88 340 ≤ 1529038877474280 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3027 c22250R_112_18 (by norm_num)

theorem c22250R_112_16 : rowsJ2 112 113 85 340 ≤ 1533741147013846 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3026 c22250R_112_17 (by norm_num)

theorem c22250R_112_15 : rowsJ2 112 113 82 340 ≤ 1534956103857781 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3025 c22250R_112_16 (by norm_num)

theorem c22250R_112_14 : rowsJ2 112 113 79 340 ≤ 1534970721862696 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3024 c22250R_112_15 (by norm_num)

theorem c22250R_112_13 : rowsJ2 112 113 76 340 ≤ 1535141729730895 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3023 c22250R_112_14 (by norm_num)

theorem c22250R_112_12 : rowsJ2 112 113 73 340 ≤ 1535156096699821 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3022 c22250R_112_13 (by norm_num)

theorem c22250R_112_11 : rowsJ2 112 113 69 340 ≤ 1535156096699821 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3021 c22250R_112_12 (by norm_num)

theorem c22250R_112_10 : rowsJ2 112 113 64 340 ≤ 1536512536710344 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3020 c22250R_112_11 (by norm_num)

theorem c22250R_112_9 : rowsJ2 112 113 59 340 ≤ 1539331626679387 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3019 c22250R_112_10 (by norm_num)

theorem c22250R_112_8 : rowsJ2 112 113 47 340 ≤ 1539548785590638 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3018 c22250R_112_9 (by norm_num)

theorem c22250R_112_7 : rowsJ2 112 113 42 340 ≤ 1544962422634003 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3017 c22250R_112_8 (by norm_num)

theorem c22250R_112_6 : rowsJ2 112 113 39 340 ≤ 1557358225448197 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3016 c22250R_112_7 (by norm_num)

theorem c22250R_112_5 : rowsJ2 112 113 37 340 ≤ 1572651909596013 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3015 c22250R_112_6 (by norm_num)

theorem c22250R_112_4 : rowsJ2 112 113 35 340 ≤ 1592770029192949 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3014 c22250R_112_5 (by norm_num)

theorem c22250R_112_3 : rowsJ2 112 113 33 340 ≤ 1615515496947690 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3013 c22250R_112_4 (by norm_num)

theorem c22250R_112_2 : rowsJ2 112 113 31 340 ≤ 1630748441496982 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3012 c22250R_112_3 (by norm_num)

theorem c22250R_112_1 : rowsJ2 112 113 27 340 ≤ 1642301670358323 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3011 c22250R_112_2 (by norm_num)

theorem c22250R_112_0 : rowsJ2 112 113 0 340 ≤ 1643245725639608 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3010 c22250R_112_1 (by norm_num)

theorem hr22250R_112 : rows2 112 113 ≤ 1643245725639608 := rows2_le_of_rowsJ2 112 113 c22250R_112_0

theorem c22250R_113_21 : rowsJ2 113 114 96 340 ≤ 1648215727548543 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3055 rows22250R_3056 (by norm_num)

theorem c22250R_113_20 : rowsJ2 113 114 95 340 ≤ 1658452361461490 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3054 c22250R_113_21 (by norm_num)

theorem c22250R_113_19 : rowsJ2 113 114 93 340 ≤ 1675013516050494 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3053 c22250R_113_20 (by norm_num)

theorem c22250R_113_18 : rowsJ2 113 114 91 340 ≤ 1687031515103222 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3052 c22250R_113_19 (by norm_num)

theorem c22250R_113_17 : rowsJ2 113 114 89 340 ≤ 1695289520772438 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3051 c22250R_113_18 (by norm_num)

theorem c22250R_113_16 : rowsJ2 113 114 86 340 ≤ 1702231031182564 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3050 c22250R_113_17 (by norm_num)

theorem c22250R_113_15 : rowsJ2 113 114 83 340 ≤ 1704662901655926 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3049 c22250R_113_16 (by norm_num)

theorem c22250R_113_14 : rowsJ2 113 114 80 340 ≤ 1704858180106480 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3048 c22250R_113_15 (by norm_num)

theorem c22250R_113_13 : rowsJ2 113 114 77 340 ≤ 1704872578146558 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3047 c22250R_113_14 (by norm_num)

theorem c22250R_113_12 : rowsJ2 113 114 74 340 ≤ 1704915412611070 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3046 c22250R_113_13 (by norm_num)

theorem c22250R_113_11 : rowsJ2 113 114 70 340 ≤ 1704915412611070 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3045 c22250R_113_12 (by norm_num)

theorem c22250R_113_10 : rowsJ2 113 114 66 340 ≤ 1705802661268944 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3044 c22250R_113_11 (by norm_num)

theorem c22250R_113_9 : rowsJ2 113 114 62 340 ≤ 1709171464466736 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3043 c22250R_113_10 (by norm_num)

theorem c22250R_113_8 : rowsJ2 113 114 53 340 ≤ 1711409086743105 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3042 c22250R_113_9 (by norm_num)

theorem c22250R_113_7 : rowsJ2 113 114 44 340 ≤ 1712524541069354 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3041 c22250R_113_8 (by norm_num)

theorem c22250R_113_6 : rowsJ2 113 114 40 340 ≤ 1721027076766008 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3040 c22250R_113_7 (by norm_num)

theorem c22250R_113_5 : rowsJ2 113 114 37 340 ≤ 1739067530820390 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3039 c22250R_113_6 (by norm_num)

theorem c22250R_113_4 : rowsJ2 113 114 35 340 ≤ 1757153163739989 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3038 c22250R_113_5 (by norm_num)

theorem c22250R_113_3 : rowsJ2 113 114 33 340 ≤ 1779605339407842 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3037 c22250R_113_4 (by norm_num)

theorem c22250R_113_2 : rowsJ2 113 114 31 340 ≤ 1796075694898111 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3036 c22250R_113_3 (by norm_num)

theorem c22250R_113_1 : rowsJ2 113 114 27 340 ≤ 1808998911884807 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3035 c22250R_113_2 (by norm_num)

theorem c22250R_113_0 : rowsJ2 113 114 0 340 ≤ 1810059712673975 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3034 c22250R_113_1 (by norm_num)

theorem hr22250R_113 : rows2 113 114 ≤ 1810059712673975 := rows2_le_of_rowsJ2 113 114 c22250R_113_0

theorem c22250R_114_21 : rowsJ2 114 115 96 340 ≤ 1594487387344226 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3078 rows22250R_3079 (by norm_num)

theorem c22250R_114_20 : rowsJ2 114 115 94 340 ≤ 1614719228625620 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3077 c22250R_114_21 (by norm_num)

theorem c22250R_114_19 : rowsJ2 114 115 92 340 ≤ 1629771720080624 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3076 c22250R_114_20 (by norm_num)

theorem c22250R_114_18 : rowsJ2 114 115 90 340 ≤ 1640479256819106 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3075 c22250R_114_19 (by norm_num)

theorem c22250R_114_17 : rowsJ2 114 115 87 340 ≤ 1650094785733821 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3074 c22250R_114_18 (by norm_num)

theorem c22250R_114_16 : rowsJ2 114 115 84 340 ≤ 1654111643390437 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3073 c22250R_114_17 (by norm_num)

theorem c22250R_114_15 : rowsJ2 114 115 81 340 ≤ 1654811268679547 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3072 c22250R_114_16 (by norm_num)

theorem c22250R_114_14 : rowsJ2 114 115 78 340 ≤ 1654811268679547 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3071 c22250R_114_15 (by norm_num)

theorem c22250R_114_13 : rowsJ2 114 115 75 340 ≤ 1654825457212437 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3070 c22250R_114_14 (by norm_num)

theorem c22250R_114_12 : rowsJ2 114 115 72 340 ≤ 1654825457212437 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3069 c22250R_114_13 (by norm_num)

theorem c22250R_114_11 : rowsJ2 114 115 68 340 ≤ 1655180190676756 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3068 c22250R_114_12 (by norm_num)

theorem c22250R_114_10 : rowsJ2 114 115 65 340 ≤ 1657709464613770 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3067 c22250R_114_11 (by norm_num)

theorem c22250R_114_9 : rowsJ2 114 115 62 340 ≤ 1660978968462498 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3066 c22250R_114_10 (by norm_num)

theorem c22250R_114_8 : rowsJ2 114 115 52 340 ≤ 1663792046149931 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3065 c22250R_114_9 (by norm_num)

theorem c22250R_114_7 : rowsJ2 114 115 43 340 ≤ 1664912818295378 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3064 c22250R_114_8 (by norm_num)

theorem c22250R_114_6 : rowsJ2 114 115 39 340 ≤ 1674170696969282 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3063 c22250R_114_7 (by norm_num)

theorem c22250R_114_5 : rowsJ2 114 115 36 340 ≤ 1693299407717600 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3062 c22250R_114_6 (by norm_num)

theorem c22250R_114_4 : rowsJ2 114 115 34 340 ≤ 1711493264400971 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3061 c22250R_114_5 (by norm_num)

theorem c22250R_114_3 : rowsJ2 114 115 32 340 ≤ 1732308614540832 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3060 c22250R_114_4 (by norm_num)

theorem c22250R_114_2 : rowsJ2 114 115 30 340 ≤ 1745949855587954 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3059 c22250R_114_3 (by norm_num)

theorem c22250R_114_1 : rowsJ2 114 115 27 340 ≤ 1754590082982924 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3058 c22250R_114_2 (by norm_num)

theorem c22250R_114_0 : rowsJ2 114 115 0 340 ≤ 1755767895200539 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3057 c22250R_114_1 (by norm_num)

theorem hr22250R_114 : rows2 114 115 ≤ 1755767895200539 := rows2_le_of_rowsJ2 114 115 c22250R_114_0

theorem c22250R_115_20 : rowsJ2 115 116 94 340 ≤ 1594874343979563 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3100 rows22250R_3101 (by norm_num)

theorem c22250R_115_19 : rowsJ2 115 116 92 340 ≤ 1610867797521232 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3099 c22250R_115_20 (by norm_num)

theorem c22250R_115_18 : rowsJ2 115 116 90 340 ≤ 1622309248459055 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3098 c22250R_115_19 (by norm_num)

theorem c22250R_115_17 : rowsJ2 115 116 87 340 ≤ 1632674290764498 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3097 c22250R_115_18 (by norm_num)

theorem c22250R_115_16 : rowsJ2 115 116 84 340 ≤ 1637119128989492 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3096 c22250R_115_17 (by norm_num)

theorem c22250R_115_15 : rowsJ2 115 116 81 340 ≤ 1637930636099682 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3095 c22250R_115_16 (by norm_num)

theorem c22250R_115_14 : rowsJ2 115 116 78 340 ≤ 1637930636099682 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3094 c22250R_115_15 (by norm_num)

theorem c22250R_115_13 : rowsJ2 115 116 75 340 ≤ 1637930636099682 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3093 c22250R_115_14 (by norm_num)

theorem c22250R_115_12 : rowsJ2 115 116 72 340 ≤ 1637930636099682 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3092 c22250R_115_13 (by norm_num)

theorem c22250R_115_11 : rowsJ2 115 116 68 340 ≤ 1639081068366880 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3091 c22250R_115_12 (by norm_num)

theorem c22250R_115_10 : rowsJ2 115 116 65 340 ≤ 1642591166901648 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3090 c22250R_115_11 (by norm_num)

theorem c22250R_115_9 : rowsJ2 115 116 62 340 ≤ 1646594447716133 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3089 c22250R_115_10 (by norm_num)

theorem c22250R_115_8 : rowsJ2 115 116 58 340 ≤ 1649790434751119 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3088 c22250R_115_9 (by norm_num)

theorem c22250R_115_7 : rowsJ2 115 116 44 340 ≤ 1650298058631495 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3087 c22250R_115_8 (by norm_num)

theorem c22250R_115_6 : rowsJ2 115 116 39 340 ≤ 1657569393021210 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3086 c22250R_115_7 (by norm_num)

theorem c22250R_115_5 : rowsJ2 115 116 36 340 ≤ 1673980272674864 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3085 c22250R_115_6 (by norm_num)

theorem c22250R_115_4 : rowsJ2 115 116 34 340 ≤ 1690168313105481 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3084 c22250R_115_5 (by norm_num)

theorem c22250R_115_3 : rowsJ2 115 116 32 340 ≤ 1710659040586716 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3083 c22250R_115_4 (by norm_num)

theorem c22250R_115_2 : rowsJ2 115 116 30 340 ≤ 1725447664495886 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3082 c22250R_115_3 (by norm_num)

theorem c22250R_115_1 : rowsJ2 115 116 27 340 ≤ 1735378359074363 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3081 c22250R_115_2 (by norm_num)

theorem c22250R_115_0 : rowsJ2 115 116 0 340 ≤ 1736668444940069 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3080 c22250R_115_1 (by norm_num)

theorem hr22250R_115 : rows2 115 116 ≤ 1736668444940069 := rows2_le_of_rowsJ2 115 116 c22250R_115_0

theorem c22250R_116_20 : rowsJ2 116 117 94 340 ≤ 1483914976834643 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3122 rows22250R_3123 (by norm_num)

theorem c22250R_116_19 : rowsJ2 116 117 92 340 ≤ 1500839487433216 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3121 c22250R_116_20 (by norm_num)

theorem c22250R_116_18 : rowsJ2 116 117 90 340 ≤ 1512995868438406 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3120 c22250R_116_19 (by norm_num)

theorem c22250R_116_17 : rowsJ2 116 117 87 340 ≤ 1524093512131647 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3119 c22250R_116_18 (by norm_num)

theorem c22250R_116_16 : rowsJ2 116 117 84 340 ≤ 1528882850626197 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3118 c22250R_116_17 (by norm_num)

theorem c22250R_116_15 : rowsJ2 116 117 80 340 ≤ 1529761201106148 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3117 c22250R_116_16 (by norm_num)

theorem c22250R_116_14 : rowsJ2 116 117 77 340 ≤ 1529761201106148 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3116 c22250R_116_15 (by norm_num)

theorem c22250R_116_13 : rowsJ2 116 117 74 340 ≤ 1529761201106148 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3115 c22250R_116_14 (by norm_num)

theorem c22250R_116_12 : rowsJ2 116 117 71 340 ≤ 1529761201106148 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3114 c22250R_116_13 (by norm_num)

theorem c22250R_116_11 : rowsJ2 116 117 68 340 ≤ 1532160176710216 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3113 c22250R_116_12 (by norm_num)

theorem c22250R_116_10 : rowsJ2 116 117 66 340 ≤ 1535041574607889 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3112 c22250R_116_11 (by norm_num)

theorem c22250R_116_9 : rowsJ2 116 117 64 340 ≤ 1538299240987661 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3111 c22250R_116_10 (by norm_num)

theorem c22250R_116_8 : rowsJ2 116 117 61 340 ≤ 1542740556066847 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3110 c22250R_116_9 (by norm_num)

theorem c22250R_116_7 : rowsJ2 116 117 50 340 ≤ 1545776121326157 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3109 c22250R_116_8 (by norm_num)

theorem c22250R_116_6 : rowsJ2 116 117 41 340 ≤ 1547025445650242 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3108 c22250R_116_7 (by norm_num)

theorem c22250R_116_5 : rowsJ2 116 117 37 340 ≤ 1559209629224874 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3107 c22250R_116_6 (by norm_num)

theorem c22250R_116_4 : rowsJ2 116 117 34 340 ≤ 1579068014656988 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3106 c22250R_116_5 (by norm_num)

theorem c22250R_116_3 : rowsJ2 116 117 32 340 ≤ 1597490776753696 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3105 c22250R_116_4 (by norm_num)

theorem c22250R_116_2 : rowsJ2 116 117 30 340 ≤ 1613559174683485 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3104 c22250R_116_3 (by norm_num)

theorem c22250R_116_1 : rowsJ2 116 117 27 340 ≤ 1624788705240315 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3103 c22250R_116_2 (by norm_num)

theorem c22250R_116_0 : rowsJ2 116 117 0 340 ≤ 1626313613313447 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3102 c22250R_116_1 (by norm_num)

theorem hr22250R_116 : rows2 116 117 ≤ 1626313613313447 := rows2_le_of_rowsJ2 116 117 c22250R_116_0

theorem c22250R_117_21 : rowsJ2 117 118 94 340 ≤ 1464605416871724 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3145 rows22250R_3146 (by norm_num)

theorem c22250R_117_20 : rowsJ2 117 118 92 340 ≤ 1482542403302700 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3144 c22250R_117_21 (by norm_num)

theorem c22250R_117_19 : rowsJ2 117 118 90 340 ≤ 1495486933001110 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3143 c22250R_117_20 (by norm_num)

theorem c22250R_117_18 : rowsJ2 117 118 88 340 ≤ 1504292552291100 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3142 c22250R_117_19 (by norm_num)

theorem c22250R_117_17 : rowsJ2 117 118 85 340 ≤ 1511467548019817 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3141 c22250R_117_18 (by norm_num)

theorem c22250R_117_16 : rowsJ2 117 118 82 340 ≤ 1513630560434840 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3140 c22250R_117_17 (by norm_num)

theorem c22250R_117_15 : rowsJ2 117 118 78 340 ≤ 1513630560434840 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3139 c22250R_117_16 (by norm_num)

theorem c22250R_117_14 : rowsJ2 117 118 75 340 ≤ 1513630560434840 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3138 c22250R_117_15 (by norm_num)

theorem c22250R_117_13 : rowsJ2 117 118 72 340 ≤ 1513630560434840 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3137 c22250R_117_14 (by norm_num)

theorem c22250R_117_12 : rowsJ2 117 118 69 340 ≤ 1516331230809563 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3136 c22250R_117_13 (by norm_num)

theorem c22250R_117_11 : rowsJ2 117 118 67 340 ≤ 1519623574965919 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3135 c22250R_117_12 (by norm_num)

theorem c22250R_117_10 : rowsJ2 117 118 65 340 ≤ 1523451308815972 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3134 c22250R_117_11 (by norm_num)

theorem c22250R_117_9 : rowsJ2 117 118 63 340 ≤ 1527277139723483 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3133 c22250R_117_10 (by norm_num)

theorem c22250R_117_8 : rowsJ2 117 118 61 340 ≤ 1530582958280471 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3132 c22250R_117_9 (by norm_num)

theorem c22250R_117_7 : rowsJ2 117 118 56 340 ≤ 1534269340017364 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3131 c22250R_117_8 (by norm_num)

theorem c22250R_117_6 : rowsJ2 117 118 42 340 ≤ 1534530758252476 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3130 c22250R_117_7 (by norm_num)

theorem c22250R_117_5 : rowsJ2 117 118 37 340 ≤ 1544848488953403 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3129 c22250R_117_6 (by norm_num)

theorem c22250R_117_4 : rowsJ2 117 118 34 340 ≤ 1561962153025747 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3128 c22250R_117_5 (by norm_num)

theorem c22250R_117_3 : rowsJ2 117 118 32 340 ≤ 1578355109057427 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3127 c22250R_117_4 (by norm_num)

theorem c22250R_117_2 : rowsJ2 117 118 30 340 ≤ 1595709785480997 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3126 c22250R_117_3 (by norm_num)

theorem c22250R_117_1 : rowsJ2 117 118 27 340 ≤ 1608242368973962 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3125 c22250R_117_2 (by norm_num)

theorem c22250R_117_0 : rowsJ2 117 118 0 340 ≤ 1610249125394205 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3124 c22250R_117_1 (by norm_num)

theorem hr22250R_117 : rows2 117 118 ≤ 1610249125394205 := rows2_le_of_rowsJ2 117 118 c22250R_117_0

theorem c22250R_118_21 : rowsJ2 118 119 94 340 ≤ 1355783499113125 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3168 rows22250R_3169 (by norm_num)

theorem c22250R_118_20 : rowsJ2 118 119 92 340 ≤ 1374725691350356 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3167 c22250R_118_21 (by norm_num)

theorem c22250R_118_19 : rowsJ2 118 119 90 340 ≤ 1388441021479864 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3166 c22250R_118_20 (by norm_num)

theorem c22250R_118_18 : rowsJ2 118 119 88 340 ≤ 1397809987141034 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3165 c22250R_118_19 (by norm_num)

theorem c22250R_118_17 : rowsJ2 118 119 85 340 ≤ 1405505277213782 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3164 c22250R_118_18 (by norm_num)

theorem c22250R_118_16 : rowsJ2 118 119 82 340 ≤ 1407817018696926 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3163 c22250R_118_17 (by norm_num)

theorem c22250R_118_15 : rowsJ2 118 119 78 340 ≤ 1407817018696926 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3162 c22250R_118_16 (by norm_num)

theorem c22250R_118_14 : rowsJ2 118 119 75 340 ≤ 1407817018696926 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3161 c22250R_118_15 (by norm_num)

theorem c22250R_118_13 : rowsJ2 118 119 72 340 ≤ 1408358483107063 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3160 c22250R_118_14 (by norm_num)

theorem c22250R_118_12 : rowsJ2 118 119 70 340 ≤ 1410775746868670 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3159 c22250R_118_13 (by norm_num)

theorem c22250R_118_11 : rowsJ2 118 119 68 340 ≤ 1414462407927829 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3158 c22250R_118_12 (by norm_num)

theorem c22250R_118_10 : rowsJ2 118 119 66 340 ≤ 1418845582713360 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3157 c22250R_118_11 (by norm_num)

theorem c22250R_118_9 : rowsJ2 118 119 64 340 ≤ 1423379385640582 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3156 c22250R_118_10 (by norm_num)

theorem c22250R_118_8 : rowsJ2 118 119 62 340 ≤ 1427539272742517 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3155 c22250R_118_9 (by norm_num)

theorem c22250R_118_7 : rowsJ2 118 119 60 340 ≤ 1430817056384376 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3154 c22250R_118_8 (by norm_num)

theorem c22250R_118_6 : rowsJ2 118 119 48 340 ≤ 1433959242189021 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3153 c22250R_118_7 (by norm_num)

theorem c22250R_118_5 : rowsJ2 118 119 39 340 ≤ 1436318302918264 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3152 c22250R_118_6 (by norm_num)

theorem c22250R_118_4 : rowsJ2 118 119 35 340 ≤ 1451050699263242 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3151 c22250R_118_5 (by norm_num)

theorem c22250R_118_3 : rowsJ2 118 119 32 340 ≤ 1471159337593598 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3150 c22250R_118_4 (by norm_num)

theorem c22250R_118_2 : rowsJ2 118 119 30 340 ≤ 1488164408704072 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3149 c22250R_118_3 (by norm_num)

theorem c22250R_118_1 : rowsJ2 118 119 27 340 ≤ 1501882163236014 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3148 c22250R_118_2 (by norm_num)

theorem c22250R_118_0 : rowsJ2 118 119 0 340 ≤ 1504624083161211 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3147 c22250R_118_1 (by norm_num)

theorem hr22250R_118 : rows2 118 119 ≤ 1504624083161211 := rows2_le_of_rowsJ2 118 119 c22250R_118_0

theorem c22250R_119_20 : rowsJ2 119 120 93 340 ≤ 1347731388135564 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3190 rows22250R_3191 (by norm_num)

theorem c22250R_119_19 : rowsJ2 119 120 91 340 ≤ 1364912523660058 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3189 c22250R_119_20 (by norm_num)

theorem c22250R_119_18 : rowsJ2 119 120 89 340 ≤ 1377085924231748 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3188 c22250R_119_19 (by norm_num)

theorem c22250R_119_17 : rowsJ2 119 120 86 340 ≤ 1387865664733876 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3187 c22250R_119_18 (by norm_num)

theorem c22250R_119_16 : rowsJ2 119 120 83 340 ≤ 1392050444151652 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3186 c22250R_119_17 (by norm_num)

theorem c22250R_119_15 : rowsJ2 119 120 79 340 ≤ 1392428439381796 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3185 c22250R_119_16 (by norm_num)

theorem c22250R_119_14 : rowsJ2 119 120 75 340 ≤ 1392428439381796 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3184 c22250R_119_15 (by norm_num)

theorem c22250R_119_13 : rowsJ2 119 120 72 340 ≤ 1394113718733346 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3183 c22250R_119_14 (by norm_num)

theorem c22250R_119_12 : rowsJ2 119 120 70 340 ≤ 1397583744696060 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3182 c22250R_119_13 (by norm_num)

theorem c22250R_119_11 : rowsJ2 119 120 68 340 ≤ 1402203026799668 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3181 c22250R_119_12 (by norm_num)

theorem c22250R_119_10 : rowsJ2 119 120 66 340 ≤ 1407402155497448 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3180 c22250R_119_11 (by norm_num)

theorem c22250R_119_9 : rowsJ2 119 120 64 340 ≤ 1412638256350222 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3179 c22250R_119_10 (by norm_num)

theorem c22250R_119_8 : rowsJ2 119 120 62 340 ≤ 1417389370207173 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3178 c22250R_119_9 (by norm_num)

theorem c22250R_119_7 : rowsJ2 119 120 59 340 ≤ 1422505979587977 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3177 c22250R_119_8 (by norm_num)

theorem c22250R_119_6 : rowsJ2 119 120 47 340 ≤ 1425111057533418 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3176 c22250R_119_7 (by norm_num)

theorem c22250R_119_5 : rowsJ2 119 120 38 340 ≤ 1428735490308807 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3175 c22250R_119_6 (by norm_num)

theorem c22250R_119_4 : rowsJ2 119 120 34 340 ≤ 1444074060049326 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3174 c22250R_119_5 (by norm_num)

theorem c22250R_119_3 : rowsJ2 119 120 31 340 ≤ 1464314838930098 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3173 c22250R_119_4 (by norm_num)

theorem c22250R_119_2 : rowsJ2 119 120 29 340 ≤ 1479826296197336 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3172 c22250R_119_3 (by norm_num)

theorem c22250R_119_1 : rowsJ2 119 120 26 340 ≤ 1490450926513922 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3171 c22250R_119_2 (by norm_num)

theorem c22250R_119_0 : rowsJ2 119 120 0 340 ≤ 1491782820013426 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3170 c22250R_119_1 (by norm_num)

theorem hr22250R_119 : rows2 119 120 ≤ 1491782820013426 := rows2_le_of_rowsJ2 119 120 c22250R_119_0

theorem c22250R_120_22 : rowsJ2 120 121 92 340 ≤ 1251277929204325 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3214 rows22250R_3215 (by norm_num)

theorem c22250R_120_21 : rowsJ2 120 121 90 340 ≤ 1266674267739939 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3213 c22250R_120_22 (by norm_num)

theorem c22250R_120_20 : rowsJ2 120 121 88 340 ≤ 1277284183778383 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3212 c22250R_120_21 (by norm_num)

theorem c22250R_120_19 : rowsJ2 120 121 85 340 ≤ 1286126450387659 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3211 c22250R_120_20 (by norm_num)

theorem c22250R_120_18 : rowsJ2 120 121 81 340 ≤ 1288856858768947 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3210 c22250R_120_19 (by norm_num)

theorem c22250R_120_17 : rowsJ2 120 121 77 340 ≤ 1288856858768947 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3209 c22250R_120_18 (by norm_num)

theorem c22250R_120_16 : rowsJ2 120 121 74 340 ≤ 1289367437609038 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3208 c22250R_120_17 (by norm_num)

theorem c22250R_120_15 : rowsJ2 120 121 72 340 ≤ 1292143200680290 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3207 c22250R_120_16 (by norm_num)

theorem c22250R_120_14 : rowsJ2 120 121 70 340 ≤ 1296677199211155 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3206 c22250R_120_15 (by norm_num)

theorem c22250R_120_13 : rowsJ2 120 121 69 340 ≤ 1299368700779067 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3205 c22250R_120_14 (by norm_num)

theorem c22250R_120_12 : rowsJ2 120 121 68 340 ≤ 1302238969661621 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3204 c22250R_120_13 (by norm_num)

theorem c22250R_120_11 : rowsJ2 120 121 67 340 ≤ 1305230339772592 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3203 c22250R_120_12 (by norm_num)

theorem c22250R_120_10 : rowsJ2 120 121 66 340 ≤ 1308262609653974 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3202 c22250R_120_11 (by norm_num)

theorem c22250R_120_9 : rowsJ2 120 121 65 340 ≤ 1311281040591655 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3201 c22250R_120_10 (by norm_num)

theorem c22250R_120_8 : rowsJ2 120 121 63 340 ≤ 1316991862003553 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3200 c22250R_120_9 (by norm_num)

theorem c22250R_120_7 : rowsJ2 120 121 61 340 ≤ 1321851811871386 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3199 c22250R_120_8 (by norm_num)

theorem c22250R_120_6 : rowsJ2 120 121 58 340 ≤ 1326550509421721 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3198 c22250R_120_7 (by norm_num)

theorem c22250R_120_5 : rowsJ2 120 121 43 340 ≤ 1328592277048706 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3197 c22250R_120_6 (by norm_num)

theorem c22250R_120_4 : rowsJ2 120 121 36 340 ≤ 1336317522726912 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3196 c22250R_120_5 (by norm_num)

theorem c22250R_120_3 : rowsJ2 120 121 32 340 ≤ 1354615348617332 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3195 c22250R_120_4 (by norm_num)

theorem c22250R_120_2 : rowsJ2 120 121 29 340 ≤ 1376501022402474 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3194 c22250R_120_3 (by norm_num)

theorem c22250R_120_1 : rowsJ2 120 121 26 340 ≤ 1388216451732855 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3193 c22250R_120_2 (by norm_num)

theorem c22250R_120_0 : rowsJ2 120 121 0 340 ≤ 1390175272303091 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3192 c22250R_120_1 (by norm_num)

theorem hr22250R_120 : rows2 120 121 ≤ 1390175272303091 := rows2_le_of_rowsJ2 120 121 c22250R_120_0

theorem c22250R_121_23 : rowsJ2 121 122 91 340 ≤ 1242965778624650 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3239 rows22250R_3240 (by norm_num)

theorem c22250R_121_22 : rowsJ2 121 122 88 340 ≤ 1261733622318796 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3238 c22250R_121_23 (by norm_num)

theorem c22250R_121_21 : rowsJ2 121 122 85 340 ≤ 1271205901317140 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3237 c22250R_121_22 (by norm_num)

theorem c22250R_121_20 : rowsJ2 121 122 81 340 ≤ 1274209729926004 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3236 c22250R_121_21 (by norm_num)

theorem c22250R_121_19 : rowsJ2 121 122 77 340 ≤ 1274209729926004 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3235 c22250R_121_20 (by norm_num)

theorem c22250R_121_18 : rowsJ2 121 122 74 340 ≤ 1275674301221847 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3234 c22250R_121_19 (by norm_num)

theorem c22250R_121_17 : rowsJ2 121 122 72 340 ≤ 1279408787667387 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3233 c22250R_121_18 (by norm_num)

theorem c22250R_121_16 : rowsJ2 121 122 71 340 ≤ 1282093620547347 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3232 c22250R_121_17 (by norm_num)

theorem c22250R_121_15 : rowsJ2 121 122 70 340 ≤ 1285071411381950 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3231 c22250R_121_16 (by norm_num)

theorem c22250R_121_14 : rowsJ2 121 122 69 340 ≤ 1288281224941914 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3230 c22250R_121_15 (by norm_num)

theorem c22250R_121_13 : rowsJ2 121 122 68 340 ≤ 1291639814065369 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3229 c22250R_121_14 (by norm_num)

theorem c22250R_121_12 : rowsJ2 121 122 67 340 ≤ 1295089871972238 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3228 c22250R_121_13 (by norm_num)

theorem c22250R_121_11 : rowsJ2 121 122 66 340 ≤ 1298551670775501 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3227 c22250R_121_12 (by norm_num)

theorem c22250R_121_10 : rowsJ2 121 122 65 340 ≤ 1301970774102858 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3226 c22250R_121_11 (by norm_num)

theorem c22250R_121_9 : rowsJ2 121 122 64 340 ≤ 1305270250052883 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3225 c22250R_121_10 (by norm_num)

theorem c22250R_121_8 : rowsJ2 121 122 63 340 ≤ 1308397872423753 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3224 c22250R_121_9 (by norm_num)

theorem c22250R_121_7 : rowsJ2 121 122 61 340 ≤ 1313862637662221 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3223 c22250R_121_8 (by norm_num)

theorem c22250R_121_6 : rowsJ2 121 122 58 340 ≤ 1319263459833438 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3222 c22250R_121_7 (by norm_num)

theorem c22250R_121_5 : rowsJ2 121 122 45 340 ≤ 1321941462035093 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3221 c22250R_121_6 (by norm_num)

theorem c22250R_121_4 : rowsJ2 121 122 36 340 ≤ 1327951960028656 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3220 c22250R_121_5 (by norm_num)

theorem c22250R_121_3 : rowsJ2 121 122 32 340 ≤ 1343485436115289 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3219 c22250R_121_4 (by norm_num)

theorem c22250R_121_2 : rowsJ2 121 122 29 340 ≤ 1364005298526746 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3218 c22250R_121_3 (by norm_num)

theorem c22250R_121_1 : rowsJ2 121 122 26 340 ≤ 1376814979162910 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3217 c22250R_121_2 (by norm_num)

theorem c22250R_121_0 : rowsJ2 121 122 0 340 ≤ 1379531403483104 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3216 c22250R_121_1 (by norm_num)

theorem hr22250R_121 : rows2 121 122 ≤ 1379531403483104 := rows2_le_of_rowsJ2 121 122 c22250R_121_0

theorem c22250R_122_24 : rowsJ2 122 123 90 340 ≤ 1147625687688103 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3265 rows22250R_3266 (by norm_num)

theorem c22250R_122_23 : rowsJ2 122 123 87 340 ≤ 1163875074462042 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3264 c22250R_122_24 (by norm_num)

theorem c22250R_122_22 : rowsJ2 122 123 84 340 ≤ 1171337274233854 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3263 c22250R_122_23 (by norm_num)

theorem c22250R_122_21 : rowsJ2 122 123 80 340 ≤ 1172831773817626 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3262 c22250R_122_22 (by norm_num)

theorem c22250R_122_20 : rowsJ2 122 123 76 340 ≤ 1173249610940245 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3261 c22250R_122_21 (by norm_num)

theorem c22250R_122_19 : rowsJ2 122 123 74 340 ≤ 1175552610964052 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3260 c22250R_122_20 (by norm_num)

theorem c22250R_122_18 : rowsJ2 122 123 72 340 ≤ 1180129565446431 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3259 c22250R_122_19 (by norm_num)

theorem c22250R_122_17 : rowsJ2 122 123 71 340 ≤ 1183400827117307 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3258 c22250R_122_18 (by norm_num)

theorem c22250R_122_16 : rowsJ2 122 123 70 340 ≤ 1186933717354547 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3257 c22250R_122_17 (by norm_num)

theorem c22250R_122_15 : rowsJ2 122 123 69 340 ≤ 1190667729529744 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3256 c22250R_122_16 (by norm_num)

theorem c22250R_122_14 : rowsJ2 122 123 68 340 ≤ 1194520156056010 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3255 c22250R_122_15 (by norm_num)

theorem c22250R_122_13 : rowsJ2 122 123 67 340 ≤ 1198434055522761 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3254 c22250R_122_14 (by norm_num)

theorem c22250R_122_12 : rowsJ2 122 123 66 340 ≤ 1202330177547998 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3253 c22250R_122_13 (by norm_num)

theorem c22250R_122_11 : rowsJ2 122 123 65 340 ≤ 1206154393314725 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3252 c22250R_122_12 (by norm_num)

theorem c22250R_122_10 : rowsJ2 122 123 64 340 ≤ 1209830191374250 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3251 c22250R_122_11 (by norm_num)

theorem c22250R_122_9 : rowsJ2 122 123 63 340 ≤ 1213305599722252 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3250 c22250R_122_10 (by norm_num)

theorem c22250R_122_8 : rowsJ2 122 123 62 340 ≤ 1216506213158747 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3249 c22250R_122_9 (by norm_num)

theorem c22250R_122_7 : rowsJ2 122 123 61 340 ≤ 1219381635606287 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3248 c22250R_122_8 (by norm_num)

theorem c22250R_122_6 : rowsJ2 122 123 59 340 ≤ 1223888967021726 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3247 c22250R_122_7 (by norm_num)

theorem c22250R_122_5 : rowsJ2 122 123 54 340 ≤ 1228563115092103 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3246 c22250R_122_6 (by norm_num)

theorem c22250R_122_4 : rowsJ2 122 123 37 340 ≤ 1231255823146323 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3245 c22250R_122_5 (by norm_num)

theorem c22250R_122_3 : rowsJ2 122 123 32 340 ≤ 1246189344178500 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3244 c22250R_122_4 (by norm_num)

theorem c22250R_122_2 : rowsJ2 122 123 29 340 ≤ 1263876340966757 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3243 c22250R_122_3 (by norm_num)

theorem c22250R_122_1 : rowsJ2 122 123 26 340 ≤ 1277916681474774 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3242 c22250R_122_2 (by norm_num)

theorem c22250R_122_0 : rowsJ2 122 123 0 340 ≤ 1281398487887098 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3241 c22250R_122_1 (by norm_num)

theorem hr22250R_122 : rows2 122 123 ≤ 1281398487887098 := rows2_le_of_rowsJ2 122 123 c22250R_122_0

theorem c22250R_123_23 : rowsJ2 123 124 89 340 ≤ 1138984934458499 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3290 rows22250R_3291 (by norm_num)

theorem c22250R_123_22 : rowsJ2 123 124 86 340 ≤ 1152832531162458 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3289 c22250R_123_23 (by norm_num)

theorem c22250R_123_21 : rowsJ2 123 124 82 340 ≤ 1158933429473578 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3288 c22250R_123_22 (by norm_num)

theorem c22250R_123_20 : rowsJ2 123 124 78 340 ≤ 1158933429473578 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3287 c22250R_123_21 (by norm_num)

theorem c22250R_123_19 : rowsJ2 123 124 75 340 ≤ 1161405954384073 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3286 c22250R_123_20 (by norm_num)

theorem c22250R_123_18 : rowsJ2 123 124 73 340 ≤ 1165574087585170 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3285 c22250R_123_19 (by norm_num)

theorem c22250R_123_17 : rowsJ2 123 124 72 340 ≤ 1168559459380081 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3284 c22250R_123_18 (by norm_num)

theorem c22250R_123_16 : rowsJ2 123 124 71 340 ≤ 1172222491333336 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3283 c22250R_123_17 (by norm_num)

theorem c22250R_123_15 : rowsJ2 123 124 70 340 ≤ 1176344098801568 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3282 c22250R_123_16 (by norm_num)

theorem c22250R_123_14 : rowsJ2 123 124 69 340 ≤ 1180635764384076 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3281 c22250R_123_15 (by norm_num)

theorem c22250R_123_13 : rowsJ2 123 124 68 340 ≤ 1185015329643903 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3280 c22250R_123_14 (by norm_num)

theorem c22250R_123_12 : rowsJ2 123 124 67 340 ≤ 1189426229412087 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3279 c22250R_123_13 (by norm_num)

theorem c22250R_123_11 : rowsJ2 123 124 66 340 ≤ 1193789699653263 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3278 c22250R_123_12 (by norm_num)

theorem c22250R_123_10 : rowsJ2 123 124 65 340 ≤ 1198051929272476 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3277 c22250R_123_11 (by norm_num)

theorem c22250R_123_9 : rowsJ2 123 124 64 340 ≤ 1202136835473378 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3276 c22250R_123_10 (by norm_num)

theorem c22250R_123_8 : rowsJ2 123 124 63 340 ≤ 1205992709997672 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3275 c22250R_123_9 (by norm_num)

theorem c22250R_123_7 : rowsJ2 123 124 62 340 ≤ 1209545522818813 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3274 c22250R_123_8 (by norm_num)

theorem c22250R_123_6 : rowsJ2 123 124 60 340 ≤ 1215518875113552 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3273 c22250R_123_7 (by norm_num)

theorem c22250R_123_5 : rowsJ2 123 124 57 340 ≤ 1221094850233291 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3272 c22250R_123_6 (by norm_num)

theorem c22250R_123_4 : rowsJ2 123 124 40 340 ≤ 1223849298829654 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3271 c22250R_123_5 (by norm_num)

theorem c22250R_123_3 : rowsJ2 123 124 33 340 ≤ 1234251125396145 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3270 c22250R_123_4 (by norm_num)

theorem c22250R_123_2 : rowsJ2 123 124 29 340 ≤ 1252923658540419 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3269 c22250R_123_3 (by norm_num)

theorem c22250R_123_1 : rowsJ2 123 124 26 340 ≤ 1268194053489900 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3268 c22250R_123_2 (by norm_num)

theorem c22250R_123_0 : rowsJ2 123 124 0 340 ≤ 1272445395599610 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3267 c22250R_123_1 (by norm_num)

theorem hr22250R_123 : rows2 123 124 ≤ 1272445395599610 := rows2_le_of_rowsJ2 123 124 c22250R_123_0

theorem c22250R_124_24 : rowsJ2 124 125 88 340 ≤ 1044568858521516 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3316 rows22250R_3317 (by norm_num)

theorem c22250R_124_23 : rowsJ2 124 125 85 340 ≤ 1055978518740043 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3315 c22250R_124_24 (by norm_num)

theorem c22250R_124_22 : rowsJ2 124 125 81 340 ≤ 1059643019715860 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3314 c22250R_124_23 (by norm_num)

theorem c22250R_124_21 : rowsJ2 124 125 77 340 ≤ 1060686748252277 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3313 c22250R_124_22 (by norm_num)

theorem c22250R_124_20 : rowsJ2 124 125 75 340 ≤ 1063434846572956 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3312 c22250R_124_21 (by norm_num)

theorem c22250R_124_19 : rowsJ2 124 125 73 340 ≤ 1068267514361141 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3311 c22250R_124_20 (by norm_num)

theorem c22250R_124_18 : rowsJ2 124 125 72 340 ≤ 1071586548723518 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3310 c22250R_124_19 (by norm_num)

theorem c22250R_124_17 : rowsJ2 124 125 71 340 ≤ 1075584181978537 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3309 c22250R_124_18 (by norm_num)

theorem c22250R_124_16 : rowsJ2 124 125 70 340 ≤ 1080301679994339 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3308 c22250R_124_17 (by norm_num)

theorem c22250R_124_15 : rowsJ2 124 125 69 340 ≤ 1085157755738220 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3307 c22250R_124_16 (by norm_num)

theorem c22250R_124_14 : rowsJ2 124 125 68 340 ≤ 1090070806255792 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3306 c22250R_124_15 (by norm_num)

theorem c22250R_124_13 : rowsJ2 124 125 67 340 ≤ 1094984650066928 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3305 c22250R_124_14 (by norm_num)

theorem c22250R_124_12 : rowsJ2 124 125 66 340 ≤ 1099821014775141 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3304 c22250R_124_13 (by norm_num)

theorem c22250R_124_11 : rowsJ2 124 125 65 340 ≤ 1104526413440820 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3303 c22250R_124_12 (by norm_num)

theorem c22250R_124_10 : rowsJ2 124 125 64 340 ≤ 1109025196258969 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3302 c22250R_124_11 (by norm_num)

theorem c22250R_124_9 : rowsJ2 124 125 63 340 ≤ 1113265924218139 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3301 c22250R_124_10 (by norm_num)

theorem c22250R_124_8 : rowsJ2 124 125 62 340 ≤ 1117174945924579 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3300 c22250R_124_9 (by norm_num)

theorem c22250R_124_7 : rowsJ2 124 125 61 340 ≤ 1120702296923242 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3299 c22250R_124_8 (by norm_num)

theorem c22250R_124_6 : rowsJ2 124 125 59 340 ≤ 1126346341450538 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3298 c22250R_124_7 (by norm_num)

theorem c22250R_124_5 : rowsJ2 124 125 57 340 ≤ 1130082033673480 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3297 c22250R_124_6 (by norm_num)

theorem c22250R_124_4 : rowsJ2 124 125 42 340 ≤ 1133497678879669 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3296 c22250R_124_5 (by norm_num)

theorem c22250R_124_3 : rowsJ2 124 125 33 340 ≤ 1141249437461862 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3295 c22250R_124_4 (by norm_num)

theorem c22250R_124_2 : rowsJ2 124 125 29 340 ≤ 1157102714124749 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3294 c22250R_124_3 (by norm_num)

theorem c22250R_124_1 : rowsJ2 124 125 26 340 ≤ 1172291462325742 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3293 c22250R_124_2 (by norm_num)

theorem c22250R_124_0 : rowsJ2 124 125 0 340 ≤ 1177316699024554 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3292 c22250R_124_1 (by norm_num)

theorem hr22250R_124 : rows2 124 125 ≤ 1177316699024554 := rows2_le_of_rowsJ2 124 125 c22250R_124_0

theorem c22250R_125_24 : rowsJ2 125 126 87 340 ≤ 1035530797444142 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3342 rows22250R_3343 (by norm_num)

theorem c22250R_125_23 : rowsJ2 125 126 83 340 ≤ 1045906070558325 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3341 c22250R_125_24 (by norm_num)

theorem c22250R_125_22 : rowsJ2 125 126 79 340 ≤ 1046807518681093 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3340 c22250R_125_23 (by norm_num)

theorem c22250R_125_21 : rowsJ2 125 126 76 340 ≤ 1049884839798782 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3339 c22250R_125_22 (by norm_num)

theorem c22250R_125_20 : rowsJ2 125 126 74 340 ≤ 1054230124302744 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3338 c22250R_125_21 (by norm_num)

theorem c22250R_125_19 : rowsJ2 125 126 73 340 ≤ 1057237724579551 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3337 c22250R_125_20 (by norm_num)

theorem c22250R_125_18 : rowsJ2 125 126 72 340 ≤ 1060860930053210 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3336 c22250R_125_19 (by norm_num)

theorem c22250R_125_17 : rowsJ2 125 126 71 340 ≤ 1065163731130758 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3335 c22250R_125_18 (by norm_num)

theorem c22250R_125_16 : rowsJ2 125 126 70 340 ≤ 1070187504688699 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3334 c22250R_125_17 (by norm_num)

theorem c22250R_125_15 : rowsJ2 125 126 69 340 ≤ 1075642878080904 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3333 c22250R_125_16 (by norm_num)

theorem c22250R_125_14 : rowsJ2 125 126 68 340 ≤ 1081124109891883 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3332 c22250R_125_15 (by norm_num)

theorem c22250R_125_13 : rowsJ2 125 126 67 340 ≤ 1086575414756161 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3331 c22250R_125_14 (by norm_num)

theorem c22250R_125_12 : rowsJ2 125 126 66 340 ≤ 1091919022280444 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3330 c22250R_125_13 (by norm_num)

theorem c22250R_125_11 : rowsJ2 125 126 65 340 ≤ 1097101781229279 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3329 c22250R_125_12 (by norm_num)

theorem c22250R_125_10 : rowsJ2 125 126 64 340 ≤ 1102048484350670 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3328 c22250R_125_11 (by norm_num)

theorem c22250R_125_9 : rowsJ2 125 126 63 340 ≤ 1106707972661337 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3327 c22250R_125_10 (by norm_num)

theorem c22250R_125_8 : rowsJ2 125 126 62 340 ≤ 1111006982261042 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3326 c22250R_125_9 (by norm_num)

theorem c22250R_125_7 : rowsJ2 125 126 61 340 ≤ 1114895776934954 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3325 c22250R_125_8 (by norm_num)

theorem c22250R_125_6 : rowsJ2 125 126 59 340 ≤ 1121178263893628 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3324 c22250R_125_7 (by norm_num)

theorem c22250R_125_5 : rowsJ2 125 126 57 340 ≤ 1125439155227682 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3323 c22250R_125_6 (by norm_num)

theorem c22250R_125_4 : rowsJ2 125 126 52 340 ≤ 1129584570900769 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3322 c22250R_125_5 (by norm_num)

theorem c22250R_125_3 : rowsJ2 125 126 34 340 ≤ 1133475114051906 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3321 c22250R_125_4 (by norm_num)

theorem c22250R_125_2 : rowsJ2 125 126 29 340 ≤ 1148715297097849 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3320 c22250R_125_3 (by norm_num)

theorem c22250R_125_1 : rowsJ2 125 126 25 340 ≤ 1166639148112859 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3319 c22250R_125_2 (by norm_num)

theorem c22250R_125_0 : rowsJ2 125 126 0 340 ≤ 1169717643369263 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3318 c22250R_125_1 (by norm_num)

theorem hr22250R_125 : rows2 125 126 ≤ 1169717643369263 := rows2_le_of_rowsJ2 125 126 c22250R_125_0

theorem c22250R_126_25 : rowsJ2 126 127 89 340 ≤ 925481930454849 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3369 rows22250R_3370 (by norm_num)

theorem c22250R_126_24 : rowsJ2 126 127 86 340 ≤ 941907870294218 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3368 c22250R_126_25 (by norm_num)

theorem c22250R_126_23 : rowsJ2 126 127 82 340 ≤ 949268336271290 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3367 c22250R_126_24 (by norm_num)

theorem c22250R_126_22 : rowsJ2 126 127 78 340 ≤ 950924188836939 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3366 c22250R_126_23 (by norm_num)

theorem c22250R_126_21 : rowsJ2 126 127 76 340 ≤ 953863484342039 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3365 c22250R_126_22 (by norm_num)

theorem c22250R_126_20 : rowsJ2 126 127 74 340 ≤ 958701193549040 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3364 c22250R_126_21 (by norm_num)

theorem c22250R_126_19 : rowsJ2 126 127 73 340 ≤ 961956144086922 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3363 c22250R_126_20 (by norm_num)

theorem c22250R_126_18 : rowsJ2 126 127 72 340 ≤ 965827559372567 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3362 c22250R_126_19 (by norm_num)

theorem c22250R_126_17 : rowsJ2 126 127 71 340 ≤ 970379399194941 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3361 c22250R_126_18 (by norm_num)

theorem c22250R_126_16 : rowsJ2 126 127 70 340 ≤ 975653147413966 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3360 c22250R_126_17 (by norm_num)

theorem c22250R_126_15 : rowsJ2 126 127 69 340 ≤ 981715537523228 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3359 c22250R_126_16 (by norm_num)

theorem c22250R_126_14 : rowsJ2 126 127 68 340 ≤ 987772215127702 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3358 c22250R_126_15 (by norm_num)

theorem c22250R_126_13 : rowsJ2 126 127 67 340 ≤ 993767799997273 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3357 c22250R_126_14 (by norm_num)

theorem c22250R_126_12 : rowsJ2 126 127 66 340 ≤ 999625030566352 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3356 c22250R_126_13 (by norm_num)

theorem c22250R_126_11 : rowsJ2 126 127 65 340 ≤ 1005291099121639 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3355 c22250R_126_12 (by norm_num)

theorem c22250R_126_10 : rowsJ2 126 127 64 340 ≤ 1010691246658335 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3354 c22250R_126_11 (by norm_num)

theorem c22250R_126_9 : rowsJ2 126 127 63 340 ≤ 1015774600941858 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3353 c22250R_126_10 (by norm_num)

theorem c22250R_126_8 : rowsJ2 126 127 62 340 ≤ 1020468290225085 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3352 c22250R_126_9 (by norm_num)

theorem c22250R_126_7 : rowsJ2 126 127 61 340 ≤ 1024722812245327 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3351 c22250R_126_8 (by norm_num)

theorem c22250R_126_6 : rowsJ2 126 127 60 340 ≤ 1028466630095449 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3350 c22250R_126_7 (by norm_num)

theorem c22250R_126_5 : rowsJ2 126 127 58 340 ≤ 1034295436268990 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3349 c22250R_126_6 (by norm_num)

theorem c22250R_126_4 : rowsJ2 126 127 54 340 ≤ 1040368622071545 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3348 c22250R_126_5 (by norm_num)

theorem c22250R_126_3 : rowsJ2 126 127 35 340 ≤ 1042885909730058 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3347 c22250R_126_4 (by norm_num)

theorem c22250R_126_2 : rowsJ2 126 127 29 340 ≤ 1056442439565549 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3346 c22250R_126_3 (by norm_num)

theorem c22250R_126_1 : rowsJ2 126 127 25 340 ≤ 1073490657073773 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3345 c22250R_126_2 (by norm_num)

theorem c22250R_126_0 : rowsJ2 126 127 0 340 ≤ 1077096495303714 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3344 c22250R_126_1 (by norm_num)

theorem hr22250R_126 : rows2 126 127 ≤ 1077096495303714 := rows2_le_of_rowsJ2 126 127 c22250R_126_0

theorem c22250R_127_25 : rowsJ2 127 128 88 340 ≤ 918762079541044 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3396 rows22250R_3397 (by norm_num)

theorem c22250R_127_24 : rowsJ2 127 128 85 340 ≤ 932403589984418 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3395 c22250R_127_25 (by norm_num)

theorem c22250R_127_23 : rowsJ2 127 128 81 340 ≤ 937138402796774 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3394 c22250R_127_24 (by norm_num)

theorem c22250R_127_22 : rowsJ2 127 128 78 340 ≤ 939438865103402 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3393 c22250R_127_23 (by norm_num)

theorem c22250R_127_21 : rowsJ2 127 128 76 340 ≤ 942811163254163 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3392 c22250R_127_22 (by norm_num)

theorem c22250R_127_20 : rowsJ2 127 128 74 340 ≤ 948084929006506 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3391 c22250R_127_21 (by norm_num)

theorem c22250R_127_19 : rowsJ2 127 128 73 340 ≤ 951559144525978 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3390 c22250R_127_20 (by norm_num)

theorem c22250R_127_18 : rowsJ2 127 128 72 340 ≤ 955650750573815 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3389 c22250R_127_19 (by norm_num)

theorem c22250R_127_17 : rowsJ2 127 128 71 340 ≤ 960423677857154 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3388 c22250R_127_18 (by norm_num)

theorem c22250R_127_16 : rowsJ2 127 128 70 340 ≤ 965919517213250 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3387 c22250R_127_17 (by norm_num)

theorem c22250R_127_15 : rowsJ2 127 128 69 340 ≤ 972204971452533 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3386 c22250R_127_16 (by norm_num)

theorem c22250R_127_14 : rowsJ2 127 128 68 340 ≤ 978873301826592 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3385 c22250R_127_15 (by norm_num)

theorem c22250R_127_13 : rowsJ2 127 128 67 340 ≤ 985449154788871 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3384 c22250R_127_14 (by norm_num)

theorem c22250R_127_12 : rowsJ2 127 128 66 340 ≤ 991855789681143 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3383 c22250R_127_13 (by norm_num)

theorem c22250R_127_11 : rowsJ2 127 128 65 340 ≤ 998040755425572 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3382 c22250R_127_12 (by norm_num)

theorem c22250R_127_10 : rowsJ2 127 128 64 340 ≤ 1003929752356073 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3381 c22250R_127_11 (by norm_num)

theorem c22250R_127_9 : rowsJ2 127 128 63 340 ≤ 1009472207160254 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3380 c22250R_127_10 (by norm_num)

theorem c22250R_127_8 : rowsJ2 127 128 62 340 ≤ 1014595650473437 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3379 c22250R_127_9 (by norm_num)

theorem c22250R_127_7 : rowsJ2 127 128 61 340 ≤ 1019250825337750 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3378 c22250R_127_8 (by norm_num)

theorem c22250R_127_6 : rowsJ2 127 128 60 340 ≤ 1023366544069268 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3377 c22250R_127_7 (by norm_num)

theorem c22250R_127_5 : rowsJ2 127 128 58 340 ≤ 1029853263674086 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3376 c22250R_127_6 (by norm_num)

theorem c22250R_127_4 : rowsJ2 127 128 55 340 ≤ 1035755988566984 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3375 c22250R_127_5 (by norm_num)

theorem c22250R_127_3 : rowsJ2 127 128 36 340 ≤ 1038814717876506 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3374 c22250R_127_4 (by norm_num)

theorem c22250R_127_2 : rowsJ2 127 128 29 340 ≤ 1049922839166030 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3373 c22250R_127_3 (by norm_num)

theorem c22250R_127_1 : rowsJ2 127 128 25 340 ≤ 1066432080615101 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3372 c22250R_127_2 (by norm_num)

theorem c22250R_127_0 : rowsJ2 127 128 0 340 ≤ 1070561453689428 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3371 c22250R_127_1 (by norm_num)

theorem hr22250R_127 : rows2 127 128 ≤ 1070561453689428 := rows2_le_of_rowsJ2 127 128 c22250R_127_0

theorem c22250R_128_26 : rowsJ2 128 129 87 340 ≤ 828559773889103 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3424 rows22250R_3425 (by norm_num)

theorem c22250R_128_25 : rowsJ2 128 129 83 340 ≤ 840928426288025 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3423 c22250R_128_26 (by norm_num)

theorem c22250R_128_24 : rowsJ2 128 129 79 340 ≤ 843703422107501 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3422 c22250R_128_25 (by norm_num)

theorem c22250R_128_23 : rowsJ2 128 129 77 340 ≤ 846588773840845 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3421 c22250R_128_24 (by norm_num)

theorem c22250R_128_22 : rowsJ2 128 129 75 340 ≤ 851189492471653 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3420 c22250R_128_23 (by norm_num)

theorem c22250R_128_21 : rowsJ2 128 129 74 340 ≤ 854248656971624 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3419 c22250R_128_22 (by norm_num)

theorem c22250R_128_20 : rowsJ2 128 129 73 340 ≤ 857887195811186 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3418 c22250R_128_21 (by norm_num)

theorem c22250R_128_19 : rowsJ2 128 129 72 340 ≤ 862143890725532 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3417 c22250R_128_20 (by norm_num)

theorem c22250R_128_18 : rowsJ2 128 129 71 340 ≤ 867082641000601 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3416 c22250R_128_19 (by norm_num)

theorem c22250R_128_17 : rowsJ2 128 129 70 340 ≤ 872745140498106 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3415 c22250R_128_18 (by norm_num)

theorem c22250R_128_16 : rowsJ2 128 129 69 340 ≤ 879198058908026 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3414 c22250R_128_17 (by norm_num)

theorem c22250R_128_15 : rowsJ2 128 129 68 340 ≤ 886486323011304 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3413 c22250R_128_16 (by norm_num)

theorem c22250R_128_14 : rowsJ2 128 129 67 340 ≤ 893650232819466 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3412 c22250R_128_15 (by norm_num)

theorem c22250R_128_13 : rowsJ2 128 129 66 340 ≤ 900613577144214 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3411 c22250R_128_14 (by norm_num)

theorem c22250R_128_12 : rowsJ2 128 129 65 340 ≤ 907324270939719 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3410 c22250R_128_13 (by norm_num)

theorem c22250R_128_11 : rowsJ2 128 129 64 340 ≤ 913708481106249 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3409 c22250R_128_12 (by norm_num)

theorem c22250R_128_10 : rowsJ2 128 129 63 340 ≤ 919715941362367 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3408 c22250R_128_11 (by norm_num)

theorem c22250R_128_9 : rowsJ2 128 129 62 340 ≤ 925274590740376 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3407 c22250R_128_10 (by norm_num)

theorem c22250R_128_8 : rowsJ2 128 129 61 340 ≤ 930335424521011 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3406 c22250R_128_9 (by norm_num)

theorem c22250R_128_7 : rowsJ2 128 129 60 340 ≤ 934827609147428 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3405 c22250R_128_8 (by norm_num)

theorem c22250R_128_6 : rowsJ2 128 129 59 340 ≤ 938702897268052 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3404 c22250R_128_7 (by norm_num)

theorem c22250R_128_5 : rowsJ2 128 129 58 340 ≤ 941980076377354 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3403 c22250R_128_6 (by norm_num)

theorem c22250R_128_4 : rowsJ2 128 129 55 340 ≤ 948658569942007 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3402 c22250R_128_5 (by norm_num)

theorem c22250R_128_3 : rowsJ2 128 129 38 340 ≤ 952279421731748 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3401 c22250R_128_4 (by norm_num)

theorem c22250R_128_2 : rowsJ2 128 129 29 340 ≤ 960528287522342 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3400 c22250R_128_3 (by norm_num)

theorem c22250R_128_1 : rowsJ2 128 129 25 340 ≤ 975548250026474 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3399 c22250R_128_2 (by norm_num)

theorem c22250R_128_0 : rowsJ2 128 129 0 340 ≤ 980201586308885 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3398 c22250R_128_1 (by norm_num)

theorem hr22250R_128 : rows2 128 129 ≤ 980201586308885 := rows2_le_of_rowsJ2 128 129 c22250R_128_0

theorem c22250R_129_26 : rowsJ2 129 130 86 340 ≤ 822590649907058 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3452 rows22250R_3453 (by norm_num)

theorem c22250R_129_25 : rowsJ2 129 130 82 340 ≤ 831909483475965 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3451 c22250R_129_26 (by norm_num)

theorem c22250R_129_24 : rowsJ2 129 130 79 340 ≤ 834217053938287 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3450 c22250R_129_25 (by norm_num)

theorem c22250R_129_23 : rowsJ2 129 130 77 340 ≤ 837371289566585 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3449 c22250R_129_24 (by norm_num)

theorem c22250R_129_22 : rowsJ2 129 130 75 340 ≤ 842243467025860 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3448 c22250R_129_23 (by norm_num)

theorem c22250R_129_21 : rowsJ2 129 130 74 340 ≤ 845439450229724 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3447 c22250R_129_22 (by norm_num)

theorem c22250R_129_20 : rowsJ2 129 130 73 340 ≤ 849215542657692 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3446 c22250R_129_21 (by norm_num)

theorem c22250R_129_19 : rowsJ2 129 130 72 340 ≤ 853610632610198 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3445 c22250R_129_20 (by norm_num)

theorem c22250R_129_18 : rowsJ2 129 130 71 340 ≤ 858688589571812 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3444 c22250R_129_19 (by norm_num)

theorem c22250R_129_17 : rowsJ2 129 130 70 340 ≤ 864491210564043 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3443 c22250R_129_18 (by norm_num)

theorem c22250R_129_16 : rowsJ2 129 130 69 340 ≤ 871085133886643 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3442 c22250R_129_17 (by norm_num)

theorem c22250R_129_15 : rowsJ2 129 130 68 340 ≤ 878515386315140 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3441 c22250R_129_16 (by norm_num)

theorem c22250R_129_14 : rowsJ2 129 130 67 340 ≤ 886304935992294 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3440 c22250R_129_15 (by norm_num)

theorem c22250R_129_13 : rowsJ2 129 130 66 340 ≤ 893862324072892 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3439 c22250R_129_14 (by norm_num)

theorem c22250R_129_12 : rowsJ2 129 130 65 340 ≤ 901135846435328 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3438 c22250R_129_13 (by norm_num)

theorem c22250R_129_11 : rowsJ2 129 130 64 340 ≤ 908052149365030 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3437 c22250R_129_12 (by norm_num)

theorem c22250R_129_10 : rowsJ2 129 130 63 340 ≤ 914561287363954 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3436 c22250R_129_11 (by norm_num)

theorem c22250R_129_9 : rowsJ2 129 130 62 340 ≤ 920591619631373 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3435 c22250R_129_10 (by norm_num)

theorem c22250R_129_8 : rowsJ2 129 130 61 340 ≤ 926094406444735 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3434 c22250R_129_9 (by norm_num)

theorem c22250R_129_7 : rowsJ2 129 130 60 340 ≤ 930999179230236 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3433 c22250R_129_8 (by norm_num)

theorem c22250R_129_6 : rowsJ2 129 130 59 340 ≤ 935257903408938 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3432 c22250R_129_7 (by norm_num)

theorem c22250R_129_5 : rowsJ2 129 130 58 340 ≤ 938889174592625 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3431 c22250R_129_6 (by norm_num)

theorem c22250R_129_4 : rowsJ2 129 130 56 340 ≤ 944440221686489 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3430 c22250R_129_5 (by norm_num)

theorem c22250R_129_3 : rowsJ2 129 130 50 340 ≤ 950846439222818 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3429 c22250R_129_4 (by norm_num)

theorem c22250R_129_2 : rowsJ2 129 130 30 340 ≤ 954848865774216 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3428 c22250R_129_3 (by norm_num)

theorem c22250R_129_1 : rowsJ2 129 130 25 340 ≤ 970551951433055 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3427 c22250R_129_2 (by norm_num)

theorem c22250R_129_0 : rowsJ2 129 130 0 340 ≤ 975864513945409 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3426 c22250R_129_1 (by norm_num)

theorem hr22250R_129 : rows2 129 130 ≤ 975864513945409 := rows2_le_of_rowsJ2 129 130 c22250R_129_0

theorem c22250R_130_27 : rowsJ2 130 131 86 340 ≤ 730113380431660 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3481 rows22250R_3482 (by norm_num)

theorem c22250R_130_26 : rowsJ2 130 131 82 340 ≤ 740145175701618 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3480 c22250R_130_27 (by norm_num)

theorem c22250R_130_25 : rowsJ2 130 131 79 340 ≤ 742692267815846 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3479 c22250R_130_26 (by norm_num)

theorem c22250R_130_24 : rowsJ2 130 131 77 340 ≤ 746008199081418 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3478 c22250R_130_25 (by norm_num)

theorem c22250R_130_23 : rowsJ2 130 131 75 340 ≤ 751044075536963 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3477 c22250R_130_24 (by norm_num)

theorem c22250R_130_22 : rowsJ2 130 131 74 340 ≤ 754322775668146 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3476 c22250R_130_23 (by norm_num)

theorem c22250R_130_21 : rowsJ2 130 131 73 340 ≤ 758182168510205 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3475 c22250R_130_22 (by norm_num)

theorem c22250R_130_20 : rowsJ2 130 131 72 340 ≤ 762661245104421 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3474 c22250R_130_21 (by norm_num)

theorem c22250R_130_19 : rowsJ2 130 131 71 340 ≤ 767823842791594 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3473 c22250R_130_20 (by norm_num)

theorem c22250R_130_18 : rowsJ2 130 131 70 340 ≤ 773711857851582 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3472 c22250R_130_19 (by norm_num)

theorem c22250R_130_17 : rowsJ2 130 131 69 340 ≤ 780391894757323 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3471 c22250R_130_18 (by norm_num)

theorem c22250R_130_16 : rowsJ2 130 131 68 340 ≤ 787909076304392 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3470 c22250R_130_17 (by norm_num)

theorem c22250R_130_15 : rowsJ2 130 131 67 340 ≤ 796333129677738 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3469 c22250R_130_16 (by norm_num)

theorem c22250R_130_14 : rowsJ2 130 131 66 340 ≤ 804492892530948 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3468 c22250R_130_15 (by norm_num)

theorem c22250R_130_13 : rowsJ2 130 131 65 340 ≤ 812337052870707 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3467 c22250R_130_14 (by norm_num)

theorem c22250R_130_12 : rowsJ2 130 131 64 340 ≤ 819792745339190 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3466 c22250R_130_13 (by norm_num)

theorem c22250R_130_11 : rowsJ2 130 131 63 340 ≤ 826810354916866 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3465 c22250R_130_12 (by norm_num)

theorem c22250R_130_10 : rowsJ2 130 131 62 340 ≤ 833318668521832 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3464 c22250R_130_11 (by norm_num)

theorem c22250R_130_9 : rowsJ2 130 131 61 340 ≤ 839269219756066 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3463 c22250R_130_10 (by norm_num)

theorem c22250R_130_8 : rowsJ2 130 131 60 340 ≤ 844591911289585 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3462 c22250R_130_9 (by norm_num)

theorem c22250R_130_7 : rowsJ2 130 131 59 340 ≤ 849238928395299 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3461 c22250R_130_8 (by norm_num)

theorem c22250R_130_6 : rowsJ2 130 131 58 340 ≤ 853228685584627 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3460 c22250R_130_7 (by norm_num)

theorem c22250R_130_5 : rowsJ2 130 131 57 340 ≤ 856603096406504 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3459 c22250R_130_6 (by norm_num)

theorem c22250R_130_4 : rowsJ2 130 131 55 340 ≤ 861682754917183 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3458 c22250R_130_5 (by norm_num)

theorem c22250R_130_3 : rowsJ2 130 131 50 340 ≤ 866932480095096 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3457 c22250R_130_4 (by norm_num)

theorem c22250R_130_2 : rowsJ2 130 131 29 340 ≤ 871068818902848 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3456 c22250R_130_3 (by norm_num)

theorem c22250R_130_1 : rowsJ2 130 131 24 340 ≤ 885664953406915 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3455 c22250R_130_2 (by norm_num)

theorem c22250R_130_0 : rowsJ2 130 131 0 340 ≤ 888700173647942 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_3454 c22250R_130_1 (by norm_num)

theorem hr22250R_130 : rows2 130 131 ≤ 888700173647942 := rows2_le_of_rowsJ2 130 131 c22250R_130_0

theorem c22250R_131_26 : rowsJ2 131 132 82 340 ≤ 733121736824460 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3509 rows22250R_3510 (by norm_num)

theorem c22250R_131_25 : rowsJ2 131 132 79 340 ≤ 735829835162590 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3508 c22250R_131_26 (by norm_num)

theorem c22250R_131_24 : rowsJ2 131 132 77 340 ≤ 739255524309273 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3507 c22250R_131_25 (by norm_num)

theorem c22250R_131_23 : rowsJ2 131 132 75 340 ≤ 744403493114892 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3506 c22250R_131_24 (by norm_num)

theorem c22250R_131_22 : rowsJ2 131 132 74 340 ≤ 747739232706771 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3505 c22250R_131_23 (by norm_num)

theorem c22250R_131_21 : rowsJ2 131 132 73 340 ≤ 751656333996870 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3504 c22250R_131_22 (by norm_num)

theorem c22250R_131_20 : rowsJ2 131 132 72 340 ≤ 756193890898808 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3503 c22250R_131_21 (by norm_num)

theorem c22250R_131_19 : rowsJ2 131 132 71 340 ≤ 761415710298292 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3502 c22250R_131_20 (by norm_num)

theorem c22250R_131_18 : rowsJ2 131 132 70 340 ≤ 767363787993140 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3501 c22250R_131_19 (by norm_num)

theorem c22250R_131_17 : rowsJ2 131 132 69 340 ≤ 774104696436507 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3500 c22250R_131_18 (by norm_num)

theorem c22250R_131_16 : rowsJ2 131 132 68 340 ≤ 781683654850117 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3499 c22250R_131_17 (by norm_num)

theorem c22250R_131_15 : rowsJ2 131 132 67 340 ≤ 790170356986539 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3498 c22250R_131_16 (by norm_num)

theorem c22250R_131_14 : rowsJ2 131 132 66 340 ≤ 798971514052397 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3497 c22250R_131_15 (by norm_num)

theorem c22250R_131_13 : rowsJ2 131 132 65 340 ≤ 807425053807192 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3496 c22250R_131_14 (by norm_num)

theorem c22250R_131_12 : rowsJ2 131 132 64 340 ≤ 815458614029091 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3495 c22250R_131_13 (by norm_num)

theorem c22250R_131_11 : rowsJ2 131 132 63 340 ≤ 823022925727815 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3494 c22250R_131_12 (by norm_num)

theorem c22250R_131_10 : rowsJ2 131 132 62 340 ≤ 830047217053220 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3493 c22250R_131_11 (by norm_num)

theorem c22250R_131_9 : rowsJ2 131 132 61 340 ≤ 836483309286507 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3492 c22250R_131_10 (by norm_num)

theorem c22250R_131_8 : rowsJ2 131 132 60 340 ≤ 842261488752189 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3491 c22250R_131_9 (by norm_num)

theorem c22250R_131_7 : rowsJ2 131 132 59 340 ≤ 847334173887453 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3490 c22250R_131_8 (by norm_num)

theorem c22250R_131_6 : rowsJ2 131 132 58 340 ≤ 851719615162983 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3489 c22250R_131_7 (by norm_num)

theorem c22250R_131_5 : rowsJ2 131 132 57 340 ≤ 855459404965665 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3488 c22250R_131_6 (by norm_num)

theorem c22250R_131_4 : rowsJ2 131 132 55 340 ≤ 861177444027422 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3487 c22250R_131_5 (by norm_num)

theorem c22250R_131_3 : rowsJ2 131 132 52 340 ≤ 866061803625669 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3486 c22250R_131_4 (by norm_num)

theorem c22250R_131_2 : rowsJ2 131 132 30 340 ≤ 869232352199966 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3485 c22250R_131_3 (by norm_num)

theorem c22250R_131_1 : rowsJ2 131 132 24 340 ≤ 883312651870115 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3484 c22250R_131_2 (by norm_num)

theorem c22250R_131_0 : rowsJ2 131 132 0 340 ≤ 886885532595982 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_3483 c22250R_131_1 (by norm_num)

theorem hr22250R_131 : rows2 131 132 ≤ 886885532595982 := rows2_le_of_rowsJ2 131 132 c22250R_131_0

theorem c22250R_132_26 : rowsJ2 132 133 82 340 ≤ 643624314568646 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3537 rows22250R_3538 (by norm_num)

theorem c22250R_132_25 : rowsJ2 132 133 79 340 ≤ 646335147548319 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3536 c22250R_132_26 (by norm_num)

theorem c22250R_132_24 : rowsJ2 132 133 77 340 ≤ 649764423105589 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3535 c22250R_132_25 (by norm_num)

theorem c22250R_132_23 : rowsJ2 132 133 75 340 ≤ 654917760757660 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3534 c22250R_132_24 (by norm_num)

theorem c22250R_132_22 : rowsJ2 132 133 74 340 ≤ 658256963527463 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3533 c22250R_132_23 (by norm_num)

theorem c22250R_132_21 : rowsJ2 132 133 73 340 ≤ 662178050454691 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3532 c22250R_132_22 (by norm_num)

theorem c22250R_132_20 : rowsJ2 132 133 72 340 ≤ 666720214528681 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3531 c22250R_132_21 (by norm_num)

theorem c22250R_132_19 : rowsJ2 132 133 71 340 ≤ 671947229816154 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3530 c22250R_132_20 (by norm_num)

theorem c22250R_132_18 : rowsJ2 132 133 70 340 ≤ 677901187762264 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3529 c22250R_132_19 (by norm_num)

theorem c22250R_132_17 : rowsJ2 132 133 69 340 ≤ 684648626346150 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3528 c22250R_132_18 (by norm_num)

theorem c22250R_132_16 : rowsJ2 132 133 68 340 ≤ 692234857275265 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3527 c22250R_132_17 (by norm_num)

theorem c22250R_132_15 : rowsJ2 132 133 67 340 ≤ 700729538330429 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3526 c22250R_132_16 (by norm_num)

theorem c22250R_132_14 : rowsJ2 132 133 66 340 ≤ 710181559134623 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3525 c22250R_132_15 (by norm_num)

theorem c22250R_132_13 : rowsJ2 132 133 65 340 ≤ 719253374237986 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3524 c22250R_132_14 (by norm_num)

theorem c22250R_132_12 : rowsJ2 132 133 64 340 ≤ 727873135519503 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3523 c22250R_132_13 (by norm_num)

theorem c22250R_132_11 : rowsJ2 132 133 63 340 ≤ 735991931533487 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3522 c22250R_132_12 (by norm_num)

theorem c22250R_132_10 : rowsJ2 132 133 62 340 ≤ 743539440965956 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3521 c22250R_132_11 (by norm_num)

theorem c22250R_132_9 : rowsJ2 132 133 61 340 ≤ 750467782701568 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3520 c22250R_132_10 (by norm_num)

theorem c22250R_132_8 : rowsJ2 132 133 60 340 ≤ 756707634523517 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3519 c22250R_132_9 (by norm_num)

theorem c22250R_132_7 : rowsJ2 132 133 59 340 ≤ 762211656514051 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3518 c22250R_132_8 (by norm_num)

theorem c22250R_132_6 : rowsJ2 132 133 58 340 ≤ 766997947055997 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3517 c22250R_132_7 (by norm_num)

theorem c22250R_132_5 : rowsJ2 132 133 57 340 ≤ 771107790153027 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3516 c22250R_132_6 (by norm_num)

theorem c22250R_132_4 : rowsJ2 132 133 55 340 ≤ 777472134435687 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3515 c22250R_132_5 (by norm_num)

theorem c22250R_132_3 : rowsJ2 132 133 52 340 ≤ 783085167991571 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3514 c22250R_132_4 (by norm_num)

theorem c22250R_132_2 : rowsJ2 132 133 31 340 ≤ 785664083785890 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3513 c22250R_132_3 (by norm_num)

theorem c22250R_132_1 : rowsJ2 132 133 24 340 ≤ 797202773259268 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3512 c22250R_132_2 (by norm_num)

theorem c22250R_132_0 : rowsJ2 132 133 0 340 ≤ 801601088863920 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_3511 c22250R_132_1 (by norm_num)

theorem hr22250R_132 : rows2 132 133 ≤ 801601088863920 := rows2_le_of_rowsJ2 132 133 c22250R_132_0

theorem c22250R_133_26 : rowsJ2 133 134 83 340 ≤ 637187527345086 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3565 rows22250R_3566 (by norm_num)

theorem c22250R_133_25 : rowsJ2 133 134 79 340 ≤ 641221759514139 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3564 c22250R_133_26 (by norm_num)

theorem c22250R_133_24 : rowsJ2 133 134 77 340 ≤ 644604692984593 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3563 c22250R_133_25 (by norm_num)

theorem c22250R_133_23 : rowsJ2 133 134 75 340 ≤ 649713840367330 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3562 c22250R_133_24 (by norm_num)

theorem c22250R_133_22 : rowsJ2 133 134 74 340 ≤ 653031867133988 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3561 c22250R_133_23 (by norm_num)

theorem c22250R_133_21 : rowsJ2 133 134 73 340 ≤ 656932395774852 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3560 c22250R_133_22 (by norm_num)

theorem c22250R_133_20 : rowsJ2 133 134 72 340 ≤ 661454718586121 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3559 c22250R_133_21 (by norm_num)

theorem c22250R_133_19 : rowsJ2 133 134 71 340 ≤ 666662578557957 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3558 c22250R_133_20 (by norm_num)

theorem c22250R_133_18 : rowsJ2 133 134 70 340 ≤ 672598163149558 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3557 c22250R_133_19 (by norm_num)

theorem c22250R_133_17 : rowsJ2 133 134 69 340 ≤ 679327977735211 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3556 c22250R_133_18 (by norm_num)

theorem c22250R_133_16 : rowsJ2 133 134 68 340 ≤ 686897427029274 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3555 c22250R_133_17 (by norm_num)

theorem c22250R_133_15 : rowsJ2 133 134 67 340 ≤ 695376134857234 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3554 c22250R_133_16 (by norm_num)

theorem c22250R_133_14 : rowsJ2 133 134 66 340 ≤ 704813081099145 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3553 c22250R_133_15 (by norm_num)

theorem c22250R_133_13 : rowsJ2 133 134 65 340 ≤ 714543694848338 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3552 c22250R_133_14 (by norm_num)

theorem c22250R_133_12 : rowsJ2 133 134 64 340 ≤ 723789870574023 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3551 c22250R_133_13 (by norm_num)

theorem c22250R_133_11 : rowsJ2 133 134 63 340 ≤ 732503071982761 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3550 c22250R_133_12 (by norm_num)

theorem c22250R_133_10 : rowsJ2 133 134 62 340 ≤ 740613443791258 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3549 c22250R_133_11 (by norm_num)

theorem c22250R_133_9 : rowsJ2 133 134 61 340 ≤ 748073418663323 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3548 c22250R_133_10 (by norm_num)

theorem c22250R_133_8 : rowsJ2 133 134 60 340 ≤ 754814080013416 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3547 c22250R_133_9 (by norm_num)

theorem c22250R_133_7 : rowsJ2 133 134 59 340 ≤ 760788344498444 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3546 c22250R_133_8 (by norm_num)

theorem c22250R_133_6 : rowsJ2 133 134 58 340 ≤ 766014176858845 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3545 c22250R_133_7 (by norm_num)

theorem c22250R_133_5 : rowsJ2 133 134 57 340 ≤ 770532572084209 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3544 c22250R_133_6 (by norm_num)

theorem c22250R_133_4 : rowsJ2 133 134 55 340 ≤ 777619713763320 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3543 c22250R_133_5 (by norm_num)

theorem c22250R_133_3 : rowsJ2 133 134 53 340 ≤ 782414373544721 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3542 c22250R_133_4 (by norm_num)

theorem c22250R_133_2 : rowsJ2 133 134 33 340 ≤ 787272103996330 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3541 c22250R_133_3 (by norm_num)

theorem c22250R_133_1 : rowsJ2 133 134 24 340 ≤ 795843606159298 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3540 c22250R_133_2 (by norm_num)

theorem c22250R_133_0 : rowsJ2 133 134 0 340 ≤ 801354142951572 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_3539 c22250R_133_1 (by norm_num)

theorem hr22250R_133 : rows2 133 134 ≤ 801354142951572 := rows2_le_of_rowsJ2 133 134 c22250R_133_0

theorem c22250R_134_25 : rowsJ2 134 135 81 340 ≤ 551249798523375 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3592 rows22250R_3593 (by norm_num)

theorem c22250R_134_24 : rowsJ2 134 135 78 340 ≤ 554539608690532 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3591 c22250R_134_25 (by norm_num)

theorem c22250R_134_23 : rowsJ2 134 135 76 340 ≤ 558587867809327 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3590 c22250R_134_24 (by norm_num)

theorem c22250R_134_22 : rowsJ2 134 135 74 340 ≤ 564553458318015 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3589 c22250R_134_23 (by norm_num)

theorem c22250R_134_21 : rowsJ2 134 135 73 340 ≤ 568380084367497 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3588 c22250R_134_22 (by norm_num)

theorem c22250R_134_20 : rowsJ2 134 135 72 340 ≤ 572829076132565 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3587 c22250R_134_21 (by norm_num)

theorem c22250R_134_19 : rowsJ2 134 135 71 340 ≤ 577964143122553 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3586 c22250R_134_20 (by norm_num)

theorem c22250R_134_18 : rowsJ2 134 135 70 340 ≤ 583827564949760 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3585 c22250R_134_19 (by norm_num)

theorem c22250R_134_17 : rowsJ2 134 135 69 340 ≤ 590485811893054 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3584 c22250R_134_18 (by norm_num)

theorem c22250R_134_16 : rowsJ2 134 135 68 340 ≤ 597984377746620 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3583 c22250R_134_17 (by norm_num)

theorem c22250R_134_15 : rowsJ2 134 135 67 340 ≤ 606392849809135 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3582 c22250R_134_16 (by norm_num)

theorem c22250R_134_14 : rowsJ2 134 135 66 340 ≤ 615760294228774 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3581 c22250R_134_15 (by norm_num)

theorem c22250R_134_13 : rowsJ2 134 135 65 340 ≤ 626159809608987 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3580 c22250R_134_14 (by norm_num)

theorem c22250R_134_12 : rowsJ2 134 135 64 340 ≤ 636041885100256 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3579 c22250R_134_13 (by norm_num)

theorem c22250R_134_11 : rowsJ2 134 135 63 340 ≤ 645358373173672 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3578 c22250R_134_12 (by norm_num)

theorem c22250R_134_10 : rowsJ2 134 135 62 340 ≤ 654039895888346 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3577 c22250R_134_11 (by norm_num)

theorem c22250R_134_9 : rowsJ2 134 135 61 340 ≤ 662039211446732 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3576 c22250R_134_10 (by norm_num)

theorem c22250R_134_8 : rowsJ2 134 135 60 340 ≤ 669287818462118 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3575 c22250R_134_9 (by norm_num)

theorem c22250R_134_7 : rowsJ2 134 135 59 340 ≤ 675738900255166 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3574 c22250R_134_8 (by norm_num)

theorem c22250R_134_6 : rowsJ2 134 135 58 340 ≤ 681410301246315 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3573 c22250R_134_7 (by norm_num)

theorem c22250R_134_5 : rowsJ2 134 135 57 340 ≤ 686342741415258 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3572 c22250R_134_6 (by norm_num)

theorem c22250R_134_4 : rowsJ2 134 135 55 340 ≤ 694162117212527 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3571 c22250R_134_5 (by norm_num)

theorem c22250R_134_3 : rowsJ2 134 135 53 340 ≤ 699558682596700 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3570 c22250R_134_4 (by norm_num)

theorem c22250R_134_2 : rowsJ2 134 135 36 340 ≤ 705439007937466 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3569 c22250R_134_3 (by norm_num)

theorem c22250R_134_1 : rowsJ2 134 135 24 340 ≤ 711489863443479 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3568 c22250R_134_2 (by norm_num)

theorem c22250R_134_0 : rowsJ2 134 135 0 340 ≤ 717232061017139 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_3567 c22250R_134_1 (by norm_num)

theorem hr22250R_134 : rows2 134 135 ≤ 717232061017139 := rows2_le_of_rowsJ2 134 135 c22250R_134_0

theorem c22250R_135_26 : rowsJ2 135 136 82 340 ≤ 549511196087869 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3620 rows22250R_3621 (by norm_num)

theorem c22250R_135_25 : rowsJ2 135 136 78 340 ≤ 552935729407871 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3619 c22250R_135_26 (by norm_num)

theorem c22250R_135_24 : rowsJ2 135 136 76 340 ≤ 556784997189346 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3618 c22250R_135_25 (by norm_num)

theorem c22250R_135_23 : rowsJ2 135 136 74 340 ≤ 562553771231069 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3617 c22250R_135_24 (by norm_num)

theorem c22250R_135_22 : rowsJ2 135 136 73 340 ≤ 566282875938170 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3616 c22250R_135_23 (by norm_num)

theorem c22250R_135_21 : rowsJ2 135 136 72 340 ≤ 570635023453962 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3615 c22250R_135_22 (by norm_num)

theorem c22250R_135_20 : rowsJ2 135 136 71 340 ≤ 575673891587447 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3614 c22250R_135_21 (by norm_num)

theorem c22250R_135_19 : rowsJ2 135 136 70 340 ≤ 581441852560396 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3613 c22250R_135_20 (by norm_num)

theorem c22250R_135_18 : rowsJ2 135 136 69 340 ≤ 588005343472372 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3612 c22250R_135_19 (by norm_num)

theorem c22250R_135_17 : rowsJ2 135 136 68 340 ≤ 595409947816685 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3611 c22250R_135_18 (by norm_num)

theorem c22250R_135_16 : rowsJ2 135 136 67 340 ≤ 603725218437972 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3610 c22250R_135_17 (by norm_num)

theorem c22250R_135_15 : rowsJ2 135 136 66 340 ≤ 613000308555517 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3609 c22250R_135_16 (by norm_num)

theorem c22250R_135_14 : rowsJ2 135 136 65 340 ≤ 623308281224818 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3608 c22250R_135_15 (by norm_num)

theorem c22250R_135_13 : rowsJ2 135 136 64 340 ≤ 633868355556592 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3607 c22250R_135_14 (by norm_num)

theorem c22250R_135_12 : rowsJ2 135 136 63 340 ≤ 643829887572867 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3606 c22250R_135_13 (by norm_num)

theorem c22250R_135_11 : rowsJ2 135 136 62 340 ≤ 653123994433600 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3605 c22250R_135_12 (by norm_num)

theorem c22250R_135_10 : rowsJ2 135 136 61 340 ≤ 661703778141052 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3604 c22250R_135_11 (by norm_num)

theorem c22250R_135_9 : rowsJ2 135 136 60 340 ≤ 669501168686153 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3603 c22250R_135_10 (by norm_num)

theorem c22250R_135_8 : rowsJ2 135 136 59 340 ≤ 676469632829623 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3602 c22250R_135_9 (by norm_num)

theorem c22250R_135_7 : rowsJ2 135 136 58 340 ≤ 682626914723536 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3601 c22250R_135_8 (by norm_num)

theorem c22250R_135_6 : rowsJ2 135 136 57 340 ≤ 688013480166170 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3600 c22250R_135_7 (by norm_num)

theorem c22250R_135_5 : rowsJ2 135 136 56 340 ≤ 692671430889405 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3599 c22250R_135_6 (by norm_num)

theorem c22250R_135_4 : rowsJ2 135 136 55 340 ≤ 696644635938638 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3598 c22250R_135_5 (by norm_num)

theorem c22250R_135_3 : rowsJ2 135 136 53 340 ≤ 702721964232273 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3597 c22250R_135_4 (by norm_num)

theorem c22250R_135_2 : rowsJ2 135 136 47 340 ≤ 709745321409937 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3596 c22250R_135_3 (by norm_num)

theorem c22250R_135_1 : rowsJ2 135 136 24 340 ≤ 713946688689430 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3595 c22250R_135_2 (by norm_num)

theorem c22250R_135_0 : rowsJ2 135 136 0 340 ≤ 720186480190434 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_3594 c22250R_135_1 (by norm_num)

theorem hr22250R_135 : rows2 135 136 ≤ 720186480190434 := rows2_le_of_rowsJ2 135 136 c22250R_135_0

theorem c22250R_136_25 : rowsJ2 136 137 79 340 ≤ 465254722795935 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3647 rows22250R_3648 (by norm_num)

theorem c22250R_136_24 : rowsJ2 136 137 76 340 ≤ 469966742196076 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3646 c22250R_136_25 (by norm_num)

theorem c22250R_136_23 : rowsJ2 136 137 74 340 ≤ 475432882582048 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3645 c22250R_136_24 (by norm_num)

theorem c22250R_136_22 : rowsJ2 136 137 73 340 ≤ 479011353323464 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3644 c22250R_136_23 (by norm_num)

theorem c22250R_136_21 : rowsJ2 136 137 72 340 ≤ 483213403348956 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3643 c22250R_136_22 (by norm_num)

theorem c22250R_136_20 : rowsJ2 136 137 71 340 ≤ 488102676302612 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3642 c22250R_136_21 (by norm_num)

theorem c22250R_136_19 : rowsJ2 136 137 70 340 ≤ 493721633142756 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3641 c22250R_136_20 (by norm_num)

theorem c22250R_136_18 : rowsJ2 136 137 69 340 ≤ 500136675243280 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3640 c22250R_136_19 (by norm_num)

theorem c22250R_136_17 : rowsJ2 136 137 68 340 ≤ 507393471861470 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3639 c22250R_136_18 (by norm_num)

theorem c22250R_136_16 : rowsJ2 136 137 67 340 ≤ 515561538765261 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3638 c22250R_136_17 (by norm_num)

theorem c22250R_136_15 : rowsJ2 136 137 66 340 ≤ 524690112252170 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3637 c22250R_136_16 (by norm_num)

theorem c22250R_136_14 : rowsJ2 136 137 65 340 ≤ 534852217136296 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3636 c22250R_136_15 (by norm_num)

theorem c22250R_136_13 : rowsJ2 136 137 64 340 ≤ 546101056760313 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3635 c22250R_136_14 (by norm_num)

theorem c22250R_136_12 : rowsJ2 136 137 63 340 ≤ 556717736682999 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3634 c22250R_136_13 (by norm_num)

theorem c22250R_136_11 : rowsJ2 136 137 62 340 ≤ 566633882786809 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3633 c22250R_136_12 (by norm_num)

theorem c22250R_136_10 : rowsJ2 136 137 61 340 ≤ 575802954751158 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3632 c22250R_136_11 (by norm_num)

theorem c22250R_136_9 : rowsJ2 136 137 60 340 ≤ 584157325535874 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3631 c22250R_136_10 (by norm_num)

theorem c22250R_136_8 : rowsJ2 136 137 59 340 ≤ 591650757283043 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3630 c22250R_136_9 (by norm_num)

theorem c22250R_136_7 : rowsJ2 136 137 58 340 ≤ 598300908800938 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3629 c22250R_136_8 (by norm_num)

theorem c22250R_136_6 : rowsJ2 136 137 57 340 ≤ 604148007155155 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3628 c22250R_136_7 (by norm_num)

theorem c22250R_136_5 : rowsJ2 136 137 56 340 ≤ 609233877375211 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3627 c22250R_136_6 (by norm_num)

theorem c22250R_136_4 : rowsJ2 136 137 55 340 ≤ 613602073257155 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3626 c22250R_136_5 (by norm_num)

theorem c22250R_136_3 : rowsJ2 136 137 53 340 ≤ 620369139209245 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3625 c22250R_136_4 (by norm_num)

theorem c22250R_136_2 : rowsJ2 136 137 48 340 ≤ 628174064389372 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3624 c22250R_136_3 (by norm_num)

theorem c22250R_136_1 : rowsJ2 136 137 24 340 ≤ 631412748569168 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3623 c22250R_136_2 (by norm_num)

theorem c22250R_136_0 : rowsJ2 136 137 0 340 ≤ 637346662822214 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_3622 c22250R_136_1 (by norm_num)

theorem hr22250R_136 : rows2 136 137 ≤ 637346662822214 := rows2_le_of_rowsJ2 136 137 c22250R_136_0

theorem c22250R_137_24 : rowsJ2 137 138 77 340 ≤ 633671373724040 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3673 rows22250R_3674 (by norm_num)

theorem c22250R_137_23 : rowsJ2 137 138 75 340 ≤ 637779223455840 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3672 c22250R_137_24 (by norm_num)

theorem c22250R_137_22 : rowsJ2 137 138 73 340 ≤ 644004712017904 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3671 c22250R_137_23 (by norm_num)

theorem c22250R_137_21 : rowsJ2 137 138 72 340 ≤ 648033969737174 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3670 c22250R_137_22 (by norm_num)

theorem c22250R_137_20 : rowsJ2 137 138 71 340 ≤ 652751070384540 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3669 c22250R_137_21 (by norm_num)

theorem c22250R_137_19 : rowsJ2 137 138 70 340 ≤ 658198564182586 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3668 c22250R_137_20 (by norm_num)

theorem c22250R_137_18 : rowsJ2 137 138 69 340 ≤ 664442818726854 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3667 c22250R_137_19 (by norm_num)

theorem c22250R_137_17 : rowsJ2 137 138 68 340 ≤ 671529589738599 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3666 c22250R_137_18 (by norm_num)

theorem c22250R_137_16 : rowsJ2 137 138 67 340 ≤ 679528358022912 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3665 c22250R_137_17 (by norm_num)

theorem c22250R_137_15 : rowsJ2 137 138 66 340 ≤ 688488443848829 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3664 c22250R_137_16 (by norm_num)

theorem c22250R_137_14 : rowsJ2 137 138 65 340 ≤ 698482836092350 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3663 c22250R_137_15 (by norm_num)

theorem c22250R_137_13 : rowsJ2 137 138 64 340 ≤ 709564819860831 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3662 c22250R_137_14 (by norm_num)

theorem c22250R_137_12 : rowsJ2 137 138 63 340 ≤ 720880402061827 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3661 c22250R_137_13 (by norm_num)

theorem c22250R_137_11 : rowsJ2 137 138 62 340 ≤ 731461965212221 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3660 c22250R_137_12 (by norm_num)

theorem c22250R_137_10 : rowsJ2 137 138 61 340 ≤ 741263347328088 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3659 c22250R_137_11 (by norm_num)

theorem c22250R_137_9 : rowsJ2 137 138 60 340 ≤ 750217382812056 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3658 c22250R_137_10 (by norm_num)

theorem c22250R_137_8 : rowsJ2 137 138 59 340 ≤ 758278148081100 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3657 c22250R_137_9 (by norm_num)

theorem c22250R_137_7 : rowsJ2 137 138 58 340 ≤ 765463238515296 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3656 c22250R_137_8 (by norm_num)

theorem c22250R_137_6 : rowsJ2 137 138 57 340 ≤ 771812664978010 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3655 c22250R_137_7 (by norm_num)

theorem c22250R_137_5 : rowsJ2 137 138 56 340 ≤ 777367997746019 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3654 c22250R_137_6 (by norm_num)

theorem c22250R_137_4 : rowsJ2 137 138 55 340 ≤ 782172496795189 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3653 c22250R_137_5 (by norm_num)

theorem c22250R_137_3 : rowsJ2 137 138 53 340 ≤ 789711316382444 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3652 c22250R_137_4 (by norm_num)

theorem c22250R_137_2 : rowsJ2 137 138 49 340 ≤ 797903926671263 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3651 c22250R_137_3 (by norm_num)

theorem c22250R_137_1 : rowsJ2 137 138 24 340 ≤ 801324930816699 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3650 c22250R_137_2 (by norm_num)

theorem c22250R_137_0 : rowsJ2 137 138 0 340 ≤ 807204912133362 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_3649 c22250R_137_1 (by norm_num)

theorem hr22250R_137 : rows2 137 138 ≤ 807204912133362 := rows2_le_of_rowsJ2 137 138 c22250R_137_0

theorem c22250R_138_25 : rowsJ2 138 139 78 340 ≤ 705363819873562 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3700 rows22250R_3701 (by norm_num)

theorem c22250R_138_24 : rowsJ2 138 139 75 340 ≤ 710241992501025 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3699 c22250R_138_25 (by norm_num)

theorem c22250R_138_23 : rowsJ2 138 139 73 340 ≤ 716014115825682 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3698 c22250R_138_24 (by norm_num)

theorem c22250R_138_22 : rowsJ2 138 139 72 340 ≤ 719817421682267 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3697 c22250R_138_23 (by norm_num)

theorem c22250R_138_21 : rowsJ2 138 139 71 340 ≤ 724309052246665 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3696 c22250R_138_22 (by norm_num)

theorem c22250R_138_20 : rowsJ2 138 139 70 340 ≤ 729531643098079 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3695 c22250R_138_21 (by norm_num)

theorem c22250R_138_19 : rowsJ2 138 139 69 340 ≤ 735551525431043 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3694 c22250R_138_20 (by norm_num)

theorem c22250R_138_18 : rowsJ2 138 139 68 340 ≤ 742414537465381 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3693 c22250R_138_19 (by norm_num)

theorem c22250R_138_17 : rowsJ2 138 139 67 340 ≤ 750190122349473 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3692 c22250R_138_18 (by norm_num)

theorem c22250R_138_16 : rowsJ2 138 139 66 340 ≤ 758927680305328 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3691 c22250R_138_17 (by norm_num)

theorem c22250R_138_15 : rowsJ2 138 139 65 340 ≤ 768700161511307 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3690 c22250R_138_16 (by norm_num)

theorem c22250R_138_14 : rowsJ2 138 139 64 340 ≤ 779560928772431 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3689 c22250R_138_15 (by norm_num)

theorem c22250R_138_13 : rowsJ2 138 139 63 340 ≤ 791586878341744 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3688 c22250R_138_14 (by norm_num)

theorem c22250R_138_12 : rowsJ2 138 139 62 340 ≤ 802844612640047 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3687 c22250R_138_13 (by norm_num)

theorem c22250R_138_11 : rowsJ2 138 139 61 340 ≤ 813288364350855 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3686 c22250R_138_12 (by norm_num)

theorem c22250R_138_10 : rowsJ2 138 139 60 340 ≤ 822851443243835 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3685 c22250R_138_11 (by norm_num)

theorem c22250R_138_9 : rowsJ2 138 139 59 340 ≤ 831488254092844 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3684 c22250R_138_10 (by norm_num)

theorem c22250R_138_8 : rowsJ2 138 139 58 340 ≤ 839216345650036 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3683 c22250R_138_9 (by norm_num)

theorem c22250R_138_7 : rowsJ2 138 139 57 340 ≤ 846075529726445 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3682 c22250R_138_8 (by norm_num)

theorem c22250R_138_6 : rowsJ2 138 139 56 340 ≤ 852107138167858 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3681 c22250R_138_7 (by norm_num)

theorem c22250R_138_5 : rowsJ2 138 139 55 340 ≤ 857354152680885 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3680 c22250R_138_6 (by norm_num)

theorem c22250R_138_4 : rowsJ2 138 139 54 340 ≤ 861861341945952 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3679 c22250R_138_5 (by norm_num)

theorem c22250R_138_3 : rowsJ2 138 139 52 340 ≤ 868845133352307 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3678 c22250R_138_4 (by norm_num)

theorem c22250R_138_2 : rowsJ2 138 139 49 340 ≤ 875010934925553 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3677 c22250R_138_3 (by norm_num)

theorem c22250R_138_1 : rowsJ2 138 139 24 340 ≤ 878293022343851 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3676 c22250R_138_2 (by norm_num)

theorem c22250R_138_0 : rowsJ2 138 139 0 340 ≤ 883406997499962 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_3675 c22250R_138_1 (by norm_num)

theorem hr22250R_138 : rows2 138 139 ≤ 883406997499962 := rows2_le_of_rowsJ2 138 139 c22250R_138_0

theorem c22250R_139_24 : rowsJ2 139 140 76 340 ≤ 867035398281963 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3726 rows22250R_3727 (by norm_num)

theorem c22250R_139_23 : rowsJ2 139 140 74 340 ≤ 871268499382127 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3725 c22250R_139_24 (by norm_num)

theorem c22250R_139_22 : rowsJ2 139 140 72 340 ≤ 877753838809206 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3724 c22250R_139_23 (by norm_num)

theorem c22250R_139_21 : rowsJ2 139 140 71 340 ≤ 881998139211181 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3723 c22250R_139_22 (by norm_num)

theorem c22250R_139_20 : rowsJ2 139 140 70 340 ≤ 886974096011278 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3722 c22250R_139_21 (by norm_num)

theorem c22250R_139_19 : rowsJ2 139 140 69 340 ≤ 892748005964716 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3721 c22250R_139_20 (by norm_num)

theorem c22250R_139_18 : rowsJ2 139 140 68 340 ≤ 899365790552197 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3720 c22250R_139_19 (by norm_num)

theorem c22250R_139_17 : rowsJ2 139 140 67 340 ≤ 906896857404430 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3719 c22250R_139_18 (by norm_num)

theorem c22250R_139_16 : rowsJ2 139 140 66 340 ≤ 915390687662440 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3718 c22250R_139_17 (by norm_num)

theorem c22250R_139_15 : rowsJ2 139 140 65 340 ≤ 924920195146551 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3717 c22250R_139_16 (by norm_num)

theorem c22250R_139_14 : rowsJ2 139 140 64 340 ≤ 935538821552494 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3716 c22250R_139_15 (by norm_num)

theorem c22250R_139_13 : rowsJ2 139 140 63 340 ≤ 947323426156442 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3715 c22250R_139_14 (by norm_num)

theorem c22250R_139_12 : rowsJ2 139 140 62 340 ≤ 959302826109739 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3714 c22250R_139_13 (by norm_num)

theorem c22250R_139_11 : rowsJ2 139 140 61 340 ≤ 970434030095961 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3713 c22250R_139_12 (by norm_num)

theorem c22250R_139_10 : rowsJ2 139 140 60 340 ≤ 980650844363605 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3712 c22250R_139_11 (by norm_num)

theorem c22250R_139_9 : rowsJ2 139 140 59 340 ≤ 989908023374164 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3711 c22250R_139_10 (by norm_num)

theorem c22250R_139_8 : rowsJ2 139 140 58 340 ≤ 998223093334285 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3710 c22250R_139_9 (by norm_num)

theorem c22250R_139_7 : rowsJ2 139 140 57 340 ≤ 1005635691519321 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3709 c22250R_139_8 (by norm_num)

theorem c22250R_139_6 : rowsJ2 139 140 56 340 ≤ 1012186935149068 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3708 c22250R_139_7 (by norm_num)

theorem c22250R_139_5 : rowsJ2 139 140 55 340 ≤ 1017919550823354 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3707 c22250R_139_6 (by norm_num)

theorem c22250R_139_4 : rowsJ2 139 140 54 340 ≤ 1022878011117850 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3706 c22250R_139_5 (by norm_num)

theorem c22250R_139_3 : rowsJ2 139 140 52 340 ≤ 1030659960779047 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3705 c22250R_139_4 (by norm_num)

theorem c22250R_139_2 : rowsJ2 139 140 49 340 ≤ 1037755681455384 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3704 c22250R_139_3 (by norm_num)

theorem c22250R_139_1 : rowsJ2 139 140 24 340 ≤ 1041428535167013 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3703 c22250R_139_2 (by norm_num)

theorem c22250R_139_0 : rowsJ2 139 140 0 340 ≤ 1046023091602735 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_3702 c22250R_139_1 (by norm_num)

theorem hr22250R_139 : rows2 139 140 ≤ 1046023091602735 := rows2_le_of_rowsJ2 139 140 c22250R_139_0

theorem c22250R_140_24 : rowsJ2 140 141 77 340 ≤ 928920283654554 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3752 rows22250R_3753 (by norm_num)

theorem c22250R_140_23 : rowsJ2 140 141 74 340 ≤ 933948476779384 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3751 c22250R_140_24 (by norm_num)

theorem c22250R_140_22 : rowsJ2 140 141 72 340 ≤ 939898404404283 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3750 c22250R_140_23 (by norm_num)

theorem c22250R_140_21 : rowsJ2 140 141 71 340 ≤ 943842035558704 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3749 c22250R_140_22 (by norm_num)

theorem c22250R_140_20 : rowsJ2 140 141 70 340 ≤ 948517882030273 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3748 c22250R_140_21 (by norm_num)

theorem c22250R_140_19 : rowsJ2 140 141 69 340 ≤ 953992203414009 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3747 c22250R_140_20 (by norm_num)

theorem c22250R_140_18 : rowsJ2 140 141 68 340 ≤ 960311000432462 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3746 c22250R_140_19 (by norm_num)

theorem c22250R_140_17 : rowsJ2 140 141 67 340 ≤ 967543642412386 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3745 c22250R_140_18 (by norm_num)

theorem c22250R_140_16 : rowsJ2 140 141 66 340 ≤ 975739687346873 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3744 c22250R_140_17 (by norm_num)

theorem c22250R_140_15 : rowsJ2 140 141 65 340 ≤ 984972009851898 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3743 c22250R_140_16 (by norm_num)

theorem c22250R_140_14 : rowsJ2 140 141 64 340 ≤ 995294126403665 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3742 c22250R_140_15 (by norm_num)

theorem c22250R_140_13 : rowsJ2 140 141 63 340 ≤ 1006782856400960 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3741 c22250R_140_14 (by norm_num)

theorem c22250R_140_12 : rowsJ2 140 141 62 340 ≤ 1019496123671635 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3740 c22250R_140_13 (by norm_num)

theorem c22250R_140_11 : rowsJ2 140 141 61 340 ≤ 1031326220729331 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3739 c22250R_140_12 (by norm_num)

theorem c22250R_140_10 : rowsJ2 140 141 60 340 ≤ 1042207466926913 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3738 c22250R_140_11 (by norm_num)

theorem c22250R_140_9 : rowsJ2 140 141 59 340 ≤ 1052094982979010 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3737 c22250R_140_10 (by norm_num)

theorem c22250R_140_8 : rowsJ2 140 141 58 340 ≤ 1061006291545685 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3736 c22250R_140_9 (by norm_num)

theorem c22250R_140_7 : rowsJ2 140 141 57 340 ≤ 1068980874519471 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3735 c22250R_140_8 (by norm_num)

theorem c22250R_140_6 : rowsJ2 140 141 56 340 ≤ 1076059652673156 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3734 c22250R_140_7 (by norm_num)

theorem c22250R_140_5 : rowsJ2 140 141 55 340 ≤ 1082285114771428 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3733 c22250R_140_6 (by norm_num)

theorem c22250R_140_4 : rowsJ2 140 141 54 340 ≤ 1087701453711877 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3732 c22250R_140_5 (by norm_num)

theorem c22250R_140_3 : rowsJ2 140 141 52 340 ≤ 1096292925750043 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3731 c22250R_140_4 (by norm_num)

theorem c22250R_140_2 : rowsJ2 140 141 49 340 ≤ 1104331197633468 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3730 c22250R_140_3 (by norm_num)

theorem c22250R_140_1 : rowsJ2 140 141 25 340 ≤ 1108703330380566 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3729 c22250R_140_2 (by norm_num)

theorem c22250R_140_0 : rowsJ2 140 141 0 340 ≤ 1112323868922277 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_3728 c22250R_140_1 (by norm_num)

theorem hr22250R_140 : rows2 140 141 ≤ 1112323868922277 := rows2_le_of_rowsJ2 140 141 c22250R_140_0

theorem c22250R_141_23 : rowsJ2 141 142 76 340 ≤ 1082711440341294 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3777 rows22250R_3778 (by norm_num)

theorem c22250R_141_22 : rowsJ2 141 142 73 340 ≤ 1088545875926393 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3776 c22250R_141_23 (by norm_num)

theorem c22250R_141_21 : rowsJ2 141 142 71 340 ≤ 1095232922215902 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3775 c22250R_141_22 (by norm_num)

theorem c22250R_141_20 : rowsJ2 141 142 70 340 ≤ 1099609439224442 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3774 c22250R_141_21 (by norm_num)

theorem c22250R_141_19 : rowsJ2 141 142 69 340 ≤ 1104763203470963 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3773 c22250R_141_20 (by norm_num)

theorem c22250R_141_18 : rowsJ2 141 142 68 340 ≤ 1110762187257943 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3772 c22250R_141_19 (by norm_num)

theorem c22250R_141_17 : rowsJ2 141 142 67 340 ≤ 1117675723755192 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3771 c22250R_141_18 (by norm_num)

theorem c22250R_141_16 : rowsJ2 141 142 66 340 ≤ 1125553448828296 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3770 c22250R_141_17 (by norm_num)

theorem c22250R_141_15 : rowsJ2 141 142 65 340 ≤ 1134468200248532 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3769 c22250R_141_16 (by norm_num)

theorem c22250R_141_14 : rowsJ2 141 142 64 340 ≤ 1144473570531787 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3768 c22250R_141_15 (by norm_num)

theorem c22250R_141_13 : rowsJ2 141 142 63 340 ≤ 1155646341797199 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3767 c22250R_141_14 (by norm_num)

theorem c22250R_141_12 : rowsJ2 141 142 62 340 ≤ 1168044512407521 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3766 c22250R_141_13 (by norm_num)

theorem c22250R_141_11 : rowsJ2 141 142 61 340 ≤ 1180620830349455 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3765 c22250R_141_12 (by norm_num)

theorem c22250R_141_10 : rowsJ2 141 142 60 340 ≤ 1192213385976233 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3764 c22250R_141_11 (by norm_num)

theorem c22250R_141_9 : rowsJ2 141 142 59 340 ≤ 1202777690403652 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3763 c22250R_141_10 (by norm_num)

theorem c22250R_141_8 : rowsJ2 141 142 58 340 ≤ 1212331289352112 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3762 c22250R_141_9 (by norm_num)

theorem c22250R_141_7 : rowsJ2 141 142 57 340 ≤ 1220913536168484 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3761 c22250R_141_8 (by norm_num)

theorem c22250R_141_6 : rowsJ2 141 142 56 340 ≤ 1228565181150379 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3760 c22250R_141_7 (by norm_num)

theorem c22250R_141_5 : rowsJ2 141 142 55 340 ≤ 1235328500413586 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3759 c22250R_141_6 (by norm_num)

theorem c22250R_141_4 : rowsJ2 141 142 54 340 ≤ 1241247431653297 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3758 c22250R_141_5 (by norm_num)

theorem c22250R_141_3 : rowsJ2 141 142 52 340 ≤ 1250737056884332 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3757 c22250R_141_4 (by norm_num)

theorem c22250R_141_2 : rowsJ2 141 142 49 340 ≤ 1259849176680480 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3756 c22250R_141_3 (by norm_num)

theorem c22250R_141_1 : rowsJ2 141 142 26 340 ≤ 1265375392214870 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3755 c22250R_141_2 (by norm_num)

theorem c22250R_141_0 : rowsJ2 141 142 0 340 ≤ 1268274708467757 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_3754 c22250R_141_1 (by norm_num)

theorem hr22250R_141 : rows2 141 142 ≤ 1268274708467757 := rows2_le_of_rowsJ2 141 142 c22250R_141_0

theorem c22250R_142_23 : rowsJ2 142 143 74 340 ≤ 1140135495650985 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3802 rows22250R_3803 (by norm_num)

theorem c22250R_142_22 : rowsJ2 142 143 72 340 ≤ 1145092973236270 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3801 c22250R_142_23 (by norm_num)

theorem c22250R_142_21 : rowsJ2 142 143 70 340 ≤ 1152539828054522 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3800 c22250R_142_22 (by norm_num)

theorem c22250R_142_20 : rowsJ2 142 143 69 340 ≤ 1157362752354356 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3799 c22250R_142_21 (by norm_num)

theorem c22250R_142_19 : rowsJ2 142 143 68 340 ≤ 1163009511999917 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3798 c22250R_142_20 (by norm_num)

theorem c22250R_142_18 : rowsJ2 142 143 67 340 ≤ 1169549876758345 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3797 c22250R_142_19 (by norm_num)

theorem c22250R_142_17 : rowsJ2 142 143 66 340 ≤ 1177055069658687 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3796 c22250R_142_18 (by norm_num)

theorem c22250R_142_16 : rowsJ2 142 143 65 340 ≤ 1185597888672446 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3795 c22250R_142_17 (by norm_num)

theorem c22250R_142_15 : rowsJ2 142 143 64 340 ≤ 1195231998178388 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3794 c22250R_142_16 (by norm_num)

theorem c22250R_142_14 : rowsJ2 142 143 63 340 ≤ 1206034140012954 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3793 c22250R_142_15 (by norm_num)

theorem c22250R_142_13 : rowsJ2 142 143 62 340 ≤ 1218062382864732 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3792 c22250R_142_14 (by norm_num)

theorem c22250R_142_12 : rowsJ2 142 143 61 340 ≤ 1231397903414089 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3791 c22250R_142_13 (by norm_num)

theorem c22250R_142_11 : rowsJ2 142 143 60 340 ≤ 1243713935305448 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3790 c22250R_142_12 (by norm_num)

theorem c22250R_142_10 : rowsJ2 142 143 59 340 ≤ 1254966399513551 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3789 c22250R_142_11 (by norm_num)

theorem c22250R_142_9 : rowsJ2 142 143 58 340 ≤ 1265172886399904 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3788 c22250R_142_10 (by norm_num)

theorem c22250R_142_8 : rowsJ2 142 143 57 340 ≤ 1274372642278444 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3787 c22250R_142_9 (by norm_num)

theorem c22250R_142_7 : rowsJ2 142 143 56 340 ≤ 1282606267339095 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3786 c22250R_142_8 (by norm_num)

theorem c22250R_142_6 : rowsJ2 142 143 55 340 ≤ 1289915844349244 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3785 c22250R_142_7 (by norm_num)

theorem c22250R_142_5 : rowsJ2 142 143 54 340 ≤ 1296345074107861 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3784 c22250R_142_6 (by norm_num)

theorem c22250R_142_4 : rowsJ2 142 143 53 340 ≤ 1301939418311725 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3783 c22250R_142_5 (by norm_num)

theorem c22250R_142_3 : rowsJ2 142 143 51 340 ≤ 1310815016114129 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3782 c22250R_142_4 (by norm_num)

theorem c22250R_142_2 : rowsJ2 142 143 49 340 ≤ 1316947515202761 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3781 c22250R_142_3 (by norm_num)

theorem c22250R_142_1 : rowsJ2 142 143 28 340 ≤ 1323643004132321 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3780 c22250R_142_2 (by norm_num)

theorem c22250R_142_0 : rowsJ2 142 143 0 340 ≤ 1325661602878675 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_3779 c22250R_142_1 (by norm_num)

theorem hr22250R_142 : rows2 142 143 ≤ 1325661602878675 := rows2_le_of_rowsJ2 142 143 c22250R_142_0

theorem c22250R_143_23 : rowsJ2 143 144 75 340 ≤ 1284827022068752 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3827 rows22250R_3828 (by norm_num)

theorem c22250R_143_22 : rowsJ2 143 144 72 340 ≤ 1290845901566805 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3826 c22250R_143_23 (by norm_num)

theorem c22250R_143_21 : rowsJ2 143 144 70 340 ≤ 1297744734890090 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3825 c22250R_143_22 (by norm_num)

theorem c22250R_143_20 : rowsJ2 143 144 69 340 ≤ 1302260084395145 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3824 c22250R_143_21 (by norm_num)

theorem c22250R_143_19 : rowsJ2 143 144 68 340 ≤ 1307577555412659 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3823 c22250R_143_20 (by norm_num)

theorem c22250R_143_18 : rowsJ2 143 144 67 340 ≤ 1313767381714467 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3822 c22250R_143_19 (by norm_num)

theorem c22250R_143_17 : rowsJ2 143 144 66 340 ≤ 1320901225596519 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3821 c22250R_143_18 (by norm_num)

theorem c22250R_143_16 : rowsJ2 143 144 65 340 ≤ 1329052300622336 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3820 c22250R_143_17 (by norm_num)

theorem c22250R_143_15 : rowsJ2 143 144 64 340 ≤ 1338295499200404 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3819 c22250R_143_16 (by norm_num)

theorem c22250R_143_14 : rowsJ2 143 144 63 340 ≤ 1348707525498323 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3818 c22250R_143_15 (by norm_num)

theorem c22250R_143_13 : rowsJ2 143 144 62 340 ≤ 1360346520114860 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3817 c22250R_143_14 (by norm_num)

theorem c22250R_143_12 : rowsJ2 143 144 61 340 ≤ 1373293622107758 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3816 c22250R_143_13 (by norm_num)

theorem c22250R_143_11 : rowsJ2 143 144 60 340 ≤ 1386382390908374 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3815 c22250R_143_12 (by norm_num)

theorem c22250R_143_10 : rowsJ2 143 144 59 340 ≤ 1398371785691815 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3814 c22250R_143_11 (by norm_num)

theorem c22250R_143_9 : rowsJ2 143 144 58 340 ≤ 1409279471016611 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3813 c22250R_143_10 (by norm_num)

theorem c22250R_143_8 : rowsJ2 143 144 57 340 ≤ 1419144615716808 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3812 c22250R_143_9 (by norm_num)

theorem c22250R_143_7 : rowsJ2 143 144 56 340 ≤ 1428007698380791 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3811 c22250R_143_8 (by norm_num)

theorem c22250R_143_6 : rowsJ2 143 144 55 340 ≤ 1435910635979385 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3810 c22250R_143_7 (by norm_num)

theorem c22250R_143_5 : rowsJ2 143 144 54 340 ≤ 1442896919099832 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3809 c22250R_143_6 (by norm_num)

theorem c22250R_143_4 : rowsJ2 143 144 53 340 ≤ 1449011754445837 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3808 c22250R_143_5 (by norm_num)

theorem c22250R_143_3 : rowsJ2 143 144 51 340 ≤ 1458817400773857 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3807 c22250R_143_4 (by norm_num)

theorem c22250R_143_2 : rowsJ2 143 144 49 340 ≤ 1465729493675784 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3806 c22250R_143_3 (by norm_num)

theorem c22250R_143_1 : rowsJ2 143 144 42 340 ≤ 1473907588069398 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3805 c22250R_143_2 (by norm_num)

theorem c22250R_143_0 : rowsJ2 143 144 0 340 ≤ 1475522067301431 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_3804 c22250R_143_1 (by norm_num)

theorem hr22250R_143 : rows2 143 144 ≤ 1475522067301431 := rows2_le_of_rowsJ2 143 144 c22250R_143_0

theorem c22250R_144_23 : rowsJ2 144 145 73 340 ≤ 1332791884820159 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3852 rows22250R_3853 (by norm_num)

theorem c22250R_144_22 : rowsJ2 144 145 71 340 ≤ 1337907582043269 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3851 c22250R_144_23 (by norm_num)

theorem c22250R_144_21 : rowsJ2 144 145 69 340 ≤ 1345592540854185 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3850 c22250R_144_22 (by norm_num)

theorem c22250R_144_20 : rowsJ2 144 145 68 340 ≤ 1350569942281163 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3849 c22250R_144_21 (by norm_num)

theorem c22250R_144_19 : rowsJ2 144 145 67 340 ≤ 1356397825663026 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3848 c22250R_144_20 (by norm_num)

theorem c22250R_144_18 : rowsJ2 144 145 66 340 ≤ 1363148314853052 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3847 c22250R_144_19 (by norm_num)

theorem c22250R_144_17 : rowsJ2 144 145 65 340 ≤ 1370895060220521 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3846 c22250R_144_18 (by norm_num)

theorem c22250R_144_16 : rowsJ2 144 145 64 340 ≤ 1379713367291444 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3845 c22250R_144_17 (by norm_num)

theorem c22250R_144_15 : rowsJ2 144 145 63 340 ≤ 1389680330658641 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3844 c22250R_144_16 (by norm_num)

theorem c22250R_144_14 : rowsJ2 144 145 62 340 ≤ 1400874973701396 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3843 c22250R_144_15 (by norm_num)

theorem c22250R_144_13 : rowsJ2 144 145 61 340 ≤ 1413378394691621 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3842 c22250R_144_14 (by norm_num)

theorem c22250R_144_12 : rowsJ2 144 145 60 340 ≤ 1427253709096797 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3841 c22250R_144_13 (by norm_num)

theorem c22250R_144_11 : rowsJ2 144 145 59 340 ≤ 1439992972167210 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3840 c22250R_144_12 (by norm_num)

theorem c22250R_144_10 : rowsJ2 144 145 58 340 ≤ 1451613947277751 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3839 c22250R_144_11 (by norm_num)

theorem c22250R_144_9 : rowsJ2 144 145 57 340 ≤ 1462155750079260 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3838 c22250R_144_10 (by norm_num)

theorem c22250R_144_8 : rowsJ2 144 145 56 340 ≤ 1471658760507473 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3837 c22250R_144_9 (by norm_num)

theorem c22250R_144_7 : rowsJ2 144 145 55 340 ≤ 1480164751430259 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3836 c22250R_144_8 (by norm_num)

theorem c22250R_144_6 : rowsJ2 144 145 54 340 ≤ 1487717023747175 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3835 c22250R_144_7 (by norm_num)

theorem c22250R_144_5 : rowsJ2 144 145 53 340 ≤ 1494360548602909 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3834 c22250R_144_6 (by norm_num)

theorem c22250R_144_4 : rowsJ2 144 145 52 340 ≤ 1500142117421020 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3833 c22250R_144_5 (by norm_num)

theorem c22250R_144_3 : rowsJ2 144 145 51 340 ≤ 1505110500514862 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3832 c22250R_144_4 (by norm_num)

theorem c22250R_144_2 : rowsJ2 144 145 49 340 ≤ 1512813703503390 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3831 c22250R_144_3 (by norm_num)

theorem c22250R_144_1 : rowsJ2 144 145 43 340 ≤ 1522231682438987 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3830 c22250R_144_2 (by norm_num)

theorem c22250R_144_0 : rowsJ2 144 145 0 340 ≤ 1523543695555388 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_3829 c22250R_144_1 (by norm_num)

theorem hr22250R_144 : rows2 144 145 ≤ 1523543695555388 := rows2_le_of_rowsJ2 144 145 c22250R_144_0

theorem c22250R_145_23 : rowsJ2 145 146 74 340 ≤ 1471740584507235 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3877 rows22250R_3878 (by norm_num)

theorem c22250R_145_22 : rowsJ2 145 146 71 340 ≤ 1477953203222186 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3876 c22250R_145_23 (by norm_num)

theorem c22250R_145_21 : rowsJ2 145 146 69 340 ≤ 1485074511877179 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3875 c22250R_145_22 (by norm_num)

theorem c22250R_145_20 : rowsJ2 145 146 68 340 ≤ 1489735709558187 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3874 c22250R_145_21 (by norm_num)

theorem c22250R_145_19 : rowsJ2 145 146 67 340 ≤ 1495225169270331 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3873 c22250R_145_20 (by norm_num)

theorem c22250R_145_18 : rowsJ2 145 146 66 340 ≤ 1501615505216529 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3872 c22250R_145_19 (by norm_num)

theorem c22250R_145_17 : rowsJ2 145 146 65 340 ≤ 1508980832360258 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3871 c22250R_145_18 (by norm_num)

theorem c22250R_145_16 : rowsJ2 145 146 64 340 ≤ 1517396896207326 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3870 c22250R_145_17 (by norm_num)

theorem c22250R_145_15 : rowsJ2 145 146 63 340 ≤ 1526941207785491 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3869 c22250R_145_16 (by norm_num)

theorem c22250R_145_14 : rowsJ2 145 146 62 340 ≤ 1537693184366837 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3868 c22250R_145_15 (by norm_num)

theorem c22250R_145_13 : rowsJ2 145 146 61 340 ≤ 1549734296514092 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3867 c22250R_145_14 (by norm_num)

theorem c22250R_145_12 : rowsJ2 145 146 60 340 ≤ 1563148222073299 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3866 c22250R_145_13 (by norm_num)

theorem c22250R_145_11 : rowsJ2 145 146 59 340 ≤ 1576688655734165 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3865 c22250R_145_12 (by norm_num)

theorem c22250R_145_10 : rowsJ2 145 146 58 340 ≤ 1589073694361741 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3864 c22250R_145_11 (by norm_num)

theorem c22250R_145_9 : rowsJ2 145 146 57 340 ≤ 1600342433162775 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3863 c22250R_145_10 (by norm_num)

theorem c22250R_145_8 : rowsJ2 145 146 56 340 ≤ 1610535184896399 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3862 c22250R_145_9 (by norm_num)

theorem c22250R_145_7 : rowsJ2 145 146 55 340 ≤ 1619693608649389 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3861 c22250R_145_8 (by norm_num)

theorem c22250R_145_6 : rowsJ2 145 146 54 340 ≤ 1627860844902700 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3860 c22250R_145_7 (by norm_num)

theorem c22250R_145_5 : rowsJ2 145 146 53 340 ≤ 1635081657553314 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3859 c22250R_145_6 (by norm_num)

theorem c22250R_145_4 : rowsJ2 145 146 52 340 ≤ 1641402583598884 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3858 c22250R_145_5 (by norm_num)

theorem c22250R_145_3 : rowsJ2 145 146 50 340 ≤ 1651540747227013 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3857 c22250R_145_4 (by norm_num)

theorem c22250R_145_2 : rowsJ2 145 146 48 340 ≤ 1658689339602979 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3856 c22250R_145_3 (by norm_num)

theorem c22250R_145_1 : rowsJ2 145 146 44 340 ≤ 1665878113979633 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3855 c22250R_145_2 (by norm_num)

theorem c22250R_145_0 : rowsJ2 145 146 0 340 ≤ 1667843296492592 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_3854 c22250R_145_1 (by norm_num)

theorem hr22250R_145 : rows2 145 146 ≤ 1667843296492592 := rows2_le_of_rowsJ2 145 146 c22250R_145_0

theorem c22250R_146_22 : rowsJ2 146 147 73 340 ≤ 1509552631387430 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3901 rows22250R_3902 (by norm_num)

theorem c22250R_146_21 : rowsJ2 146 147 70 340 ≤ 1516653626817098 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3900 c22250R_146_22 (by norm_num)

theorem c22250R_146_20 : rowsJ2 146 147 68 340 ≤ 1524588771212253 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3899 c22250R_146_21 (by norm_num)

theorem c22250R_146_19 : rowsJ2 146 147 67 340 ≤ 1529728499486551 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3898 c22250R_146_20 (by norm_num)

theorem c22250R_146_18 : rowsJ2 146 147 66 340 ≤ 1535746721606393 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3897 c22250R_146_19 (by norm_num)

theorem c22250R_146_17 : rowsJ2 146 147 65 340 ≤ 1542718040544864 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3896 c22250R_146_18 (by norm_num)

theorem c22250R_146_16 : rowsJ2 146 147 64 340 ≤ 1550718664056885 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3895 c22250R_146_17 (by norm_num)

theorem c22250R_146_15 : rowsJ2 146 147 63 340 ≤ 1559826540801301 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3894 c22250R_146_16 (by norm_num)

theorem c22250R_146_14 : rowsJ2 146 147 62 340 ≤ 1570121502134283 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3893 c22250R_146_15 (by norm_num)

theorem c22250R_146_13 : rowsJ2 146 147 61 340 ≤ 1581685410160269 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3892 c22250R_146_14 (by norm_num)

theorem c22250R_146_12 : rowsJ2 146 147 60 340 ≤ 1594602312666936 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3891 c22250R_146_13 (by norm_num)

theorem c22250R_146_11 : rowsJ2 146 147 59 340 ≤ 1608958605616830 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3890 c22250R_146_12 (by norm_num)

theorem c22250R_146_10 : rowsJ2 146 147 58 340 ≤ 1622121469059183 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3889 c22250R_146_11 (by norm_num)

theorem c22250R_146_9 : rowsJ2 146 147 57 340 ≤ 1634130005343757 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3888 c22250R_146_10 (by norm_num)

theorem c22250R_146_8 : rowsJ2 146 147 56 340 ≤ 1645024486051422 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3887 c22250R_146_9 (by norm_num)

theorem c22250R_146_7 : rowsJ2 146 147 55 340 ≤ 1654846481007661 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3886 c22250R_146_8 (by norm_num)

theorem c22250R_146_6 : rowsJ2 146 147 54 340 ≤ 1663638993417913 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3885 c22250R_146_7 (by norm_num)

theorem c22250R_146_5 : rowsJ2 146 147 53 340 ≤ 1671446601791817 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3884 c22250R_146_6 (by norm_num)

theorem c22250R_146_4 : rowsJ2 146 147 52 340 ≤ 1678315609365850 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3883 c22250R_146_5 (by norm_num)

theorem c22250R_146_3 : rowsJ2 146 147 50 340 ≤ 1689432613834385 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3882 c22250R_146_4 (by norm_num)

theorem c22250R_146_2 : rowsJ2 146 147 48 340 ≤ 1697401152786294 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3881 c22250R_146_3 (by norm_num)

theorem c22250R_146_1 : rowsJ2 146 147 44 340 ≤ 1705737575982018 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3880 c22250R_146_2 (by norm_num)

theorem c22250R_146_0 : rowsJ2 146 147 0 340 ≤ 1707843760213596 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_3879 c22250R_146_1 (by norm_num)

theorem hr22250R_146 : rows2 146 147 ≤ 1707843760213596 := rows2_le_of_rowsJ2 146 147 c22250R_146_0

theorem c22250R_147_22 : rowsJ2 147 148 71 340 ≤ 1641186267944393 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3925 rows22250R_3926 (by norm_num)

theorem c22250R_147_21 : rowsJ2 147 148 69 340 ≤ 1647193129975143 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3924 c22250R_147_22 (by norm_num)

theorem c22250R_147_20 : rowsJ2 147 148 67 340 ≤ 1656040040886716 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3923 c22250R_147_21 (by norm_num)

theorem c22250R_147_19 : rowsJ2 147 148 66 340 ≤ 1661710279140832 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3922 c22250R_147_20 (by norm_num)

theorem c22250R_147_18 : rowsJ2 147 148 65 340 ≤ 1668311385717713 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3921 c22250R_147_19 (by norm_num)

theorem c22250R_147_17 : rowsJ2 147 148 64 340 ≤ 1675920059822740 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3920 c22250R_147_18 (by norm_num)

theorem c22250R_147_16 : rowsJ2 147 148 63 340 ≤ 1684614715960769 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3919 c22250R_147_17 (by norm_num)

theorem c22250R_147_15 : rowsJ2 147 148 62 340 ≤ 1694475626879553 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3918 c22250R_147_16 (by norm_num)

theorem c22250R_147_14 : rowsJ2 147 148 61 340 ≤ 1705585072699973 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3917 c22250R_147_15 (by norm_num)

theorem c22250R_147_13 : rowsJ2 147 148 60 340 ≤ 1718027496864362 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3916 c22250R_147_14 (by norm_num)

theorem c22250R_147_12 : rowsJ2 147 148 59 340 ≤ 1731889669579904 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3915 c22250R_147_13 (by norm_num)

theorem c22250R_147_11 : rowsJ2 147 148 58 340 ≤ 1745883822581358 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3914 c22250R_147_12 (by norm_num)

theorem c22250R_147_10 : rowsJ2 147 148 57 340 ≤ 1758685051920638 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3913 c22250R_147_11 (by norm_num)

theorem c22250R_147_9 : rowsJ2 147 148 56 340 ≤ 1770333622965843 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3912 c22250R_147_10 (by norm_num)

theorem c22250R_147_8 : rowsJ2 147 148 55 340 ≤ 1780871049853840 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3911 c22250R_147_9 (by norm_num)

theorem c22250R_147_7 : rowsJ2 147 148 54 340 ≤ 1790340230813998 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3910 c22250R_147_8 (by norm_num)

theorem c22250R_147_6 : rowsJ2 147 148 53 340 ≤ 1798785590106186 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3909 c22250R_147_7 (by norm_num)

theorem c22250R_147_5 : rowsJ2 147 148 52 340 ≤ 1806253227285459 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3908 c22250R_147_6 (by norm_num)

theorem c22250R_147_4 : rowsJ2 147 148 51 340 ≤ 1812791074552651 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3907 c22250R_147_5 (by norm_num)

theorem c22250R_147_3 : rowsJ2 147 148 50 340 ≤ 1818449063003013 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3906 c22250R_147_4 (by norm_num)

theorem c22250R_147_2 : rowsJ2 147 148 48 340 ≤ 1827336249125632 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3905 c22250R_147_3 (by norm_num)

theorem c22250R_147_1 : rowsJ2 147 148 44 340 ≤ 1837014691384197 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3904 c22250R_147_2 (by norm_num)

theorem c22250R_147_0 : rowsJ2 147 148 0 340 ≤ 1839652158126851 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_3903 c22250R_147_1 (by norm_num)

theorem hr22250R_147 : rows2 147 148 ≤ 1839652158126851 := rows2_le_of_rowsJ2 147 148 c22250R_147_0

theorem c22250R_148_22 : rowsJ2 148 149 72 340 ≤ 1757573313177467 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3949 rows22250R_3950 (by norm_num)

theorem c22250R_148_21 : rowsJ2 148 149 69 340 ≤ 1764909176178091 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3948 c22250R_148_22 (by norm_num)

theorem c22250R_148_20 : rowsJ2 148 149 67 340 ≤ 1773107331712987 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3947 c22250R_148_21 (by norm_num)

theorem c22250R_148_19 : rowsJ2 148 149 66 340 ≤ 1778417720825117 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3946 c22250R_148_20 (by norm_num)

theorem c22250R_148_18 : rowsJ2 148 149 65 340 ≤ 1784636066070316 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3945 c22250R_148_19 (by norm_num)

theorem c22250R_148_17 : rowsJ2 148 149 64 340 ≤ 1791839582721358 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3944 c22250R_148_18 (by norm_num)

theorem c22250R_148_16 : rowsJ2 148 149 63 340 ≤ 1800107174525354 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3943 c22250R_148_17 (by norm_num)

theorem c22250R_148_15 : rowsJ2 148 149 62 340 ≤ 1809519577875364 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3942 c22250R_148_16 (by norm_num)

theorem c22250R_148_14 : rowsJ2 148 149 61 340 ≤ 1820159512093217 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3941 c22250R_148_15 (by norm_num)

theorem c22250R_148_13 : rowsJ2 148 149 60 340 ≤ 1832111836460160 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3940 c22250R_148_14 (by norm_num)

theorem c22250R_148_12 : rowsJ2 148 149 59 340 ≤ 1845463714677060 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3939 c22250R_148_13 (by norm_num)

theorem c22250R_148_11 : rowsJ2 148 149 58 340 ≤ 1860304787486407 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3938 c22250R_148_12 (by norm_num)

theorem c22250R_148_10 : rowsJ2 148 149 57 340 ≤ 1873913353249895 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3937 c22250R_148_11 (by norm_num)

theorem c22250R_148_9 : rowsJ2 148 149 56 340 ≤ 1886329700731233 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3936 c22250R_148_10 (by norm_num)

theorem c22250R_148_8 : rowsJ2 148 149 55 340 ≤ 1897595316242105 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3935 c22250R_148_9 (by norm_num)

theorem c22250R_148_7 : rowsJ2 148 149 54 340 ≤ 1907753019276046 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3934 c22250R_148_8 (by norm_num)

theorem c22250R_148_6 : rowsJ2 148 149 53 340 ≤ 1916847104572308 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3933 c22250R_148_7 (by norm_num)

theorem c22250R_148_5 : rowsJ2 148 149 52 340 ≤ 1924923491325945 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3932 c22250R_148_6 (by norm_num)

theorem c22250R_148_4 : rowsJ2 148 149 51 340 ≤ 1932029880305832 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3931 c22250R_148_5 (by norm_num)

theorem c22250R_148_3 : rowsJ2 148 149 50 340 ≤ 1938215919693906 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3930 c22250R_148_4 (by norm_num)

theorem c22250R_148_2 : rowsJ2 148 149 48 340 ≤ 1948036342611299 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3929 c22250R_148_3 (by norm_num)

theorem c22250R_148_1 : rowsJ2 148 149 44 340 ≤ 1959077032146736 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3928 c22250R_148_2 (by norm_num)

theorem c22250R_148_0 : rowsJ2 148 149 0 340 ≤ 1962254628390755 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_3927 c22250R_148_1 (by norm_num)

theorem hr22250R_148 : rows2 148 149 ≤ 1962254628390755 := rows2_le_of_rowsJ2 148 149 c22250R_148_0

theorem c22250R_149_22 : rowsJ2 149 150 70 340 ≤ 1886422829986312 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3973 rows22250R_3974 (by norm_num)

theorem c22250R_149_21 : rowsJ2 149 150 68 340 ≤ 1892630299207356 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3972 c22250R_149_22 (by norm_num)

theorem c22250R_149_20 : rowsJ2 149 150 66 340 ≤ 1901773265302750 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3971 c22250R_149_21 (by norm_num)

theorem c22250R_149_19 : rowsJ2 149 150 65 340 ≤ 1907633618283767 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3970 c22250R_149_20 (by norm_num)

theorem c22250R_149_18 : rowsJ2 149 150 64 340 ≤ 1914456395326274 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3969 c22250R_149_19 (by norm_num)

theorem c22250R_149_17 : rowsJ2 149 150 63 340 ≤ 1922321020130075 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3968 c22250R_149_18 (by norm_num)

theorem c22250R_149_16 : rowsJ2 149 150 62 340 ≤ 1931308722392930 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3967 c22250R_149_17 (by norm_num)

theorem c22250R_149_15 : rowsJ2 149 150 61 340 ≤ 1941502689330648 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3966 c22250R_149_16 (by norm_num)

theorem c22250R_149_14 : rowsJ2 149 150 60 340 ≤ 1952988223870173 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3965 c22250R_149_15 (by norm_num)

theorem c22250R_149_13 : rowsJ2 149 150 59 340 ≤ 1965852910202656 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3964 c22250R_149_14 (by norm_num)

theorem c22250R_149_12 : rowsJ2 149 150 58 340 ≤ 1980186787433590 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3963 c22250R_149_13 (by norm_num)

theorem c22250R_149_11 : rowsJ2 149 150 57 340 ≤ 1994658447818333 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3962 c22250R_149_12 (by norm_num)

theorem c22250R_149_10 : rowsJ2 149 150 56 340 ≤ 2007897716845024 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3961 c22250R_149_11 (by norm_num)

theorem c22250R_149_9 : rowsJ2 149 150 55 340 ≤ 2019946090398602 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3960 c22250R_149_10 (by norm_num)

theorem c22250R_149_8 : rowsJ2 149 150 54 340 ≤ 2030846345098053 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3959 c22250R_149_9 (by norm_num)

theorem c22250R_149_7 : rowsJ2 149 150 53 340 ≤ 2040642680617868 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3958 c22250R_149_8 (by norm_num)

theorem c22250R_149_6 : rowsJ2 149 150 52 340 ≤ 2049380868966068 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3957 c22250R_149_7 (by norm_num)

theorem c22250R_149_5 : rowsJ2 149 150 51 340 ≤ 2057108411483836 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3956 c22250R_149_6 (by norm_num)

theorem c22250R_149_4 : rowsJ2 149 150 50 340 ≤ 2063874704382198 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3955 c22250R_149_5 (by norm_num)

theorem c22250R_149_3 : rowsJ2 149 150 49 340 ≤ 2069731213688318 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3954 c22250R_149_4 (by norm_num)

theorem c22250R_149_2 : rowsJ2 149 150 47 340 ≤ 2078932217823250 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3953 c22250R_149_3 (by norm_num)

theorem c22250R_149_1 : rowsJ2 149 150 44 340 ≤ 2087337545145358 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3952 c22250R_149_2 (by norm_num)

theorem c22250R_149_0 : rowsJ2 149 150 0 340 ≤ 2091519181994916 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_3951 c22250R_149_1 (by norm_num)

theorem hr22250R_149 : rows2 149 150 ≤ 2091519181994916 := rows2_le_of_rowsJ2 149 150 c22250R_149_0

theorem c22250R_150_22 : rowsJ2 150 151 71 340 ≤ 2007478254783189 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3997 rows22250R_3998 (by norm_num)

theorem c22250R_150_21 : rowsJ2 150 151 68 340 ≤ 2015061132354263 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3996 c22250R_150_22 (by norm_num)

theorem c22250R_150_20 : rowsJ2 150 151 66 340 ≤ 2023535924972188 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3995 c22250R_150_21 (by norm_num)

theorem c22250R_150_19 : rowsJ2 150 151 65 340 ≤ 2029025829983737 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3994 c22250R_150_20 (by norm_num)

theorem c22250R_150_18 : rowsJ2 150 151 64 340 ≤ 2035454695468342 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3993 c22250R_150_19 (by norm_num)

theorem c22250R_150_17 : rowsJ2 150 151 63 340 ≤ 2042902490979475 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3992 c22250R_150_18 (by norm_num)

theorem c22250R_150_16 : rowsJ2 150 151 62 340 ≤ 2051450964119645 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3991 c22250R_150_17 (by norm_num)

theorem c22250R_150_15 : rowsJ2 150 151 61 340 ≤ 2061183793381694 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3990 c22250R_150_16 (by norm_num)

theorem c22250R_150_14 : rowsJ2 150 151 60 340 ≤ 2072186747583097 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3989 c22250R_150_15 (by norm_num)

theorem c22250R_150_13 : rowsJ2 150 151 59 340 ≤ 2084547852585778 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3988 c22250R_150_14 (by norm_num)

theorem c22250R_150_12 : rowsJ2 150 151 58 340 ≤ 2098357566043983 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3987 c22250R_150_13 (by norm_num)

theorem c22250R_150_11 : rowsJ2 150 151 57 340 ≤ 2113708960978826 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3986 c22250R_150_12 (by norm_num)

theorem c22250R_150_10 : rowsJ2 150 151 56 340 ≤ 2127786740549140 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3985 c22250R_150_11 (by norm_num)

theorem c22250R_150_9 : rowsJ2 150 151 55 340 ≤ 2140632442041664 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3984 c22250R_150_10 (by norm_num)

theorem c22250R_150_8 : rowsJ2 150 151 54 340 ≤ 2152288829111157 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3983 c22250R_150_9 (by norm_num)

theorem c22250R_150_7 : rowsJ2 150 151 53 340 ≤ 2162800034494051 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3982 c22250R_150_8 (by norm_num)

theorem c22250R_150_6 : rowsJ2 150 151 52 340 ≤ 2172211709478115 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3981 c22250R_150_7 (by norm_num)

theorem c22250R_150_5 : rowsJ2 150 151 51 340 ≤ 2180571180897508 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3980 c22250R_150_6 (by norm_num)

theorem c22250R_150_4 : rowsJ2 150 151 50 340 ≤ 2187927616472010 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3979 c22250R_150_5 (by norm_num)

theorem c22250R_150_3 : rowsJ2 150 151 49 340 ≤ 2194332199364380 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3978 c22250R_150_4 (by norm_num)

theorem c22250R_150_2 : rowsJ2 150 151 47 340 ≤ 2204501736406899 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3977 c22250R_150_3 (by norm_num)

theorem c22250R_150_1 : rowsJ2 150 151 44 340 ≤ 2214034066717392 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3976 c22250R_150_2 (by norm_num)

theorem c22250R_150_0 : rowsJ2 150 151 0 340 ≤ 2219234363194686 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_3975 c22250R_150_1 (by norm_num)

theorem hr22250R_150 : rows2 150 151 ≤ 2219234363194686 := rows2_le_of_rowsJ2 150 151 c22250R_150_0

theorem c22250R_151_22 : rowsJ2 151 152 69 340 ≤ 2125868602250365 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4021 rows22250R_4022 (by norm_num)

theorem c22250R_151_21 : rowsJ2 151 152 67 340 ≤ 2132287115254078 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4020 c22250R_151_22 (by norm_num)

theorem c22250R_151_20 : rowsJ2 151 152 65 340 ≤ 2141741565225870 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4019 c22250R_151_21 (by norm_num)

theorem c22250R_151_19 : rowsJ2 151 152 64 340 ≤ 2147801957244275 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4018 c22250R_151_20 (by norm_num)

theorem c22250R_151_18 : rowsJ2 151 152 63 340 ≤ 2154857992388266 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4017 c22250R_151_19 (by norm_num)

theorem c22250R_151_17 : rowsJ2 151 152 62 340 ≤ 2162991968488451 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4016 c22250R_151_18 (by norm_num)

theorem c22250R_151_16 : rowsJ2 151 152 61 340 ≤ 2172288086517622 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4015 c22250R_151_17 (by norm_num)

theorem c22250R_151_15 : rowsJ2 151 152 60 340 ≤ 2182832611357039 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4014 c22250R_151_16 (by norm_num)

theorem c22250R_151_14 : rowsJ2 151 152 59 340 ≤ 2194714039769065 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4013 c22250R_151_15 (by norm_num)

theorem c22250R_151_13 : rowsJ2 151 152 58 340 ≤ 2208023276324435 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4012 c22250R_151_14 (by norm_num)

theorem c22250R_151_12 : rowsJ2 151 152 57 340 ≤ 2222853818088048 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4011 c22250R_151_13 (by norm_num)

theorem c22250R_151_11 : rowsJ2 151 152 56 340 ≤ 2237828300769886 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4010 c22250R_151_12 (by norm_num)

theorem c22250R_151_10 : rowsJ2 151 152 55 340 ≤ 2251528862128910 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4009 c22250R_151_11 (by norm_num)

theorem c22250R_151_9 : rowsJ2 151 152 54 340 ≤ 2263998292916035 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4008 c22250R_151_10 (by norm_num)

theorem c22250R_151_8 : rowsJ2 151 152 53 340 ≤ 2275280697292298 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4007 c22250R_151_9 (by norm_num)

theorem c22250R_151_7 : rowsJ2 151 152 52 340 ≤ 2285421642635437 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4006 c22250R_151_8 (by norm_num)

theorem c22250R_151_6 : rowsJ2 151 152 51 340 ≤ 2294468316665462 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4005 c22250R_151_7 (by norm_num)

theorem c22250R_151_5 : rowsJ2 151 152 50 340 ≤ 2302469692711916 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4004 c22250R_151_6 (by norm_num)

theorem c22250R_151_4 : rowsJ2 151 152 49 340 ≤ 2309476703999579 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4003 c22250R_151_5 (by norm_num)

theorem c22250R_151_3 : rowsJ2 151 152 48 340 ≤ 2315542427890893 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4002 c22250R_151_4 (by norm_num)

theorem c22250R_151_2 : rowsJ2 151 152 46 340 ≤ 2325074226912061 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4001 c22250R_151_3 (by norm_num)

theorem c22250R_151_1 : rowsJ2 151 152 43 340 ≤ 2333785185064506 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4000 c22250R_151_2 (by norm_num)

theorem c22250R_151_0 : rowsJ2 151 152 0 340 ≤ 2338121584931752 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_3999 c22250R_151_1 (by norm_num)

theorem hr22250R_151 : rows2 151 152 ≤ 2338121584931752 := rows2_le_of_rowsJ2 151 152 c22250R_151_0

theorem c22250R_152_21 : rowsJ2 152 153 68 340 ≤ 2248663077411115 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4044 rows22250R_4045 (by norm_num)

theorem c22250R_152_20 : rowsJ2 152 153 66 340 ≤ 2255885441065856 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4043 c22250R_152_21 (by norm_num)

theorem c22250R_152_19 : rowsJ2 152 153 64 340 ≤ 2266352666705897 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4042 c22250R_152_20 (by norm_num)

theorem c22250R_152_18 : rowsJ2 152 153 63 340 ≤ 2273003109446670 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4041 c22250R_152_19 (by norm_num)

theorem c22250R_152_17 : rowsJ2 152 153 62 340 ≤ 2280708033166855 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4040 c22250R_152_18 (by norm_num)

theorem c22250R_152_16 : rowsJ2 152 153 61 340 ≤ 2289552187206014 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4039 c22250R_152_17 (by norm_num)

theorem c22250R_152_15 : rowsJ2 152 153 60 340 ≤ 2299622357099072 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4038 c22250R_152_16 (by norm_num)

theorem c22250R_152_14 : rowsJ2 152 153 59 340 ≤ 2311007533886296 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4037 c22250R_152_15 (by norm_num)

theorem c22250R_152_13 : rowsJ2 152 153 58 340 ≤ 2323799091299271 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4036 c22250R_152_14 (by norm_num)

theorem c22250R_152_12 : rowsJ2 152 153 57 340 ≤ 2338090971632617 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4035 c22250R_152_13 (by norm_num)

theorem c22250R_152_11 : rowsJ2 152 153 56 340 ≤ 2353979881173747 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4034 c22250R_152_12 (by norm_num)

theorem c22250R_152_10 : rowsJ2 152 153 55 340 ≤ 2368551906164115 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4033 c22250R_152_11 (by norm_num)

theorem c22250R_152_9 : rowsJ2 152 153 54 340 ≤ 2381849898721367 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4032 c22250R_152_10 (by norm_num)

theorem c22250R_152_8 : rowsJ2 152 153 53 340 ≤ 2393917966590732 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4031 c22250R_152_9 (by norm_num)

theorem c22250R_152_7 : rowsJ2 152 153 52 340 ≤ 2404801623437770 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4030 c22250R_152_8 (by norm_num)

theorem c22250R_152_6 : rowsJ2 152 153 51 340 ≤ 2414547946241105 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4029 c22250R_152_7 (by norm_num)

theorem c22250R_152_5 : rowsJ2 152 153 50 340 ≤ 2423205740613411 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4028 c22250R_152_6 (by norm_num)

theorem c22250R_152_4 : rowsJ2 152 153 49 340 ≤ 2430825714931217 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4027 c22250R_152_5 (by norm_num)

theorem c22250R_152_3 : rowsJ2 152 153 48 340 ≤ 2437460664213901 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4026 c22250R_152_4 (by norm_num)

theorem c22250R_152_2 : rowsJ2 152 153 46 340 ≤ 2447998280626303 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4025 c22250R_152_3 (by norm_num)

theorem c22250R_152_1 : rowsJ2 152 153 43 340 ≤ 2457879487736222 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4024 c22250R_152_2 (by norm_num)

theorem c22250R_152_0 : rowsJ2 152 153 0 340 ≤ 2463273538244763 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4023 c22250R_152_1 (by norm_num)

theorem hr22250R_152 : rows2 152 153 ≤ 2463273538244763 := rows2_le_of_rowsJ2 152 153 c22250R_152_0

theorem c22250R_153_21 : rowsJ2 153 154 69 340 ≤ 2365052788077238 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4067 rows22250R_4068 (by norm_num)

theorem c22250R_153_20 : rowsJ2 153 154 66 340 ≤ 2374032114914045 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4066 c22250R_153_21 (by norm_num)

theorem c22250R_153_19 : rowsJ2 153 154 64 340 ≤ 2383814460455707 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4065 c22250R_153_20 (by norm_num)

theorem c22250R_153_18 : rowsJ2 153 154 63 340 ≤ 2390085449453032 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4064 c22250R_153_19 (by norm_num)

theorem c22250R_153_17 : rowsJ2 153 154 62 340 ≤ 2397387071451751 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4063 c22250R_153_18 (by norm_num)

theorem c22250R_153_16 : rowsJ2 153 154 61 340 ≤ 2405804658206599 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4062 c22250R_153_17 (by norm_num)

theorem c22250R_153_15 : rowsJ2 153 154 60 340 ≤ 2415425548759424 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4061 c22250R_153_16 (by norm_num)

theorem c22250R_153_14 : rowsJ2 153 154 59 340 ≤ 2426339260184222 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4060 c22250R_153_15 (by norm_num)

theorem c22250R_153_13 : rowsJ2 153 154 58 340 ≤ 2438637666124172 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4059 c22250R_153_14 (by norm_num)

theorem c22250R_153_12 : rowsJ2 153 154 57 340 ≤ 2452415183936941 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4058 c22250R_153_13 (by norm_num)

theorem c22250R_153_11 : rowsJ2 153 154 56 340 ≤ 2467768971326335 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4057 c22250R_153_12 (by norm_num)

theorem c22250R_153_10 : rowsJ2 153 154 55 340 ≤ 2483273238617674 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4056 c22250R_153_11 (by norm_num)

theorem c22250R_153_9 : rowsJ2 153 154 54 340 ≤ 2497459859422910 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4055 c22250R_153_10 (by norm_num)

theorem c22250R_153_8 : rowsJ2 153 154 53 340 ≤ 2510372988048474 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4054 c22250R_153_9 (by norm_num)

theorem c22250R_153_7 : rowsJ2 153 154 52 340 ≤ 2522058125547829 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4053 c22250R_153_8 (by norm_num)

theorem c22250R_153_6 : rowsJ2 153 154 51 340 ≤ 2532562277542255 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4052 c22250R_153_7 (by norm_num)

theorem c22250R_153_5 : rowsJ2 153 154 50 340 ≤ 2541934119744542 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4051 c22250R_153_6 (by norm_num)

theorem c22250R_153_4 : rowsJ2 153 154 49 340 ≤ 2550224172071168 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4050 c22250R_153_5 (by norm_num)

theorem c22250R_153_3 : rowsJ2 153 154 48 340 ≤ 2557484982286855 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4049 c22250R_153_4 (by norm_num)

theorem c22250R_153_2 : rowsJ2 153 154 46 340 ≤ 2569140383432428 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4048 c22250R_153_3 (by norm_num)

theorem c22250R_153_1 : rowsJ2 153 154 43 340 ≤ 2580357010002118 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4047 c22250R_153_2 (by norm_num)

theorem c22250R_153_0 : rowsJ2 153 154 0 340 ≤ 2587185277234602 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4046 c22250R_153_1 (by norm_num)

theorem hr22250R_153 : rows2 153 154 ≤ 2587185277234602 := rows2_le_of_rowsJ2 153 154 c22250R_153_0

theorem c22250R_154_20 : rowsJ2 154 155 67 340 ≤ 2479797258670880 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4089 rows22250R_4090 (by norm_num)

theorem c22250R_154_19 : rowsJ2 154 155 65 340 ≤ 2487271921567516 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4088 c22250R_154_20 (by norm_num)

theorem c22250R_154_18 : rowsJ2 154 155 63 340 ≤ 2498105634947090 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4087 c22250R_154_19 (by norm_num)

theorem c22250R_154_17 : rowsJ2 154 155 62 340 ≤ 2504989423267562 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4086 c22250R_154_18 (by norm_num)

theorem c22250R_154_16 : rowsJ2 154 155 61 340 ≤ 2512965152707678 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4085 c22250R_154_17 (by norm_num)

theorem c22250R_154_15 : rowsJ2 154 155 60 340 ≤ 2522120743079475 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4084 c22250R_154_16 (by norm_num)

theorem c22250R_154_14 : rowsJ2 154 155 59 340 ≤ 2532546263370913 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4083 c22250R_154_15 (by norm_num)

theorem c22250R_154_13 : rowsJ2 154 155 58 340 ≤ 2544334111724914 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4082 c22250R_154_14 (by norm_num)

theorem c22250R_154_12 : rowsJ2 154 155 57 340 ≤ 2557579203943495 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4081 c22250R_154_13 (by norm_num)

theorem c22250R_154_11 : rowsJ2 154 155 56 340 ≤ 2572379171401471 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4080 c22250R_154_12 (by norm_num)

theorem c22250R_154_10 : rowsJ2 154 155 55 340 ≤ 2588834569323963 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4079 c22250R_154_11 (by norm_num)

theorem c22250R_154_9 : rowsJ2 154 155 54 340 ≤ 2603927512195840 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4078 c22250R_154_10 (by norm_num)

theorem c22250R_154_8 : rowsJ2 154 155 53 340 ≤ 2617702237844935 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4077 c22250R_154_9 (by norm_num)

theorem c22250R_154_7 : rowsJ2 154 155 52 340 ≤ 2630204269347281 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4076 c22250R_154_8 (by norm_num)

theorem c22250R_154_6 : rowsJ2 154 155 51 340 ≤ 2641480573441483 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4075 c22250R_154_7 (by norm_num)

theorem c22250R_154_5 : rowsJ2 154 155 50 340 ≤ 2651579726406605 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4074 c22250R_154_6 (by norm_num)

theorem c22250R_154_4 : rowsJ2 154 155 49 340 ≤ 2660552088295770 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4073 c22250R_154_5 (by norm_num)

theorem c22250R_154_3 : rowsJ2 154 155 48 340 ≤ 2668449986473896 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4072 c22250R_154_4 (by norm_num)

theorem c22250R_154_2 : rowsJ2 154 155 46 340 ≤ 2681242712245612 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4071 c22250R_154_3 (by norm_num)

theorem c22250R_154_1 : rowsJ2 154 155 43 340 ≤ 2693817117740511 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4070 c22250R_154_2 (by norm_num)

theorem c22250R_154_0 : rowsJ2 154 155 0 340 ≤ 2702101921276670 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4069 c22250R_154_1 (by norm_num)

theorem hr22250R_154 : rows2 154 155 ≤ 2702101921276670 := rows2_le_of_rowsJ2 154 155 c22250R_154_0

theorem c22250R_155_20 : rowsJ2 155 156 65 340 ≤ 2602653398715942 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4111 rows22250R_4112 (by norm_num)

theorem c22250R_155_19 : rowsJ2 155 156 63 340 ≤ 2612781111303247 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4110 c22250R_155_20 (by norm_num)

theorem c22250R_155_18 : rowsJ2 155 156 62 340 ≤ 2619273938457723 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4109 c22250R_155_19 (by norm_num)

theorem c22250R_155_17 : rowsJ2 155 156 61 340 ≤ 2626834275312968 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4108 c22250R_155_18 (by norm_num)

theorem c22250R_155_16 : rowsJ2 155 156 60 340 ≤ 2635550658345863 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4107 c22250R_155_17 (by norm_num)

theorem c22250R_155_15 : rowsJ2 155 156 59 340 ≤ 2645513743077541 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4106 c22250R_155_16 (by norm_num)

theorem c22250R_155_14 : rowsJ2 155 156 58 340 ≤ 2656816485599561 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4105 c22250R_155_15 (by norm_num)

theorem c22250R_155_13 : rowsJ2 155 156 57 340 ≤ 2669554332536152 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4104 c22250R_155_14 (by norm_num)

theorem c22250R_155_12 : rowsJ2 155 156 56 340 ≤ 2683825420334216 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4103 c22250R_155_13 (by norm_num)

theorem c22250R_155_11 : rowsJ2 155 156 55 340 ≤ 2699730784841582 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4102 c22250R_155_12 (by norm_num)

theorem c22250R_155_10 : rowsJ2 155 156 54 340 ≤ 2715793578098815 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4101 c22250R_155_11 (by norm_num)

theorem c22250R_155_9 : rowsJ2 155 156 53 340 ≤ 2730492660945697 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4100 c22250R_155_10 (by norm_num)

theorem c22250R_155_8 : rowsJ2 155 156 52 340 ≤ 2743873624657806 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4099 c22250R_155_9 (by norm_num)

theorem c22250R_155_7 : rowsJ2 155 156 51 340 ≤ 2755983441191135 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4098 c22250R_155_8 (by norm_num)

theorem c22250R_155_6 : rowsJ2 155 156 50 340 ≤ 2766870629592436 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4097 c22250R_155_7 (by norm_num)

theorem c22250R_155_5 : rowsJ2 155 156 49 340 ≤ 2776585430519013 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4096 c22250R_155_6 (by norm_num)

theorem c22250R_155_4 : rowsJ2 155 156 48 340 ≤ 2785179989822278 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4095 c22250R_155_5 (by norm_num)

theorem c22250R_155_3 : rowsJ2 155 156 47 340 ≤ 2792708552212182 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4094 c22250R_155_4 (by norm_num)

theorem c22250R_155_2 : rowsJ2 155 156 45 340 ≤ 2804796400724564 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4093 c22250R_155_3 (by norm_num)

theorem c22250R_155_1 : rowsJ2 155 156 42 340 ≤ 2816433787216931 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4092 c22250R_155_2 (by norm_num)

theorem c22250R_155_0 : rowsJ2 155 156 0 340 ≤ 2823467601506560 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4091 c22250R_155_1 (by norm_num)

theorem hr22250R_155 : rows2 155 156 ≤ 2823467601506560 := rows2_le_of_rowsJ2 155 156 c22250R_155_0

theorem c22250R_156_19 : rowsJ2 156 157 64 340 ≤ 2662611846692758 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4132 rows22250R_4133 (by norm_num)

theorem c22250R_156_18 : rowsJ2 156 157 62 340 ≤ 2673831698125291 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4131 c22250R_156_19 (by norm_num)

theorem c22250R_156_17 : rowsJ2 156 157 61 340 ≤ 2680961367726303 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4130 c22250R_156_18 (by norm_num)

theorem c22250R_156_16 : rowsJ2 156 157 60 340 ≤ 2689222473975906 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4129 c22250R_156_17 (by norm_num)

theorem c22250R_156_15 : rowsJ2 156 157 59 340 ≤ 2698706287664949 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4128 c22250R_156_16 (by norm_num)

theorem c22250R_156_14 : rowsJ2 156 157 58 340 ≤ 2709506350094562 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4127 c22250R_156_15 (by norm_num)

theorem c22250R_156_13 : rowsJ2 156 157 57 340 ≤ 2721718664594386 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4126 c22250R_156_14 (by norm_num)

theorem c22250R_156_12 : rowsJ2 156 157 56 340 ≤ 2735441897280491 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4125 c22250R_156_13 (by norm_num)

theorem c22250R_156_11 : rowsJ2 156 157 55 340 ≤ 2750777588020748 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4124 c22250R_156_12 (by norm_num)

theorem c22250R_156_10 : rowsJ2 156 157 54 340 ≤ 2767830372652713 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4123 c22250R_156_11 (by norm_num)

theorem c22250R_156_9 : rowsJ2 156 157 53 340 ≤ 2783472678641910 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4122 c22250R_156_10 (by norm_num)

theorem c22250R_156_8 : rowsJ2 156 157 52 340 ≤ 2797750205390358 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4121 c22250R_156_9 (by norm_num)

theorem c22250R_156_7 : rowsJ2 156 157 51 340 ≤ 2810709967433346 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4120 c22250R_156_8 (by norm_num)

theorem c22250R_156_6 : rowsJ2 156 157 50 340 ≤ 2822400461566443 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4119 c22250R_156_7 (by norm_num)

theorem c22250R_156_5 : rowsJ2 156 157 49 340 ≤ 2832871841819581 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4118 c22250R_156_6 (by norm_num)

theorem c22250R_156_4 : rowsJ2 156 157 48 340 ≤ 2842176103240587 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4117 c22250R_156_5 (by norm_num)

theorem c22250R_156_3 : rowsJ2 156 157 47 340 ≤ 2850367275510699 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4116 c22250R_156_4 (by norm_num)

theorem c22250R_156_2 : rowsJ2 156 157 45 340 ≤ 2863637883822522 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4115 c22250R_156_3 (by norm_num)

theorem c22250R_156_1 : rowsJ2 156 157 42 340 ≤ 2876687097062105 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4114 c22250R_156_2 (by norm_num)

theorem c22250R_156_0 : rowsJ2 156 157 0 340 ≤ 2885234155874903 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4113 c22250R_156_1 (by norm_num)

theorem hr22250R_156 : rows2 156 157 ≤ 2885234155874903 := rows2_le_of_rowsJ2 156 157 c22250R_156_0

theorem c22250R_157_19 : rowsJ2 157 158 65 340 ≤ 2647554168434946 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4153 rows22250R_4154 (by norm_num)

theorem c22250R_157_18 : rowsJ2 157 158 63 340 ≤ 2656275079605998 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4152 c22250R_157_19 (by norm_num)

theorem c22250R_157_17 : rowsJ2 157 158 61 340 ≤ 2668711838568272 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4151 c22250R_157_18 (by norm_num)

theorem c22250R_157_16 : rowsJ2 157 158 60 340 ≤ 2676544880979294 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4150 c22250R_157_17 (by norm_num)

theorem c22250R_157_15 : rowsJ2 157 158 59 340 ≤ 2685576245874217 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4149 c22250R_157_16 (by norm_num)

theorem c22250R_157_14 : rowsJ2 157 158 58 340 ≤ 2695900096273983 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4148 c22250R_157_15 (by norm_num)

theorem c22250R_157_13 : rowsJ2 157 158 57 340 ≤ 2707613027475151 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4147 c22250R_157_14 (by norm_num)

theorem c22250R_157_12 : rowsJ2 157 158 56 340 ≤ 2720814269382701 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4146 c22250R_157_13 (by norm_num)

theorem c22250R_157_11 : rowsJ2 157 158 55 340 ≤ 2735605898963713 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4145 c22250R_157_12 (by norm_num)

theorem c22250R_157_10 : rowsJ2 157 158 54 340 ≤ 2752093063874370 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4144 c22250R_157_11 (by norm_num)

theorem c22250R_157_9 : rowsJ2 157 158 53 340 ≤ 2768745047450812 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4143 c22250R_157_10 (by norm_num)

theorem c22250R_157_8 : rowsJ2 157 158 52 340 ≤ 2783984762732722 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4142 c22250R_157_9 (by norm_num)

theorem c22250R_157_7 : rowsJ2 157 158 51 340 ≤ 2797859316527680 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4141 c22250R_157_8 (by norm_num)

theorem c22250R_157_6 : rowsJ2 157 158 50 340 ≤ 2810417230772374 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4140 c22250R_157_7 (by norm_num)

theorem c22250R_157_5 : rowsJ2 157 158 49 340 ≤ 2821708618159019 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4139 c22250R_157_6 (by norm_num)

theorem c22250R_157_4 : rowsJ2 157 158 48 340 ≤ 2831785366301386 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4138 c22250R_157_5 (by norm_num)

theorem c22250R_157_3 : rowsJ2 157 158 47 340 ≤ 2840701331470341 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4137 c22250R_157_4 (by norm_num)

theorem c22250R_157_2 : rowsJ2 157 158 45 340 ≤ 2855277419510741 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4136 c22250R_157_3 (by norm_num)

theorem c22250R_157_1 : rowsJ2 157 158 42 340 ≤ 2869918983827717 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4135 c22250R_157_2 (by norm_num)

theorem c22250R_157_0 : rowsJ2 157 158 0 340 ≤ 2880331746861656 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4134 c22250R_157_1 (by norm_num)

theorem hr22250R_157 : rows2 157 158 ≤ 2880331746861656 := rows2_le_of_rowsJ2 157 158 c22250R_157_0

theorem c22250R_158_19 : rowsJ2 158 159 63 340 ≤ 2652838145701897 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4174 rows22250R_4175 (by norm_num)

theorem c22250R_158_18 : rowsJ2 158 159 61 340 ≤ 2664465081282785 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4173 c22250R_158_19 (by norm_num)

theorem c22250R_158_17 : rowsJ2 158 159 60 340 ≤ 2671853996469615 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4172 c22250R_158_18 (by norm_num)

theorem c22250R_158_16 : rowsJ2 158 159 59 340 ≤ 2680416015644470 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4171 c22250R_158_17 (by norm_num)

theorem c22250R_158_15 : rowsJ2 158 159 58 340 ≤ 2690245953862723 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4170 c22250R_158_16 (by norm_num)

theorem c22250R_158_14 : rowsJ2 158 159 57 340 ≤ 2701441027127194 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4169 c22250R_158_15 (by norm_num)

theorem c22250R_158_13 : rowsJ2 158 159 56 340 ≤ 2714101056401208 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4168 c22250R_158_14 (by norm_num)

theorem c22250R_158_12 : rowsJ2 158 159 55 340 ≤ 2728328681649363 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4167 c22250R_158_13 (by norm_num)

theorem c22250R_158_11 : rowsJ2 158 159 54 340 ≤ 2744229586966200 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4166 c22250R_158_12 (by norm_num)

theorem c22250R_158_10 : rowsJ2 158 159 53 340 ≤ 2761912737939806 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4165 c22250R_158_11 (by norm_num)

theorem c22250R_158_9 : rowsJ2 158 159 52 340 ≤ 2778134769393769 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4164 c22250R_158_10 (by norm_num)

theorem c22250R_158_8 : rowsJ2 158 159 51 340 ≤ 2792942923611930 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4163 c22250R_158_9 (by norm_num)

theorem c22250R_158_7 : rowsJ2 158 159 50 340 ≤ 2806385788043583 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4162 c22250R_158_8 (by norm_num)

theorem c22250R_158_6 : rowsJ2 158 159 49 340 ≤ 2818513471787435 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4161 c22250R_158_7 (by norm_num)

theorem c22250R_158_5 : rowsJ2 158 159 48 340 ≤ 2829377790327272 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4160 c22250R_158_6 (by norm_num)

theorem c22250R_158_4 : rowsJ2 158 159 47 340 ≤ 2839032459558537 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4159 c22250R_158_5 (by norm_num)

theorem c22250R_158_3 : rowsJ2 158 159 46 340 ≤ 2847533300209712 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4158 c22250R_158_4 (by norm_num)

theorem c22250R_158_2 : rowsJ2 158 159 44 340 ≤ 2861308611658121 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4157 c22250R_158_3 (by norm_num)

theorem c22250R_158_1 : rowsJ2 158 159 41 340 ≤ 2874859482326031 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4156 c22250R_158_2 (by norm_num)

theorem c22250R_158_0 : rowsJ2 158 159 0 340 ≤ 2883567116916628 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4155 c22250R_158_1 (by norm_num)

theorem hr22250R_158 : rows2 158 159 ≤ 2883567116916628 := rows2_le_of_rowsJ2 158 159 c22250R_158_0

theorem c22250R_159_19 : rowsJ2 159 160 64 340 ≤ 2645955991787792 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4195 rows22250R_4196 (by norm_num)

theorem c22250R_159_18 : rowsJ2 159 160 62 340 ≤ 2654995579527186 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4194 c22250R_159_19 (by norm_num)

theorem c22250R_159_17 : rowsJ2 159 160 60 340 ≤ 2667887951498149 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4193 c22250R_159_18 (by norm_num)

theorem c22250R_159_16 : rowsJ2 159 160 59 340 ≤ 2676008622190928 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4192 c22250R_159_17 (by norm_num)

theorem c22250R_159_15 : rowsJ2 159 160 58 340 ≤ 2685372235036050 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4191 c22250R_159_16 (by norm_num)

theorem c22250R_159_14 : rowsJ2 159 160 57 340 ≤ 2696076665279292 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4190 c22250R_159_15 (by norm_num)

theorem c22250R_159_13 : rowsJ2 159 160 56 340 ≤ 2708222362145988 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4189 c22250R_159_14 (by norm_num)

theorem c22250R_159_12 : rowsJ2 159 160 55 340 ≤ 2721912564584004 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4188 c22250R_159_13 (by norm_num)

theorem c22250R_159_11 : rowsJ2 159 160 54 340 ≤ 2737253528003389 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4187 c22250R_159_12 (by norm_num)

theorem c22250R_159_10 : rowsJ2 159 160 53 340 ≤ 2754354763167274 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4186 c22250R_159_11 (by norm_num)

theorem c22250R_159_9 : rowsJ2 159 160 52 340 ≤ 2771628682007924 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4185 c22250R_159_10 (by norm_num)

theorem c22250R_159_8 : rowsJ2 159 160 51 340 ≤ 2787439112759554 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4184 c22250R_159_9 (by norm_num)

theorem c22250R_159_7 : rowsJ2 159 160 50 340 ≤ 2801834761946004 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4183 c22250R_159_8 (by norm_num)

theorem c22250R_159_6 : rowsJ2 159 160 49 340 ≤ 2814865786083088 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4182 c22250R_159_7 (by norm_num)

theorem c22250R_159_5 : rowsJ2 159 160 48 340 ≤ 2826583977204222 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4181 c22250R_159_6 (by norm_num)

theorem c22250R_159_4 : rowsJ2 159 160 47 340 ≤ 2837042957380723 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4180 c22250R_159_5 (by norm_num)

theorem c22250R_159_3 : rowsJ2 159 160 46 340 ≤ 2846298383349609 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4179 c22250R_159_4 (by norm_num)

theorem c22250R_159_2 : rowsJ2 159 160 44 340 ≤ 2861432681022746 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4178 c22250R_159_3 (by norm_num)

theorem c22250R_159_1 : rowsJ2 159 160 41 340 ≤ 2876640923569331 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4177 c22250R_159_2 (by norm_num)

theorem c22250R_159_0 : rowsJ2 159 160 0 340 ≤ 2887228137142971 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4176 c22250R_159_1 (by norm_num)

theorem hr22250R_159 : rows2 159 160 ≤ 2887228137142971 := rows2_le_of_rowsJ2 159 160 c22250R_159_0

theorem c22250R_160_18 : rowsJ2 160 161 63 340 ≤ 2640796667423306 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4215 rows22250R_4216 (by norm_num)

theorem c22250R_160_17 : rowsJ2 160 161 61 340 ≤ 2650891668935943 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4214 c22250R_160_18 (by norm_num)

theorem c22250R_160_16 : rowsJ2 160 161 59 340 ≤ 2665095652333344 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4213 c22250R_160_17 (by norm_num)

theorem c22250R_160_15 : rowsJ2 160 161 58 340 ≤ 2673975163696860 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4212 c22250R_160_16 (by norm_num)

theorem c22250R_160_14 : rowsJ2 160 161 57 340 ≤ 2684170332304671 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4211 c22250R_160_15 (by norm_num)

theorem c22250R_160_13 : rowsJ2 160 161 56 340 ≤ 2695782265967619 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4210 c22250R_160_14 (by norm_num)

theorem c22250R_160_12 : rowsJ2 160 161 55 340 ≤ 2708914831371341 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4209 c22250R_160_13 (by norm_num)

theorem c22250R_160_11 : rowsJ2 160 161 54 340 ≤ 2723674882533054 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4208 c22250R_160_12 (by norm_num)

theorem c22250R_160_10 : rowsJ2 160 161 53 340 ≤ 2740172501319834 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4207 c22250R_160_11 (by norm_num)

theorem c22250R_160_9 : rowsJ2 160 161 52 340 ≤ 2758521251288668 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4206 c22250R_160_10 (by norm_num)

theorem c22250R_160_8 : rowsJ2 160 161 51 340 ≤ 2775355445767968 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4205 c22250R_160_9 (by norm_num)

theorem c22250R_160_7 : rowsJ2 160 161 50 340 ≤ 2790723957185590 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4204 c22250R_160_8 (by norm_num)

theorem c22250R_160_6 : rowsJ2 160 161 49 340 ≤ 2804677033171997 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4203 c22250R_160_7 (by norm_num)

theorem c22250R_160_5 : rowsJ2 160 161 48 340 ≤ 2817266483104922 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4202 c22250R_160_6 (by norm_num)

theorem c22250R_160_4 : rowsJ2 160 161 47 340 ≤ 2828545873332156 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4201 c22250R_160_5 (by norm_num)

theorem c22250R_160_3 : rowsJ2 160 161 46 340 ≤ 2838570732196023 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4200 c22250R_160_4 (by norm_num)

theorem c22250R_160_2 : rowsJ2 160 161 44 340 ≤ 2855090087559913 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4199 c22250R_160_3 (by norm_num)

theorem c22250R_160_1 : rowsJ2 160 161 41 340 ≤ 2871986186818063 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4198 c22250R_160_2 (by norm_num)

theorem c22250R_160_0 : rowsJ2 160 161 0 340 ≤ 2884543344983494 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4197 c22250R_160_1 (by norm_num)

theorem hr22250R_160 : rows2 160 161 ≤ 2884543344983494 := rows2_le_of_rowsJ2 160 161 c22250R_160_0

theorem c22250R_161_18 : rowsJ2 161 162 61 340 ≤ 2650503664907204 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4235 rows22250R_4236 (by norm_num)

theorem c22250R_161_17 : rowsJ2 161 162 59 340 ≤ 2663876828941622 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4234 c22250R_161_18 (by norm_num)

theorem c22250R_161_16 : rowsJ2 161 162 58 340 ≤ 2672301058508677 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4233 c22250R_161_17 (by norm_num)

theorem c22250R_161_15 : rowsJ2 161 162 57 340 ≤ 2682015354023945 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4232 c22250R_161_16 (by norm_num)

theorem c22250R_161_14 : rowsJ2 161 162 56 340 ≤ 2693121522593816 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4231 c22250R_161_15 (by norm_num)

theorem c22250R_161_13 : rowsJ2 161 162 55 340 ≤ 2705724097927809 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4230 c22250R_161_14 (by norm_num)

theorem c22250R_161_12 : rowsJ2 161 162 54 340 ≤ 2719930570636957 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4229 c22250R_161_13 (by norm_num)

theorem c22250R_161_11 : rowsJ2 161 162 53 340 ≤ 2735851630496904 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4228 c22250R_161_12 (by norm_num)

theorem c22250R_161_10 : rowsJ2 161 162 52 340 ≤ 2753601421945255 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4227 c22250R_161_11 (by norm_num)

theorem c22250R_161_9 : rowsJ2 161 162 51 340 ≤ 2771532274322032 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4226 c22250R_161_10 (by norm_num)

theorem c22250R_161_8 : rowsJ2 161 162 50 340 ≤ 2787945574963398 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4225 c22250R_161_9 (by norm_num)

theorem c22250R_161_7 : rowsJ2 161 162 49 340 ≤ 2802891720440342 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4224 c22250R_161_8 (by norm_num)

theorem c22250R_161_6 : rowsJ2 161 162 48 340 ≤ 2816422592468181 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4223 c22250R_161_7 (by norm_num)

theorem c22250R_161_5 : rowsJ2 161 162 47 340 ≤ 2828591754077412 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4222 c22250R_161_6 (by norm_num)

theorem c22250R_161_4 : rowsJ2 161 162 46 340 ≤ 2839454655260407 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4221 c22250R_161_5 (by norm_num)

theorem c22250R_161_3 : rowsJ2 161 162 45 340 ≤ 2849068849297736 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4220 c22250R_161_4 (by norm_num)

theorem c22250R_161_2 : rowsJ2 161 162 43 340 ≤ 2864793228554822 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4219 c22250R_161_3 (by norm_num)

theorem c22250R_161_1 : rowsJ2 161 162 40 340 ≤ 2880600745562654 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4218 c22250R_161_2 (by norm_num)

theorem c22250R_161_0 : rowsJ2 161 162 0 340 ≤ 2891186973365573 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4217 c22250R_161_1 (by norm_num)

theorem hr22250R_161 : rows2 161 162 ≤ 2891186973365573 := rows2_le_of_rowsJ2 161 162 c22250R_161_0

theorem c22250R_162_18 : rowsJ2 162 163 62 340 ≤ 2647038231696552 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4255 rows22250R_4256 (by norm_num)

theorem c22250R_162_17 : rowsJ2 162 163 60 340 ≤ 2657512289223156 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4254 c22250R_162_18 (by norm_num)

theorem c22250R_162_16 : rowsJ2 162 163 58 340 ≤ 2672251111031140 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4253 c22250R_162_17 (by norm_num)

theorem c22250R_162_15 : rowsJ2 162 163 57 340 ≤ 2681465822510420 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4252 c22250R_162_16 (by norm_num)

theorem c22250R_162_14 : rowsJ2 162 163 56 340 ≤ 2692046631021279 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4251 c22250R_162_15 (by norm_num)

theorem c22250R_162_13 : rowsJ2 162 163 55 340 ≤ 2704098769319558 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4250 c22250R_162_14 (by norm_num)

theorem c22250R_162_12 : rowsJ2 162 163 54 340 ≤ 2717730394956494 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4249 c22250R_162_13 (by norm_num)

theorem c22250R_162_11 : rowsJ2 162 163 53 340 ≤ 2733052834401587 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4248 c22250R_162_12 (by norm_num)

theorem c22250R_162_10 : rowsJ2 162 163 52 340 ≤ 2750180840304676 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4247 c22250R_162_11 (by norm_num)

theorem c22250R_162_9 : rowsJ2 162 163 51 340 ≤ 2769232863285010 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4246 c22250R_162_10 (by norm_num)

theorem c22250R_162_8 : rowsJ2 162 163 50 340 ≤ 2786713906949997 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4245 c22250R_162_9 (by norm_num)

theorem c22250R_162_7 : rowsJ2 162 163 49 340 ≤ 2802674567658080 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4244 c22250R_162_8 (by norm_num)

theorem c22250R_162_6 : rowsJ2 162 163 48 340 ≤ 2817166846841182 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4243 c22250R_162_7 (by norm_num)

theorem c22250R_162_5 : rowsJ2 162 163 47 340 ≤ 2830244348380118 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4242 c22250R_162_6 (by norm_num)

theorem c22250R_162_4 : rowsJ2 162 163 46 340 ≤ 2841962485106781 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4241 c22250R_162_5 (by norm_num)

theorem c22250R_162_3 : rowsJ2 162 163 45 340 ≤ 2852378695649650 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4240 c22250R_162_4 (by norm_num)

theorem c22250R_162_2 : rowsJ2 162 163 43 340 ≤ 2869546605574181 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4239 c22250R_162_3 (by norm_num)

theorem c22250R_162_1 : rowsJ2 162 163 40 340 ≤ 2887112949215390 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4238 c22250R_162_2 (by norm_num)

theorem c22250R_162_0 : rowsJ2 162 163 0 340 ≤ 2899681929836762 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4237 c22250R_162_1 (by norm_num)

theorem hr22250R_162 : rows2 162 163 ≤ 2899681929836762 := rows2_le_of_rowsJ2 162 163 c22250R_162_0

theorem c22250R_163_18 : rowsJ2 163 164 60 340 ≤ 2652894178555232 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_4275 rows22250R_4276 (by norm_num)

theorem c22250R_163_17 : rowsJ2 163 164 58 340 ≤ 2666775033318887 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_4274 c22250R_163_18 (by norm_num)

theorem c22250R_163_16 : rowsJ2 163 164 57 340 ≤ 2675519843276220 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_4273 c22250R_163_17 (by norm_num)

theorem c22250R_163_15 : rowsJ2 163 164 56 340 ≤ 2685604521350803 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_4272 c22250R_163_16 (by norm_num)

theorem c22250R_163_14 : rowsJ2 163 164 55 340 ≤ 2697135042387469 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_4271 c22250R_163_15 (by norm_num)

theorem c22250R_163_13 : rowsJ2 163 164 54 340 ≤ 2710220272398715 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_4270 c22250R_163_14 (by norm_num)

theorem c22250R_163_12 : rowsJ2 163 164 53 340 ≤ 2724972214681396 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_4269 c22250R_163_13 (by norm_num)

theorem c22250R_163_11 : rowsJ2 163 164 52 340 ≤ 2741506268970739 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_4268 c22250R_163_12 (by norm_num)

theorem c22250R_163_10 : rowsJ2 163 164 51 340 ≤ 2759941505028804 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_4267 c22250R_163_11 (by norm_num)

theorem c22250R_163_9 : rowsJ2 163 164 50 340 ≤ 2778566732102607 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_4266 c22250R_163_10 (by norm_num)

theorem c22250R_163_8 : rowsJ2 163 164 49 340 ≤ 2795617302628575 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_4265 c22250R_163_9 (by norm_num)

theorem c22250R_163_7 : rowsJ2 163 164 48 340 ≤ 2811145400288021 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_4264 c22250R_163_8 (by norm_num)

theorem c22250R_163_6 : rowsJ2 163 164 47 340 ≤ 2825204729195840 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_4263 c22250R_163_7 (by norm_num)

theorem c22250R_163_5 : rowsJ2 163 164 46 340 ≤ 2837850721532654 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_4262 c22250R_163_6 (by norm_num)

theorem c22250R_163_4 : rowsJ2 163 164 45 340 ≤ 2849140755160993 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_4261 c22250R_163_5 (by norm_num)

theorem c22250R_163_3 : rowsJ2 163 164 44 340 ≤ 2859134382529616 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_4260 c22250R_163_4 (by norm_num)

theorem c22250R_163_2 : rowsJ2 163 164 42 340 ≤ 2875482964852232 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_4259 c22250R_163_3 (by norm_num)

theorem c22250R_163_1 : rowsJ2 163 164 40 340 ≤ 2887425926748839 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_4258 c22250R_163_2 (by norm_num)

theorem c22250R_163_0 : rowsJ2 163 164 0 340 ≤ 2902313939363336 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_4257 c22250R_163_1 (by norm_num)

theorem hr22250R_163 : rows2 163 164 ≤ 2902313939363336 := rows2_le_of_rowsJ2 163 164 c22250R_163_0

theorem c22250R_164_17 : rowsJ2 164 165 59 340 ≤ 2663521628349838 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_4294 rows22250R_4295 (by norm_num)

theorem c22250R_164_16 : rowsJ2 164 165 57 340 ≤ 2678825419357756 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_4293 c22250R_164_17 (by norm_num)

theorem c22250R_164_15 : rowsJ2 164 165 56 340 ≤ 2688394261263411 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_4292 c22250R_164_16 (by norm_num)

theorem c22250R_164_14 : rowsJ2 164 165 55 340 ≤ 2699382531374852 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_4291 c22250R_164_15 (by norm_num)

theorem c22250R_164_13 : rowsJ2 164 165 54 340 ≤ 2711899838011548 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_4290 c22250R_164_14 (by norm_num)

theorem c22250R_164_12 : rowsJ2 164 165 53 340 ≤ 2726058893352275 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_4289 c22250R_164_13 (by norm_num)

theorem c22250R_164_11 : rowsJ2 164 165 52 340 ≤ 2741975774604823 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_4288 c22250R_164_12 (by norm_num)

theorem c22250R_164_10 : rowsJ2 164 165 51 340 ≤ 2759770199510358 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_4287 c22250R_164_11 (by norm_num)

theorem c22250R_164_9 : rowsJ2 164 165 50 340 ≤ 2779565817712649 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_4286 c22250R_164_10 (by norm_num)

theorem c22250R_164_8 : rowsJ2 164 165 49 340 ≤ 2797730835707414 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_4285 c22250R_164_9 (by norm_num)

theorem c22250R_164_7 : rowsJ2 164 165 48 340 ≤ 2814317674731133 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_4284 c22250R_164_8 (by norm_num)

theorem c22250R_164_6 : rowsJ2 164 165 47 340 ≤ 2829380190593314 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_4283 c22250R_164_7 (by norm_num)

theorem c22250R_164_5 : rowsJ2 164 165 46 340 ≤ 2842973882726195 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_4282 c22250R_164_6 (by norm_num)

theorem c22250R_164_4 : rowsJ2 164 165 45 340 ≤ 2855156112832924 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_4281 c22250R_164_5 (by norm_num)

theorem c22250R_164_3 : rowsJ2 164 165 44 340 ≤ 2865986334453055 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_4280 c22250R_164_4 (by norm_num)

theorem c22250R_164_2 : rowsJ2 164 165 42 340 ≤ 2883840490676735 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_4279 c22250R_164_3 (by norm_num)

theorem c22250R_164_1 : rowsJ2 164 165 39 340 ≤ 2902116313677119 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_4278 c22250R_164_2 (by norm_num)

theorem c22250R_164_0 : rowsJ2 164 165 0 340 ≤ 2914435124629239 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_4277 c22250R_164_1 (by norm_num)

theorem hr22250R_164 : rows2 164 165 ≤ 2914435124629239 := rows2_le_of_rowsJ2 164 165 c22250R_164_0

theorem c22250R_165_16 : rowsJ2 165 166 58 340 ≤ 2676302981792838 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_4312 rows22250R_4313 (by norm_num)

theorem c22250R_165_15 : rowsJ2 165 166 56 340 ≤ 2693185209681575 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_4311 c22250R_165_16 (by norm_num)

theorem c22250R_165_14 : rowsJ2 165 166 55 340 ≤ 2703661341248940 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_4310 c22250R_165_15 (by norm_num)

theorem c22250R_165_13 : rowsJ2 165 166 54 340 ≤ 2715640406703611 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_4309 c22250R_165_14 (by norm_num)

theorem c22250R_165_12 : rowsJ2 165 166 53 340 ≤ 2729235871027683 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_4308 c22250R_165_13 (by norm_num)

theorem c22250R_165_11 : rowsJ2 165 166 52 340 ≤ 2744564531340891 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_4307 c22250R_165_12 (by norm_num)

theorem c22250R_165_10 : rowsJ2 165 166 51 340 ≤ 2761746794457947 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_4306 c22250R_165_11 (by norm_num)

theorem c22250R_165_9 : rowsJ2 165 166 50 340 ≤ 2780906970213863 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_4305 c22250R_165_10 (by norm_num)

theorem c22250R_165_8 : rowsJ2 165 166 49 340 ≤ 2800266664323458 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_4304 c22250R_165_9 (by norm_num)

theorem c22250R_165_7 : rowsJ2 165 166 48 340 ≤ 2817991341679136 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_4303 c22250R_165_8 (by norm_num)

theorem c22250R_165_6 : rowsJ2 165 166 47 340 ≤ 2834135077522114 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_4302 c22250R_165_7 (by norm_num)

theorem c22250R_165_5 : rowsJ2 165 166 46 340 ≤ 2848753502768014 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_4301 c22250R_165_6 (by norm_num)

theorem c22250R_165_4 : rowsJ2 165 166 45 340 ≤ 2861904023994144 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_4300 c22250R_165_5 (by norm_num)

theorem c22250R_165_3 : rowsJ2 165 166 44 340 ≤ 2873646053947559 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_4299 c22250R_165_4 (by norm_num)

theorem c22250R_165_2 : rowsJ2 165 166 42 340 ≤ 2893153789968087 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_4298 c22250R_165_3 (by norm_num)

theorem c22250R_165_1 : rowsJ2 165 166 39 340 ≤ 2913480448357229 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_4297 c22250R_165_2 (by norm_num)

theorem c22250R_165_0 : rowsJ2 165 166 0 340 ≤ 2928074342190992 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_4296 c22250R_165_1 (by norm_num)

theorem hr22250R_165 : rows2 165 166 ≤ 2928074342190992 := rows2_le_of_rowsJ2 165 166 c22250R_165_0

theorem c22250R_166_17 : rowsJ2 166 167 58 340 ≤ 2676295503402211 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_4331 rows22250R_4332 (by norm_num)

theorem c22250R_166_16 : rowsJ2 166 167 56 340 ≤ 2692196497402433 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_4330 c22250R_166_17 (by norm_num)

theorem c22250R_166_15 : rowsJ2 166 167 55 340 ≤ 2702139725261807 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_4329 c22250R_166_16 (by norm_num)

theorem c22250R_166_14 : rowsJ2 166 167 54 340 ≤ 2713558809972302 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_4328 c22250R_166_15 (by norm_num)

theorem c22250R_166_13 : rowsJ2 166 167 53 340 ≤ 2726568005123517 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_4327 c22250R_166_14 (by norm_num)

theorem c22250R_166_12 : rowsJ2 166 167 52 340 ≤ 2741284861635818 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_4326 c22250R_166_13 (by norm_num)

theorem c22250R_166_11 : rowsJ2 166 167 51 340 ≤ 2757830507504595 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_4325 c22250R_166_12 (by norm_num)

theorem c22250R_166_10 : rowsJ2 166 167 50 340 ≤ 2776329943207304 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_4324 c22250R_166_11 (by norm_num)

theorem c22250R_166_9 : rowsJ2 166 167 49 340 ≤ 2796912354463739 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_4323 c22250R_166_10 (by norm_num)

theorem c22250R_166_8 : rowsJ2 166 167 48 340 ≤ 2815801120227872 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_4322 c22250R_166_9 (by norm_num)

theorem c22250R_166_7 : rowsJ2 166 167 47 340 ≤ 2833050595435759 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_4321 c22250R_166_8 (by norm_num)

theorem c22250R_166_6 : rowsJ2 166 167 46 340 ≤ 2848716598479293 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_4320 c22250R_166_7 (by norm_num)

theorem c22250R_166_5 : rowsJ2 166 167 45 340 ≤ 2862856632856267 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_4319 c22250R_166_6 (by norm_num)

theorem c22250R_166_4 : rowsJ2 166 167 44 340 ≤ 2875530118913832 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_4318 c22250R_166_5 (by norm_num)

theorem c22250R_166_3 : rowsJ2 166 167 43 340 ≤ 2886798637117240 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_4317 c22250R_166_4 (by norm_num)

theorem c22250R_166_2 : rowsJ2 166 167 41 340 ≤ 2905379444951741 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_4316 c22250R_166_3 (by norm_num)

theorem c22250R_166_1 : rowsJ2 166 167 39 340 ≤ 2919145022943721 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_4315 c22250R_166_2 (by norm_num)

theorem c22250R_166_0 : rowsJ2 166 167 0 340 ≤ 2936182460785854 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_4314 c22250R_166_1 (by norm_num)

theorem hr22250R_166 : rows2 166 167 ≤ 2936182460785854 := rows2_le_of_rowsJ2 166 167 c22250R_166_0

theorem c22250R_167_16 : rowsJ2 167 168 57 340 ≤ 2692633431503290 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_4349 rows22250R_4350 (by norm_num)

theorem c22250R_167_15 : rowsJ2 167 168 55 340 ≤ 2710180975639577 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_4348 c22250R_167_16 (by norm_num)

theorem c22250R_167_14 : rowsJ2 167 168 54 340 ≤ 2721071118934306 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_4347 c22250R_167_15 (by norm_num)

theorem c22250R_167_13 : rowsJ2 167 168 53 340 ≤ 2733524632740526 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_4346 c22250R_167_14 (by norm_num)

theorem c22250R_167_12 : rowsJ2 167 168 52 340 ≤ 2747659868281015 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_4345 c22250R_167_13 (by norm_num)

theorem c22250R_167_11 : rowsJ2 167 168 51 340 ≤ 2763598719649751 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_4344 c22250R_167_12 (by norm_num)

theorem c22250R_167_10 : rowsJ2 167 168 50 340 ≤ 2781466921448992 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_4343 c22250R_167_11 (by norm_num)

theorem c22250R_167_9 : rowsJ2 167 168 49 340 ≤ 2801394363677844 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_4342 c22250R_167_10 (by norm_num)

theorem c22250R_167_8 : rowsJ2 167 168 48 340 ≤ 2821531497500299 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_4341 c22250R_167_9 (by norm_num)

theorem c22250R_167_7 : rowsJ2 167 168 47 340 ≤ 2839969766105782 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_4340 c22250R_167_8 (by norm_num)

theorem c22250R_167_6 : rowsJ2 167 168 46 340 ≤ 2856765248863828 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_4339 c22250R_167_7 (by norm_num)

theorem c22250R_167_5 : rowsJ2 167 168 45 340 ≤ 2871975615786387 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_4338 c22250R_167_6 (by norm_num)

theorem c22250R_167_4 : rowsJ2 167 168 44 340 ≤ 2885660360851618 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_4337 c22250R_167_5 (by norm_num)

theorem c22250R_167_3 : rowsJ2 167 168 43 340 ≤ 2897881046413700 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_4336 c22250R_167_4 (by norm_num)

theorem c22250R_167_2 : rowsJ2 167 168 41 340 ≤ 2918188386770574 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_4335 c22250R_167_3 (by norm_num)

theorem c22250R_167_1 : rowsJ2 167 168 38 340 ≤ 2939356697912501 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_4334 c22250R_167_2 (by norm_num)

theorem c22250R_167_0 : rowsJ2 167 168 0 340 ≤ 2953288554294507 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_4333 c22250R_167_1 (by norm_num)

theorem hr22250R_167 : rows2 167 168 ≤ 2953288554294507 := rows2_le_of_rowsJ2 167 168 c22250R_167_0

theorem c22250R_168_16 : rowsJ2 168 169 56 340 ≤ 2710919575989803 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_4367 rows22250R_4368 (by norm_num)

theorem c22250R_168_15 : rowsJ2 168 169 54 340 ≤ 2730178551472659 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_4366 c22250R_168_16 (by norm_num)

theorem c22250R_168_14 : rowsJ2 168 169 53 340 ≤ 2742053465978444 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_4365 c22250R_168_15 (by norm_num)

theorem c22250R_168_13 : rowsJ2 168 169 52 340 ≤ 2755583176896852 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_4364 c22250R_168_14 (by norm_num)

theorem c22250R_168_12 : rowsJ2 168 169 51 340 ≤ 2770890380280370 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_4363 c22250R_168_13 (by norm_num)

theorem c22250R_168_11 : rowsJ2 168 169 50 340 ≤ 2788101578811219 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_4362 c22250R_168_12 (by norm_num)

theorem c22250R_168_10 : rowsJ2 168 169 49 340 ≤ 2807347398954122 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_4361 c22250R_168_11 (by norm_num)

theorem c22250R_168_9 : rowsJ2 168 169 48 340 ≤ 2828762927120885 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_4360 c22250R_168_10 (by norm_num)

theorem c22250R_168_8 : rowsJ2 168 169 47 340 ≤ 2848418092809422 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_4359 c22250R_168_9 (by norm_num)

theorem c22250R_168_7 : rowsJ2 168 169 46 340 ≤ 2866369302151236 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_4358 c22250R_168_8 (by norm_num)

theorem c22250R_168_6 : rowsJ2 168 169 45 340 ≤ 2882674452707202 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_4357 c22250R_168_7 (by norm_num)

theorem c22250R_168_5 : rowsJ2 168 169 44 340 ≤ 2897393168736384 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_4356 c22250R_168_6 (by norm_num)

theorem c22250R_168_4 : rowsJ2 168 169 43 340 ≤ 2910587047076426 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_4355 c22250R_168_5 (by norm_num)

theorem c22250R_168_3 : rowsJ2 168 169 42 340 ≤ 2922319915192568 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_4354 c22250R_168_4 (by norm_num)

theorem c22250R_168_2 : rowsJ2 168 169 40 340 ≤ 2941670730536505 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_4353 c22250R_168_3 (by norm_num)

theorem c22250R_168_1 : rowsJ2 168 169 38 340 ≤ 2956011582711310 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_4352 c22250R_168_2 (by norm_num)

theorem c22250R_168_0 : rowsJ2 168 169 0 340 ≤ 2972334157726705 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_4351 c22250R_168_1 (by norm_num)

theorem hr22250R_168 : rows2 168 169 ≤ 2972334157726705 := rows2_le_of_rowsJ2 168 169 c22250R_168_0

theorem c22250R_169_16 : rowsJ2 169 170 56 340 ≤ 2715583246771610 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_4385 rows22250R_4386 (by norm_num)

theorem c22250R_169_15 : rowsJ2 169 170 54 340 ≤ 2733834845670056 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_4384 c22250R_169_16 (by norm_num)

theorem c22250R_169_14 : rowsJ2 169 170 53 340 ≤ 2745163174043155 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_4383 c22250R_169_15 (by norm_num)

theorem c22250R_169_13 : rowsJ2 169 170 52 340 ≤ 2758118899672777 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_4382 c22250R_169_14 (by norm_num)

theorem c22250R_169_12 : rowsJ2 169 170 51 340 ≤ 2772825569848084 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_4381 c22250R_169_13 (by norm_num)

theorem c22250R_169_11 : rowsJ2 169 170 50 340 ≤ 2789410502915809 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_4380 c22250R_169_12 (by norm_num)

theorem c22250R_169_10 : rowsJ2 169 170 49 340 ≤ 2808005107857850 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_4379 c22250R_169_11 (by norm_num)

theorem c22250R_169_9 : rowsJ2 169 170 48 340 ≤ 2828745222774040 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_4378 c22250R_169_10 (by norm_num)

theorem c22250R_169_8 : rowsJ2 169 170 47 340 ≤ 2849705901781393 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_4377 c22250R_169_9 (by norm_num)

theorem c22250R_169_7 : rowsJ2 169 170 46 340 ≤ 2868900125424819 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_4376 c22250R_169_8 (by norm_num)

theorem c22250R_169_6 : rowsJ2 169 170 45 340 ≤ 2886386098711187 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_4375 c22250R_169_7 (by norm_num)

theorem c22250R_169_5 : rowsJ2 169 170 44 340 ≤ 2902223651714906 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_4374 c22250R_169_6 (by norm_num)

theorem c22250R_169_4 : rowsJ2 169 170 43 340 ≤ 2916474487316844 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_4373 c22250R_169_5 (by norm_num)

theorem c22250R_169_3 : rowsJ2 169 170 42 340 ≤ 2929202440624367 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_4372 c22250R_169_4 (by norm_num)

theorem c22250R_169_2 : rowsJ2 169 170 40 340 ≤ 2950357353675404 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_4371 c22250R_169_3 (by norm_num)

theorem c22250R_169_1 : rowsJ2 169 170 38 340 ≤ 2966252475092500 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_4370 c22250R_169_2 (by norm_num)

theorem c22250R_169_0 : rowsJ2 169 170 0 340 ≤ 2985275988887253 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_4369 c22250R_169_1 (by norm_num)

theorem hr22250R_169 : rows2 169 170 ≤ 2985275988887253 := rows2_le_of_rowsJ2 169 170 c22250R_169_0

theorem c22250R_170_15 : rowsJ2 170 171 55 340 ≤ 2737391945305755 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_4402 rows22250R_4403 (by norm_num)

theorem c22250R_170_14 : rowsJ2 170 171 53 340 ≤ 2757431320355771 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_4401 c22250R_170_15 (by norm_num)

theorem c22250R_170_13 : rowsJ2 170 171 52 340 ≤ 2769788886074608 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_4400 c22250R_170_14 (by norm_num)

theorem c22250R_170_12 : rowsJ2 170 171 51 340 ≤ 2783869812850712 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_4399 c22250R_170_13 (by norm_num)

theorem c22250R_170_11 : rowsJ2 170 171 50 340 ≤ 2799802272675720 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_4398 c22250R_170_12 (by norm_num)

theorem c22250R_170_10 : rowsJ2 170 171 49 340 ≤ 2817718492991447 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_4397 c22250R_170_11 (by norm_num)

theorem c22250R_170_9 : rowsJ2 170 171 48 340 ≤ 2837755097637947 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_4396 c22250R_170_10 (by norm_num)

theorem c22250R_170_8 : rowsJ2 170 171 47 340 ≤ 2860053468665020 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_4395 c22250R_170_9 (by norm_num)

theorem c22250R_170_7 : rowsJ2 170 171 46 340 ≤ 2880520819143272 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_4394 c22250R_170_8 (by norm_num)

theorem c22250R_170_6 : rowsJ2 170 171 45 340 ≤ 2899215733470227 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_4393 c22250R_170_7 (by norm_num)

theorem c22250R_170_5 : rowsJ2 170 171 44 340 ≤ 2916198314188818 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_4392 c22250R_170_6 (by norm_num)

theorem c22250R_170_4 : rowsJ2 170 171 43 340 ≤ 2931530431997014 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_4391 c22250R_170_5 (by norm_num)

theorem c22250R_170_3 : rowsJ2 170 171 42 340 ≤ 2945275986910175 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_4390 c22250R_170_4 (by norm_num)

theorem c22250R_170_2 : rowsJ2 170 171 40 340 ≤ 2968274813410599 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_4389 c22250R_170_3 (by norm_num)

theorem c22250R_170_1 : rowsJ2 170 171 37 340 ≤ 2992619696478409 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_4388 c22250R_170_2 (by norm_num)

theorem c22250R_170_0 : rowsJ2 170 171 0 340 ≤ 3007734438282712 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_4387 c22250R_170_1 (by norm_num)

theorem hr22250R_170 : rows2 170 171 ≤ 3007734438282712 := rows2_le_of_rowsJ2 170 171 c22250R_170_0

theorem c22250R_171_15 : rowsJ2 171 172 54 340 ≤ 2761349435028005 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_4419 rows22250R_4420 (by norm_num)

theorem c22250R_171_14 : rowsJ2 171 172 52 340 ≤ 2783364424321117 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_4418 c22250R_171_15 (by norm_num)

theorem c22250R_171_13 : rowsJ2 171 172 51 340 ≤ 2796852147269209 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_4417 c22250R_171_14 (by norm_num)

theorem c22250R_171_12 : rowsJ2 171 172 50 340 ≤ 2812164228448915 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_4416 c22250R_171_13 (by norm_num)

theorem c22250R_171_11 : rowsJ2 171 172 49 340 ≤ 2829433764218226 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_4415 c22250R_171_12 (by norm_num)

theorem c22250R_171_10 : rowsJ2 171 172 48 340 ≤ 2848798212975933 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_4414 c22250R_171_11 (by norm_num)

theorem c22250R_171_9 : rowsJ2 171 172 47 340 ≤ 2870399759500855 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_4413 c22250R_171_10 (by norm_num)

theorem c22250R_171_8 : rowsJ2 171 172 46 340 ≤ 2892233500459159 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_4412 c22250R_171_9 (by norm_num)

theorem c22250R_171_7 : rowsJ2 171 172 45 340 ≤ 2912229178070353 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_4411 c22250R_171_8 (by norm_num)

theorem c22250R_171_6 : rowsJ2 171 172 44 340 ≤ 2930447254352389 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_4410 c22250R_171_7 (by norm_num)

theorem c22250R_171_5 : rowsJ2 171 172 43 340 ≤ 2946949849948457 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_4409 c22250R_171_6 (by norm_num)

theorem c22250R_171_4 : rowsJ2 171 172 42 340 ≤ 2961801007469383 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_4408 c22250R_171_5 (by norm_num)

theorem c22250R_171_3 : rowsJ2 171 172 41 340 ≤ 2975066967142044 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_4407 c22250R_171_4 (by norm_num)

theorem c22250R_171_2 : rowsJ2 171 172 39 340 ≤ 2997120996636041 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_4406 c22250R_171_3 (by norm_num)

theorem c22250R_171_1 : rowsJ2 171 172 37 340 ≤ 3013697242157832 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_4405 c22250R_171_2 (by norm_num)

theorem c22250R_171_0 : rowsJ2 171 172 0 340 ≤ 3031383310915873 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_4404 c22250R_171_1 (by norm_num)

theorem hr22250R_171 : rows2 171 172 ≤ 3031383310915873 := rows2_le_of_rowsJ2 171 172 c22250R_171_0

theorem c22250R_172_14 : rowsJ2 172 173 52 340 ≤ 2791169749485941 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_4435 rows22250R_4436 (by norm_num)

theorem c22250R_172_13 : rowsJ2 172 173 51 340 ≤ 2804038752730035 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_4434 c22250R_172_14 (by norm_num)

theorem c22250R_172_12 : rowsJ2 172 173 50 340 ≤ 2818703850976401 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_4433 c22250R_172_13 (by norm_num)

theorem c22250R_172_11 : rowsJ2 172 173 49 340 ≤ 2835299049762709 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_4432 c22250R_172_12 (by norm_num)

theorem c22250R_172_10 : rowsJ2 172 173 48 340 ≤ 2853962680128837 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_4431 c22250R_172_11 (by norm_num)

theorem c22250R_172_9 : rowsJ2 172 173 47 340 ≤ 2874837765643399 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_4430 c22250R_172_10 (by norm_num)

theorem c22250R_172_8 : rowsJ2 172 173 46 340 ≤ 2898072412364916 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_4429 c22250R_172_9 (by norm_num)

theorem c22250R_172_7 : rowsJ2 172 173 45 340 ≤ 2919401145573791 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_4428 c22250R_172_8 (by norm_num)

theorem c22250R_172_6 : rowsJ2 172 173 44 340 ≤ 2938884865593893 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_4427 c22250R_172_7 (by norm_num)

theorem c22250R_172_5 : rowsJ2 172 173 43 340 ≤ 2956586015939382 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_4426 c22250R_172_6 (by norm_num)

theorem c22250R_172_4 : rowsJ2 172 173 42 340 ≤ 2972568849303669 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_4425 c22250R_172_5 (by norm_num)

theorem c22250R_172_3 : rowsJ2 172 173 41 340 ≤ 2986899705264801 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_4424 c22250R_172_4 (by norm_num)

theorem c22250R_172_2 : rowsJ2 172 173 39 340 ≤ 3010883040867916 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_4423 c22250R_172_3 (by norm_num)

theorem c22250R_172_1 : rowsJ2 172 173 37 340 ≤ 3029119950307190 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_4422 c22250R_172_2 (by norm_num)

theorem c22250R_172_0 : rowsJ2 172 173 0 340 ≤ 3049634350870382 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_4421 c22250R_172_1 (by norm_num)

theorem hr22250R_172 : rows2 172 173 ≤ 3049634350870382 := rows2_le_of_rowsJ2 172 173 c22250R_172_0

theorem c22250R_173_14 : rowsJ2 173 174 51 340 ≤ 2820619488220890 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_4451 rows22250R_4452 (by norm_num)

theorem c22250R_173_13 : rowsJ2 173 174 50 340 ≤ 2834671195166777 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_4450 c22250R_173_14 (by norm_num)

theorem c22250R_173_12 : rowsJ2 173 174 49 340 ≤ 2850625182318199 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_4449 c22250R_173_13 (by norm_num)

theorem c22250R_173_11 : rowsJ2 173 174 48 340 ≤ 2868620706907959 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_4448 c22250R_173_12 (by norm_num)

theorem c22250R_173_10 : rowsJ2 173 174 47 340 ≤ 2888801683095816 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_4447 c22250R_173_11 (by norm_num)

theorem c22250R_173_9 : rowsJ2 173 174 46 340 ≤ 2911317074689074 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_4446 c22250R_173_10 (by norm_num)

theorem c22250R_173_8 : rowsJ2 173 174 45 340 ≤ 2934077113315648 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_4445 c22250R_173_9 (by norm_num)

theorem c22250R_173_7 : rowsJ2 173 174 44 340 ≤ 2954923161469172 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_4444 c22250R_173_8 (by norm_num)

theorem c22250R_173_6 : rowsJ2 173 174 43 340 ≤ 2973918080458820 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_4443 c22250R_173_7 (by norm_num)

theorem c22250R_173_5 : rowsJ2 173 174 42 340 ≤ 2991126422520709 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_4442 c22250R_173_6 (by norm_num)

theorem c22250R_173_4 : rowsJ2 173 174 41 340 ≤ 3006614711075087 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_4441 c22250R_173_5 (by norm_num)

theorem c22250R_173_3 : rowsJ2 173 174 40 340 ≤ 3020451733944541 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_4440 c22250R_173_4 (by norm_num)

theorem c22250R_173_2 : rowsJ2 173 174 38 340 ≤ 3043460321975871 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_4439 c22250R_173_3 (by norm_num)

theorem c22250R_173_1 : rowsJ2 173 174 36 340 ≤ 3060759932064285 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_4438 c22250R_173_2 (by norm_num)

theorem c22250R_173_0 : rowsJ2 173 174 0 340 ≤ 3076462483908445 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_4437 c22250R_173_1 (by norm_num)

theorem hr22250R_173 : rows2 173 174 ≤ 3076462483908445 := rows2_le_of_rowsJ2 173 174 c22250R_173_0

theorem c22250R_174_13 : rowsJ2 174 175 50 340 ≤ 2851537993769298 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_4466 rows22250R_4467 (by norm_num)

theorem c22250R_174_12 : rowsJ2 174 175 49 340 ≤ 2866822676226723 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_4465 c22250R_174_13 (by norm_num)

theorem c22250R_174_11 : rowsJ2 174 175 48 340 ≤ 2884120900270264 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_4464 c22250R_174_12 (by norm_num)

theorem c22250R_174_10 : rowsJ2 174 175 47 340 ≤ 2903577511038715 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_4463 c22250R_174_11 (by norm_num)

theorem c22250R_174_9 : rowsJ2 174 175 46 340 ≤ 2925342368313206 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_4462 c22250R_174_10 (by norm_num)

theorem c22250R_174_8 : rowsJ2 174 175 45 340 ≤ 2949570767426466 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_4461 c22250R_174_9 (by norm_num)

theorem c22250R_174_7 : rowsJ2 174 175 44 340 ≤ 2971813804291975 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_4460 c22250R_174_8 (by norm_num)

theorem c22250R_174_6 : rowsJ2 174 175 43 340 ≤ 2992134844557698 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_4459 c22250R_174_7 (by norm_num)

theorem c22250R_174_5 : rowsJ2 174 175 42 340 ≤ 3010598819944172 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_4458 c22250R_174_6 (by norm_num)

theorem c22250R_174_4 : rowsJ2 174 175 41 340 ≤ 3027272511583150 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_4457 c22250R_174_5 (by norm_num)

theorem c22250R_174_3 : rowsJ2 174 175 40 340 ≤ 3042224845657483 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_4456 c22250R_174_4 (by norm_num)

theorem c22250R_174_2 : rowsJ2 174 175 38 340 ≤ 3067253747333921 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_4455 c22250R_174_3 (by norm_num)

theorem c22250R_174_1 : rowsJ2 174 175 36 340 ≤ 3086292043862322 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_4454 c22250R_174_2 (by norm_num)

theorem c22250R_174_0 : rowsJ2 174 175 0 340 ≤ 3104671343184766 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_4453 c22250R_174_1 (by norm_num)

theorem hr22250R_174 : rows2 174 175 ≤ 3104671343184766 := rows2_le_of_rowsJ2 174 175 c22250R_174_0

theorem c22250R_175_13 : rowsJ2 175 176 50 340 ≤ 2862863822394072 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_4481 rows22250R_4482 (by norm_num)

theorem c22250R_175_12 : rowsJ2 175 176 49 340 ≤ 2877513899018371 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_4480 c22250R_175_13 (by norm_num)

theorem c22250R_175_11 : rowsJ2 175 176 48 340 ≤ 2894149032854733 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_4479 c22250R_175_12 (by norm_num)

theorem c22250R_175_10 : rowsJ2 175 176 47 340 ≤ 2912915056913110 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_4478 c22250R_175_11 (by norm_num)

theorem c22250R_175_9 : rowsJ2 175 176 46 340 ≤ 2933962781968643 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_4477 c22250R_175_10 (by norm_num)

theorem c22250R_175_8 : rowsJ2 175 176 45 340 ≤ 2957448420487152 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_4476 c22250R_175_9 (by norm_num)

theorem c22250R_175_7 : rowsJ2 175 176 44 340 ≤ 2981192051807547 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_4475 c22250R_175_8 (by norm_num)

theorem c22250R_175_6 : rowsJ2 175 176 43 340 ≤ 3002941117191756 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_4474 c22250R_175_7 (by norm_num)

theorem c22250R_175_5 : rowsJ2 175 176 42 340 ≤ 3022761031603860 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_4473 c22250R_175_6 (by norm_num)

theorem c22250R_175_4 : rowsJ2 175 176 41 340 ≤ 3040718931515808 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_4472 c22250R_175_5 (by norm_num)

theorem c22250R_175_3 : rowsJ2 175 176 40 340 ≤ 3056883973529696 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_4471 c22250R_175_4 (by norm_num)

theorem c22250R_175_2 : rowsJ2 175 176 38 340 ≤ 3084124100345090 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_4470 c22250R_175_3 (by norm_num)

theorem c22250R_175_1 : rowsJ2 175 176 36 340 ≤ 3105087347613353 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_4469 c22250R_175_2 (by norm_num)

theorem c22250R_175_0 : rowsJ2 175 176 0 340 ≤ 3126412174463859 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_4468 c22250R_175_1 (by norm_num)

theorem hr22250R_175 : rows2 175 176 ≤ 3126412174463859 := rows2_le_of_rowsJ2 175 176 c22250R_175_0

theorem c22250R_176_13 : rowsJ2 176 177 49 340 ≤ 2888903311054182 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_4496 rows22250R_4497 (by norm_num)

theorem c22250R_176_12 : rowsJ2 176 177 48 340 ≤ 2904845670388209 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_4495 c22250R_176_13 (by norm_num)

theorem c22250R_176_11 : rowsJ2 176 177 47 340 ≤ 2922890264955129 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_4494 c22250R_176_12 (by norm_num)

theorem c22250R_176_10 : rowsJ2 176 177 46 340 ≤ 2943188899399003 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_4493 c22250R_176_11 (by norm_num)

theorem c22250R_176_9 : rowsJ2 176 177 45 340 ≤ 2965898743878150 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_4492 c22250R_176_10 (by norm_num)

theorem c22250R_176_8 : rowsJ2 176 177 44 340 ≤ 2991182789058147 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_4491 c22250R_176_9 (by norm_num)

theorem c22250R_176_7 : rowsJ2 176 177 43 340 ≤ 3014397116555432 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_4490 c22250R_176_8 (by norm_num)

theorem c22250R_176_6 : rowsJ2 176 177 42 340 ≤ 3035607719777253 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_4489 c22250R_176_7 (by norm_num)

theorem c22250R_176_5 : rowsJ2 176 177 41 340 ≤ 3054882178340411 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_4488 c22250R_176_6 (by norm_num)

theorem c22250R_176_4 : rowsJ2 176 177 40 340 ≤ 3072289960278712 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_4487 c22250R_176_5 (by norm_num)

theorem c22250R_176_3 : rowsJ2 176 177 39 340 ≤ 3087902737155654 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_4486 c22250R_176_4 (by norm_num)

theorem c22250R_176_2 : rowsJ2 176 177 37 340 ≤ 3114042978465640 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_4485 c22250R_176_3 (by norm_num)

theorem c22250R_176_1 : rowsJ2 176 177 35 340 ≤ 3133022125650123 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_4484 c22250R_176_2 (by norm_num)

theorem c22250R_176_0 : rowsJ2 176 177 0 340 ≤ 3149349564267919 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_4483 c22250R_176_1 (by norm_num)

theorem hr22250R_176 : rows2 176 177 ≤ 3149349564267919 := rows2_le_of_rowsJ2 176 177 c22250R_176_0

theorem c22250R_177_12 : rowsJ2 177 178 48 340 ≤ 2916463914290455 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_4510 rows22250R_4511 (by norm_num)

theorem c22250R_177_11 : rowsJ2 177 178 47 340 ≤ 2933822432523514 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_4509 c22250R_177_12 (by norm_num)

theorem c22250R_177_10 : rowsJ2 177 178 46 340 ≤ 2953406878297316 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_4508 c22250R_177_11 (by norm_num)

theorem c22250R_177_9 : rowsJ2 177 178 45 340 ≤ 2975375437960258 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_4507 c22250R_177_10 (by norm_num)

theorem c22250R_177_8 : rowsJ2 177 178 44 340 ≤ 2999892083490051 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_4506 c22250R_177_9 (by norm_num)

theorem c22250R_177_7 : rowsJ2 177 178 43 340 ≤ 3024681038928051 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_4505 c22250R_177_8 (by norm_num)

theorem c22250R_177_6 : rowsJ2 177 178 42 340 ≤ 3047389844464339 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_4504 c22250R_177_7 (by norm_num)

theorem c22250R_177_5 : rowsJ2 177 178 41 340 ≤ 3068086636498489 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_4503 c22250R_177_6 (by norm_num)

theorem c22250R_177_4 : rowsJ2 177 178 40 340 ≤ 3086841301243161 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_4502 c22250R_177_5 (by norm_num)

theorem c22250R_177_3 : rowsJ2 177 178 39 340 ≤ 3103725793318886 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_4501 c22250R_177_4 (by norm_num)

theorem c22250R_177_2 : rowsJ2 177 178 37 340 ≤ 3132184434437504 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_4500 c22250R_177_3 (by norm_num)

theorem c22250R_177_1 : rowsJ2 177 178 35 340 ≤ 3153080312532451 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_4499 c22250R_177_2 (by norm_num)

theorem c22250R_177_0 : rowsJ2 177 178 0 340 ≤ 3172196754426062 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_4498 c22250R_177_1 (by norm_num)

theorem hr22250R_177 : rows2 177 178 ≤ 3172196754426062 := rows2_le_of_rowsJ2 177 178 c22250R_177_0

theorem c22250R_178_12 : rowsJ2 178 179 48 340 ≤ 2929376225111957 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_4524 rows22250R_4525 (by norm_num)

theorem c22250R_178_11 : rowsJ2 178 179 47 340 ≤ 2946017280477837 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_4523 c22250R_178_12 (by norm_num)

theorem c22250R_178_10 : rowsJ2 178 179 46 340 ≤ 2964854932346016 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_4522 c22250R_178_11 (by norm_num)

theorem c22250R_178_9 : rowsJ2 178 179 45 340 ≤ 2986048428815275 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_4521 c22250R_178_10 (by norm_num)

theorem c22250R_178_8 : rowsJ2 178 179 44 340 ≤ 3009762766255717 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_4520 c22250R_178_9 (by norm_num)

theorem c22250R_178_7 : rowsJ2 178 179 43 340 ≤ 3036169181905940 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_4519 c22250R_178_8 (by norm_num)

theorem c22250R_178_6 : rowsJ2 178 179 42 340 ≤ 3060416233391642 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_4518 c22250R_178_7 (by norm_num)

theorem c22250R_178_5 : rowsJ2 178 179 41 340 ≤ 3082572718829333 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_4517 c22250R_178_6 (by norm_num)

theorem c22250R_178_4 : rowsJ2 178 179 40 340 ≤ 3102709039245292 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_4516 c22250R_178_5 (by norm_num)

theorem c22250R_178_3 : rowsJ2 178 179 39 340 ≤ 3120897521340087 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_4515 c22250R_178_4 (by norm_num)

theorem c22250R_178_2 : rowsJ2 178 179 37 340 ≤ 3151731939431773 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_4514 c22250R_178_3 (by norm_num)

theorem c22250R_178_1 : rowsJ2 178 179 35 340 ≤ 3174666780977428 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_4513 c22250R_178_2 (by norm_num)

theorem c22250R_178_0 : rowsJ2 178 179 0 340 ≤ 3196853592102615 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_4512 c22250R_178_1 (by norm_num)

theorem hr22250R_178 : rows2 178 179 ≤ 3196853592102615 := rows2_le_of_rowsJ2 178 179 c22250R_178_0

theorem c22250R_179_11 : rowsJ2 179 180 47 340 ≤ 3068835822947100 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_4537 rows22250R_4538 (by norm_num)

theorem c22250R_179_10 : rowsJ2 179 180 46 340 ≤ 3086963238606736 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_4536 c22250R_179_11 (by norm_num)

theorem c22250R_179_9 : rowsJ2 179 180 45 340 ≤ 3107417758084525 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_4535 c22250R_179_10 (by norm_num)

theorem c22250R_179_8 : rowsJ2 179 180 44 340 ≤ 3130365464401184 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_4534 c22250R_179_9 (by norm_num)

theorem c22250R_179_7 : rowsJ2 179 180 43 340 ≤ 3155978645562249 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_4533 c22250R_179_8 (by norm_num)

theorem c22250R_179_6 : rowsJ2 179 180 42 340 ≤ 3181879511365204 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_4532 c22250R_179_7 (by norm_num)

theorem c22250R_179_5 : rowsJ2 179 180 41 340 ≤ 3205609240178709 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_4531 c22250R_179_6 (by norm_num)

theorem c22250R_179_4 : rowsJ2 179 180 40 340 ≤ 3227238872549689 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_4530 c22250R_179_5 (by norm_num)

theorem c22250R_179_3 : rowsJ2 179 180 39 340 ≤ 3246841224205786 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_4529 c22250R_179_4 (by norm_num)

theorem c22250R_179_2 : rowsJ2 179 180 37 340 ≤ 3280266281400394 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_4528 c22250R_179_3 (by norm_num)

theorem c22250R_179_1 : rowsJ2 179 180 34 340 ≤ 3314000838132424 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_4527 c22250R_179_2 (by norm_num)

theorem c22250R_179_0 : rowsJ2 179 180 0 340 ≤ 3330993055530279 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_4526 c22250R_179_1 (by norm_num)

theorem hr22250R_179 : rows2 179 180 ≤ 3330993055530279 := rows2_le_of_rowsJ2 179 180 c22250R_179_0

theorem c22250R_180_11 : rowsJ2 180 181 46 340 ≤ 3207302664328565 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_4550 rows22250R_4551 (by norm_num)

theorem c22250R_180_10 : rowsJ2 180 181 45 340 ≤ 3226983715072287 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_4549 c22250R_180_11 (by norm_num)

theorem c22250R_180_9 : rowsJ2 180 181 44 340 ≤ 3249129064382277 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_4548 c22250R_180_10 (by norm_num)

theorem c22250R_180_8 : rowsJ2 180 181 43 340 ≤ 3273912096836401 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_4547 c22250R_180_9 (by norm_num)

theorem c22250R_180_7 : rowsJ2 180 181 42 340 ≤ 3301512897618526 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_4546 c22250R_180_8 (by norm_num)

theorem c22250R_180_6 : rowsJ2 180 181 41 340 ≤ 3326858975129711 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_4545 c22250R_180_7 (by norm_num)

theorem c22250R_180_5 : rowsJ2 180 181 40 340 ≤ 3350022125342877 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_4544 c22250R_180_6 (by norm_num)

theorem c22250R_180_4 : rowsJ2 180 181 39 340 ≤ 3371075759584365 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_4543 c22250R_180_5 (by norm_num)

theorem c22250R_180_3 : rowsJ2 180 181 38 340 ≤ 3390095249736137 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_4542 c22250R_180_4 (by norm_num)

theorem c22250R_180_2 : rowsJ2 180 181 36 340 ≤ 3422345261058399 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_4541 c22250R_180_3 (by norm_num)

theorem c22250R_180_1 : rowsJ2 180 181 34 340 ≤ 3444101653842913 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_4540 c22250R_180_2 (by norm_num)

theorem c22250R_180_0 : rowsJ2 180 181 0 340 ≤ 3464002504762525 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_4539 c22250R_180_1 (by norm_num)

theorem hr22250R_180 : rows2 180 181 ≤ 3464002504762525 := rows2_le_of_rowsJ2 180 181 c22250R_180_0

theorem c22250R_181_10 : rowsJ2 181 182 45 340 ≤ 3344951425309446 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_4562 rows22250R_4563 (by norm_num)

theorem c22250R_181_9 : rowsJ2 181 182 44 340 ≤ 3366331753338126 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_4561 c22250R_181_10 (by norm_num)

theorem c22250R_181_8 : rowsJ2 181 182 43 340 ≤ 3390321546677176 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_4560 c22250R_181_9 (by norm_num)

theorem c22250R_181_7 : rowsJ2 181 182 42 340 ≤ 3417102016546512 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_4559 c22250R_181_8 (by norm_num)

theorem c22250R_181_6 : rowsJ2 181 182 41 340 ≤ 3444186698808234 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_4558 c22250R_181_7 (by norm_num)

theorem c22250R_181_5 : rowsJ2 181 182 40 340 ≤ 3469003420850904 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_4557 c22250R_181_6 (by norm_num)

theorem c22250R_181_4 : rowsJ2 181 182 39 340 ≤ 3491626326736620 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_4556 c22250R_181_5 (by norm_num)

theorem c22250R_181_3 : rowsJ2 181 182 38 340 ≤ 3512131357348802 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_4555 c22250R_181_4 (by norm_num)

theorem c22250R_181_2 : rowsJ2 181 182 36 340 ≤ 3547102740843388 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_4554 c22250R_181_3 (by norm_num)

theorem c22250R_181_1 : rowsJ2 181 182 34 340 ≤ 3570990085810147 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_4553 c22250R_181_2 (by norm_num)

theorem c22250R_181_0 : rowsJ2 181 182 0 340 ≤ 3594094401692722 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_4552 c22250R_181_1 (by norm_num)

theorem hr22250R_181 : rows2 181 182 ≤ 3594094401692722 := rows2_le_of_rowsJ2 181 182 c22250R_181_0

theorem c22250R_182_9 : rowsJ2 182 183 44 340 ≤ 3481671459320590 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_4573 rows22250R_4574 (by norm_num)

theorem c22250R_182_8 : rowsJ2 182 183 43 340 ≤ 3504830201843532 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_4572 c22250R_182_9 (by norm_num)

theorem c22250R_182_7 : rowsJ2 182 183 42 340 ≤ 3530751279005113 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_4571 c22250R_182_8 (by norm_num)

theorem c22250R_182_6 : rowsJ2 182 183 41 340 ≤ 3559624281035743 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_4570 c22250R_182_7 (by norm_num)

theorem c22250R_182_5 : rowsJ2 182 183 40 340 ≤ 3586141024930268 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_4569 c22250R_182_6 (by norm_num)

theorem c22250R_182_4 : rowsJ2 182 183 39 340 ≤ 3610376515784379 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_4568 c22250R_182_5 (by norm_num)

theorem c22250R_182_3 : rowsJ2 182 183 38 340 ≤ 3632407381261548 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_4567 c22250R_182_4 (by norm_num)

theorem c22250R_182_2 : rowsJ2 182 183 36 340 ≤ 3670172092814126 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_4566 c22250R_182_3 (by norm_num)

theorem c22250R_182_1 : rowsJ2 182 183 33 340 ≤ 3705318375678787 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_4565 c22250R_182_2 (by norm_num)

theorem c22250R_182_0 : rowsJ2 182 183 0 340 ≤ 3723018344074615 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_4564 c22250R_182_1 (by norm_num)

theorem hr22250R_182 : rows2 182 183 ≤ 3723018344074615 := rows2_le_of_rowsJ2 182 183 c22250R_182_0

theorem c22250R_183_9 : rowsJ2 183 184 43 340 ≤ 3617647263684552 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_4584 rows22250R_4585 (by norm_num)

theorem c22250R_183_8 : rowsJ2 183 184 42 340 ≤ 3642747159897800 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_4583 c22250R_183_9 (by norm_num)

theorem c22250R_183_7 : rowsJ2 183 184 41 340 ≤ 3670771403444712 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_4582 c22250R_183_8 (by norm_num)

theorem c22250R_183_6 : rowsJ2 183 184 40 340 ≤ 3699117645755284 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_4581 c22250R_183_7 (by norm_num)

theorem c22250R_183_5 : rowsJ2 183 184 39 340 ≤ 3725092792578531 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_4580 c22250R_183_6 (by norm_num)

theorem c22250R_183_4 : rowsJ2 183 184 38 340 ≤ 3748774309484792 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_4579 c22250R_183_5 (by norm_num)

theorem c22250R_183_3 : rowsJ2 183 184 37 340 ≤ 3770241475838502 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_4578 c22250R_183_4 (by norm_num)

theorem c22250R_183_2 : rowsJ2 183 184 35 340 ≤ 3805405278908214 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_4577 c22250R_183_3 (by norm_num)

theorem c22250R_183_1 : rowsJ2 183 184 33 340 ≤ 3828078357843507 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_4576 c22250R_183_2 (by norm_num)

theorem c22250R_183_0 : rowsJ2 183 184 0 340 ≤ 3848814555963203 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_4575 c22250R_183_1 (by norm_num)

theorem hr22250R_183 : rows2 183 184 ≤ 3848814555963203 := rows2_le_of_rowsJ2 183 184 c22250R_183_0

theorem c22250R_184_8 : rowsJ2 184 185 42 340 ≤ 3752761611197745 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_4594 rows22250R_4595 (by norm_num)

theorem c22250R_184_7 : rowsJ2 184 185 41 340 ≤ 3779895732997961 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_4593 c22250R_184_8 (by norm_num)

theorem c22250R_184_6 : rowsJ2 184 185 40 340 ≤ 3810125123468802 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_4592 c22250R_184_7 (by norm_num)

theorem c22250R_184_5 : rowsJ2 184 185 39 340 ≤ 3837890035570717 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_4591 c22250R_184_6 (by norm_num)

theorem c22250R_184_4 : rowsJ2 184 185 38 340 ≤ 3863268915109116 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_4590 c22250R_184_5 (by norm_num)

theorem c22250R_184_3 : rowsJ2 184 185 37 340 ≤ 3886341831287866 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_4589 c22250R_184_4 (by norm_num)

theorem c22250R_184_2 : rowsJ2 184 185 35 340 ≤ 3924401580111774 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_4588 c22250R_184_3 (by norm_num)

theorem c22250R_184_1 : rowsJ2 184 185 33 340 ≤ 3949303942423499 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_4587 c22250R_184_2 (by norm_num)

theorem c22250R_184_0 : rowsJ2 184 185 0 340 ≤ 3973385622751394 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_4586 c22250R_184_1 (by norm_num)

theorem hr22250R_184 : rows2 184 185 ≤ 3973385622751394 := rows2_le_of_rowsJ2 184 185 c22250R_184_0

theorem c22250R_185_7 : rowsJ2 185 186 41 340 ≤ 3887209910860436 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_4603 rows22250R_4604 (by norm_num)

theorem c22250R_185_6 : rowsJ2 185 186 40 340 ≤ 3916560710661085 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_4602 c22250R_185_7 (by norm_num)

theorem c22250R_185_5 : rowsJ2 185 186 39 340 ≤ 3946252671307087 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_4601 c22250R_185_6 (by norm_num)

theorem c22250R_185_4 : rowsJ2 185 186 38 340 ≤ 3973463565291799 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_4600 c22250R_185_5 (by norm_num)

theorem c22250R_185_3 : rowsJ2 185 186 37 340 ≤ 3998274418567415 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_4599 c22250R_185_4 (by norm_num)

theorem c22250R_185_2 : rowsJ2 185 186 35 340 ≤ 4039397137269617 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_4598 c22250R_185_3 (by norm_num)

theorem c22250R_185_1 : rowsJ2 185 186 32 340 ≤ 4076048208619468 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_4597 c22250R_185_2 (by norm_num)

theorem c22250R_185_0 : rowsJ2 185 186 0 340 ≤ 4094502274256218 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_4596 c22250R_185_1 (by norm_num)

theorem hr22250R_185 : rows2 185 186 ≤ 4094502274256218 := rows2_le_of_rowsJ2 185 186 c22250R_185_0

theorem c22250R_186_6 : rowsJ2 186 187 40 340 ≤ 4020868137148500 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_4611 rows22250R_4612 (by norm_num)

theorem c22250R_186_5 : rowsJ2 186 187 39 340 ≤ 4052545110140337 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_4610 c22250R_186_6 (by norm_num)

theorem c22250R_186_4 : rowsJ2 186 187 38 340 ≤ 4081642137472729 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_4609 c22250R_186_5 (by norm_num)

theorem c22250R_186_3 : rowsJ2 186 187 37 340 ≤ 4108241360097471 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_4608 c22250R_186_4 (by norm_num)

theorem c22250R_186_2 : rowsJ2 186 187 35 340 ≤ 4152601156052185 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_4607 c22250R_186_3 (by norm_num)

theorem c22250R_186_1 : rowsJ2 186 187 32 340 ≤ 4192766319258367 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_4606 c22250R_186_2 (by norm_num)

theorem c22250R_186_0 : rowsJ2 186 187 0 340 ≤ 4214392826527452 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_4605 c22250R_186_1 (by norm_num)

theorem hr22250R_186 : rows2 186 187 ≤ 4214392826527452 := rows2_le_of_rowsJ2 186 187 c22250R_186_0

theorem c22250R_187_6 : rowsJ2 187 188 39 340 ≤ 4153943852237175 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_4619 rows22250R_4620 (by norm_num)

theorem c22250R_187_5 : rowsJ2 187 188 38 340 ≤ 4185072748920088 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_4618 c22250R_187_6 (by norm_num)

theorem c22250R_187_4 : rowsJ2 187 188 37 340 ≤ 4213603194217768 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_4617 c22250R_187_5 (by norm_num)

theorem c22250R_187_3 : rowsJ2 187 188 36 340 ≤ 4239620036809117 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_4616 c22250R_187_4 (by norm_num)

theorem c22250R_187_2 : rowsJ2 187 188 34 340 ≤ 4279345991720325 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_4615 c22250R_187_3 (by norm_num)

theorem c22250R_187_1 : rowsJ2 187 188 32 340 ≤ 4305330896758269 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_4614 c22250R_187_2 (by norm_num)

theorem c22250R_187_0 : rowsJ2 187 188 0 340 ≤ 4330454558686029 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_4613 c22250R_187_1 (by norm_num)

theorem hr22250R_187 : rows2 187 188 ≤ 4330454558686029 := rows2_le_of_rowsJ2 187 188 c22250R_187_0

theorem c22250R_188_5 : rowsJ2 188 189 38 340 ≤ 4286165326592889 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22250R_4626 rows22250R_4627 (by norm_num)

theorem c22250R_188_4 : rowsJ2 188 189 37 340 ≤ 4316685513855185 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22250R_4625 c22250R_188_5 (by norm_num)

theorem c22250R_188_3 : rowsJ2 188 189 36 340 ≤ 4344588537231654 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22250R_4624 c22250R_188_4 (by norm_num)

theorem c22250R_188_2 : rowsJ2 188 189 34 340 ≤ 4387528121676695 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22250R_4623 c22250R_188_3 (by norm_num)

theorem c22250R_188_1 : rowsJ2 188 189 32 340 ≤ 4415998243817575 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22250R_4622 c22250R_188_2 (by norm_num)

theorem c22250R_188_0 : rowsJ2 188 189 0 340 ≤ 4445042755741974 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22250R_4621 c22250R_188_1 (by norm_num)

theorem hr22250R_188 : rows2 188 189 ≤ 4445042755741974 := rows2_le_of_rowsJ2 188 189 c22250R_188_0

theorem c22250R_189_4 : rowsJ2 189 190 37 340 ≤ 4414656912905524 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22250R_4632 rows22250R_4633 (by norm_num)

theorem c22250R_189_3 : rowsJ2 189 190 36 340 ≤ 4444597856451639 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22250R_4631 c22250R_189_4 (by norm_num)

theorem c22250R_189_2 : rowsJ2 189 190 34 340 ≤ 4490935804258677 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22250R_4630 c22250R_189_3 (by norm_num)

theorem c22250R_189_1 : rowsJ2 189 190 31 340 ≤ 4532875304650358 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22250R_4629 c22250R_189_2 (by norm_num)

theorem c22250R_189_0 : rowsJ2 189 190 0 340 ≤ 4555451498058402 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22250R_4628 c22250R_189_1 (by norm_num)

theorem hr22250R_189 : rows2 189 190 ≤ 4555451498058402 := rows2_le_of_rowsJ2 189 190 c22250R_189_0

theorem c22250R_190_3 : rowsJ2 190 191 36 340 ≤ 4542161838959069 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22250R_4637 rows22250R_4638 (by norm_num)

theorem c22250R_190_2 : rowsJ2 190 191 34 340 ≤ 4592093050380882 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22250R_4636 c22250R_190_3 (by norm_num)

theorem c22250R_190_1 : rowsJ2 190 191 31 340 ≤ 4637998668452824 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22250R_4635 c22250R_190_2 (by norm_num)

theorem c22250R_190_0 : rowsJ2 190 191 0 340 ≤ 4664234151730231 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22250R_4634 c22250R_190_1 (by norm_num)

theorem hr22250R_190 : rows2 190 191 ≤ 4664234151730231 := rows2_le_of_rowsJ2 190 191 c22250R_190_0

theorem c22250R_191_3 : rowsJ2 191 192 35 340 ≤ 4663816365030896 :=
  rowsJ2_le_of_split 191 192 (by norm_num) (by norm_num) rows22250R_4642 rows22250R_4643 (by norm_num)

theorem c22250R_191_2 : rowsJ2 191 192 33 340 ≤ 4708697265227417 :=
  rowsJ2_le_of_split 191 192 (by norm_num) (by norm_num) rows22250R_4641 c22250R_191_3 (by norm_num)

theorem c22250R_191_1 : rowsJ2 191 192 31 340 ≤ 4738444396793053 :=
  rowsJ2_le_of_split 191 192 (by norm_num) (by norm_num) rows22250R_4640 c22250R_191_2 (by norm_num)

theorem c22250R_191_0 : rowsJ2 191 192 0 340 ≤ 4768784318570601 :=
  rowsJ2_le_of_split 191 192 (by norm_num) (by norm_num) rows22250R_4639 c22250R_191_1 (by norm_num)

theorem hr22250R_191 : rows2 191 192 ≤ 4768784318570601 := rows2_le_of_rowsJ2 191 192 c22250R_191_0

theorem c22250R_192_2 : rowsJ2 192 193 33 340 ≤ 4804502020648375 :=
  rowsJ2_le_of_split 192 193 (by norm_num) (by norm_num) rows22250R_4646 rows22250R_4647 (by norm_num)

theorem c22250R_192_1 : rowsJ2 192 193 30 340 ≤ 4848336847955004 :=
  rowsJ2_le_of_split 192 193 (by norm_num) (by norm_num) rows22250R_4645 c22250R_192_2 (by norm_num)

theorem c22250R_192_0 : rowsJ2 192 193 0 340 ≤ 4871926955065996 :=
  rowsJ2_le_of_split 192 193 (by norm_num) (by norm_num) rows22250R_4644 c22250R_192_1 (by norm_num)

theorem hr22250R_192 : rows2 192 193 ≤ 4871926955065996 := rows2_le_of_rowsJ2 192 193 c22250R_192_0

theorem c22250R_193_2 : rowsJ2 193 194 33 340 ≤ 4900379295543511 :=
  rowsJ2_le_of_split 193 194 (by norm_num) (by norm_num) rows22250R_4650 rows22250R_4651 (by norm_num)

theorem c22250R_193_1 : rowsJ2 193 194 30 340 ≤ 4948377569454592 :=
  rowsJ2_le_of_split 193 194 (by norm_num) (by norm_num) rows22250R_4649 c22250R_193_2 (by norm_num)

theorem c22250R_193_0 : rowsJ2 193 194 0 340 ≤ 4975800454506848 :=
  rowsJ2_le_of_split 193 194 (by norm_num) (by norm_num) rows22250R_4648 c22250R_193_1 (by norm_num)

theorem hr22250R_193 : rows2 193 194 ≤ 4975800454506848 := rows2_le_of_rowsJ2 193 194 c22250R_193_0

theorem c22250R_194_1 : rowsJ2 194 195 30 340 ≤ 5048675225820905 :=
  rowsJ2_le_of_split 194 195 (by norm_num) (by norm_num) rows22250R_4653 rows22250R_4654 (by norm_num)

theorem c22250R_194_0 : rowsJ2 194 195 0 340 ≤ 5080399083099111 :=
  rowsJ2_le_of_split 194 195 (by norm_num) (by norm_num) rows22250R_4652 c22250R_194_1 (by norm_num)

theorem hr22250R_194 : rows2 194 195 ≤ 5080399083099111 := rows2_le_of_rowsJ2 194 195 c22250R_194_0

theorem c22250R_195_1 : rowsJ2 195 196 29 340 ≤ 5161193498020468 :=
  rowsJ2_le_of_split 195 196 (by norm_num) (by norm_num) rows22250R_4656 rows22250R_4657 (by norm_num)

theorem c22250R_195_0 : rowsJ2 195 196 0 340 ≤ 5185867082574668 :=
  rowsJ2_le_of_split 195 196 (by norm_num) (by norm_num) rows22250R_4655 c22250R_195_1 (by norm_num)

theorem hr22250R_195 : rows2 195 196 ≤ 5185867082574668 := rows2_le_of_rowsJ2 195 196 c22250R_195_0

theorem c22250R_196_1 : rowsJ2 196 197 29 340 ≤ 5263415237298786 :=
  rowsJ2_le_of_split 196 197 (by norm_num) (by norm_num) rows22250R_4659 rows22250R_4660 (by norm_num)

theorem c22250R_196_0 : rowsJ2 196 197 0 340 ≤ 5292107423236596 :=
  rowsJ2_le_of_split 196 197 (by norm_num) (by norm_num) rows22250R_4658 c22250R_196_1 (by norm_num)

theorem hr22250R_196 : rows2 196 197 ≤ 5292107423236596 := rows2_le_of_rowsJ2 196 197 c22250R_196_0

theorem c22250R_197_0 : rowsJ2 197 198 0 340 ≤ 5399113549789000 :=
  rowsJ2_le_of_split 197 198 (by norm_num) (by norm_num) rows22250R_4661 rows22250R_4662 (by norm_num)

theorem hr22250R_197 : rows2 197 198 ≤ 5399113549789000 := rows2_le_of_rowsJ2 197 198 c22250R_197_0

theorem c22250R_198_0 : rowsJ2 198 199 0 340 ≤ 5506878799614943 :=
  rowsJ2_le_of_split 198 199 (by norm_num) (by norm_num) rows22250R_4663 rows22250R_4664 (by norm_num)

theorem hr22250R_198 : rows2 198 199 ≤ 5506878799614943 := rows2_le_of_rowsJ2 198 199 c22250R_198_0

theorem c22250R_199_0 : rowsJ2 199 200 0 340 ≤ 5616638750013342 :=
  rowsJ2_le_of_split 199 200 (by norm_num) (by norm_num) rows22250R_4665 rows22250R_4666 (by norm_num)

theorem hr22250R_199 : rows2 199 200 ≤ 5616638750013342 := rows2_le_of_rowsJ2 199 200 c22250R_199_0

theorem c22250R_200_0 : rowsJ2 200 201 0 340 ≤ 5728389492127996 :=
  rowsJ2_le_of_split 200 201 (by norm_num) (by norm_num) rows22250R_4667 rows22250R_4668 (by norm_num)

theorem hr22250R_200 : rows2 200 201 ≤ 5728389492127996 := rows2_le_of_rowsJ2 200 201 c22250R_200_0

theorem t22250R_235 : rows2 335 340 ≤ 69340507543233641 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4713 rows22250R_4714 (by norm_num)

theorem t22250R_234 : rows2 332 340 ≤ 108161795360473137 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4712 t22250R_235 (by norm_num)

theorem t22250R_233 : rows2 329 340 ≤ 145064107750415618 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4711 t22250R_234 (by norm_num)

theorem t22250R_232 : rows2 326 340 ≤ 180259938942783158 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4710 t22250R_233 (by norm_num)

theorem t22250R_231 : rows2 323 340 ≤ 213824072758953720 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4709 t22250R_232 (by norm_num)

theorem t22250R_230 : rows2 274 340 ≤ 246064363729939375 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4708 t22250R_231 (by norm_num)

theorem t22250R_229 : rows2 271 340 ≤ 278223133498086849 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4707 t22250R_230 (by norm_num)

theorem t22250R_228 : rows2 269 340 ≤ 299479486812643017 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4706 t22250R_229 (by norm_num)

theorem t22250R_227 : rows2 267 340 ≤ 320616108032710517 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4705 t22250R_228 (by norm_num)

theorem t22250R_226 : rows2 265 340 ≤ 341630499914671307 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4704 t22250R_227 (by norm_num)

theorem t22250R_225 : rows2 263 340 ≤ 362528014779693589 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4703 t22250R_226 (by norm_num)

theorem t22250R_224 : rows2 261 340 ≤ 383299665355857846 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4702 t22250R_225 (by norm_num)

theorem t22250R_223 : rows2 259 340 ≤ 403944449118335253 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4701 t22250R_224 (by norm_num)

theorem t22250R_222 : rows2 257 340 ≤ 424468998064724206 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4700 t22250R_223 (by norm_num)

theorem t22250R_221 : rows2 255 340 ≤ 444865521168514333 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4699 t22250R_222 (by norm_num)

theorem t22250R_220 : rows2 253 340 ≤ 465134029807842980 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4698 t22250R_221 (by norm_num)

theorem t22250R_219 : rows2 251 340 ≤ 485282018046875574 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4697 t22250R_220 (by norm_num)

theorem t22250R_218 : rows2 249 340 ≤ 505302513662078069 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4696 t22250R_219 (by norm_num)

theorem t22250R_217 : rows2 247 340 ≤ 525196213897703772 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4695 t22250R_218 (by norm_num)

theorem t22250R_216 : rows2 245 340 ≤ 544971190382464910 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4694 t22250R_217 (by norm_num)

theorem t22250R_215 : rows2 243 340 ≤ 564621028457049462 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4693 t22250R_216 (by norm_num)

theorem t22250R_214 : rows2 241 340 ≤ 584154077746998634 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4692 t22250R_215 (by norm_num)

theorem t22250R_213 : rows2 239 340 ≤ 603584493972353343 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4691 t22250R_214 (by norm_num)

theorem t22250R_212 : rows2 237 340 ≤ 622911357826908037 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4690 t22250R_213 (by norm_num)

theorem t22250R_211 : rows2 235 340 ≤ 641923126369337747 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4689 t22250R_212 (by norm_num)

theorem t22250R_210 : rows2 233 340 ≤ 660425546917292578 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4688 t22250R_211 (by norm_num)

theorem t22250R_209 : rows2 231 340 ≤ 678441840529567745 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4687 t22250R_210 (by norm_num)

theorem t22250R_208 : rows2 229 340 ≤ 695993507099193498 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4686 t22250R_209 (by norm_num)

theorem t22250R_207 : rows2 227 340 ≤ 713100485136823594 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4685 t22250R_208 (by norm_num)

theorem t22250R_206 : rows2 225 340 ≤ 729781293561905060 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4684 t22250R_207 (by norm_num)

theorem t22250R_205 : rows2 223 340 ≤ 746053157838593003 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4683 t22250R_206 (by norm_num)

theorem t22250R_204 : rows2 221 340 ≤ 761932122449687290 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4682 t22250R_205 (by norm_num)

theorem t22250R_203 : rows2 219 340 ≤ 777438750789905444 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4681 t22250R_204 (by norm_num)

theorem t22250R_202 : rows2 217 340 ≤ 792598123726076295 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4680 t22250R_203 (by norm_num)

theorem t22250R_201 : rows2 215 340 ≤ 807434276548356600 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4679 t22250R_202 (by norm_num)

theorem t22250R_200 : rows2 213 340 ≤ 821970286176717542 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4678 t22250R_201 (by norm_num)

theorem t22250R_199 : rows2 211 340 ≤ 836228350779285176 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4677 t22250R_200 (by norm_num)

theorem t22250R_198 : rows2 209 340 ≤ 850073217529772369 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4676 t22250R_199 (by norm_num)

theorem t22250R_197 : rows2 207 340 ≤ 863369625390280246 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4675 t22250R_198 (by norm_num)

theorem t22250R_196 : rows2 206 340 ≤ 869819703418024102 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4674 t22250R_197 (by norm_num)

theorem t22250R_195 : rows2 205 340 ≤ 876141882170567956 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4673 t22250R_196 (by norm_num)

theorem t22250R_194 : rows2 204 340 ≤ 882339347333346658 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4672 t22250R_195 (by norm_num)

theorem t22250R_193 : rows2 203 340 ≤ 888415295876381211 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4671 t22250R_194 (by norm_num)

theorem t22250R_192 : rows2 202 340 ≤ 894373037301967115 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4670 t22250R_193 (by norm_num)

theorem t22250R_191 : rows2 201 340 ≤ 900215163689937820 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_4669 t22250R_192 (by norm_num)

theorem t22250R_190 : rows2 200 340 ≤ 905943553182065816 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_200 t22250R_191 (by norm_num)

theorem t22250R_189 : rows2 199 340 ≤ 911560191932079158 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_199 t22250R_190 (by norm_num)

theorem t22250R_188 : rows2 198 340 ≤ 917067070731694101 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_198 t22250R_189 (by norm_num)

theorem t22250R_187 : rows2 197 340 ≤ 922466184281483101 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_197 t22250R_188 (by norm_num)

theorem t22250R_186 : rows2 196 340 ≤ 927758291704719697 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_196 t22250R_187 (by norm_num)

theorem t22250R_185 : rows2 195 340 ≤ 932944158787294365 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_195 t22250R_186 (by norm_num)

theorem t22250R_184 : rows2 194 340 ≤ 938024557870393476 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_194 t22250R_185 (by norm_num)

theorem t22250R_183 : rows2 193 340 ≤ 943000358324900324 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_193 t22250R_184 (by norm_num)

theorem t22250R_182 : rows2 192 340 ≤ 947872285279966320 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_192 t22250R_183 (by norm_num)

theorem t22250R_181 : rows2 191 340 ≤ 952641069598536921 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_191 t22250R_182 (by norm_num)

theorem t22250R_180 : rows2 190 340 ≤ 957305303750267152 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_190 t22250R_181 (by norm_num)

theorem t22250R_179 : rows2 189 340 ≤ 961860755248325554 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_189 t22250R_180 (by norm_num)

theorem t22250R_178 : rows2 188 340 ≤ 966305798004067528 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_188 t22250R_179 (by norm_num)

theorem t22250R_177 : rows2 187 340 ≤ 970636252562753557 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_187 t22250R_178 (by norm_num)

theorem t22250R_176 : rows2 186 340 ≤ 974850645389281009 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_186 t22250R_177 (by norm_num)

theorem t22250R_175 : rows2 185 340 ≤ 978945147663537227 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_185 t22250R_176 (by norm_num)

theorem t22250R_174 : rows2 184 340 ≤ 982918533286288621 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_184 t22250R_175 (by norm_num)

theorem t22250R_173 : rows2 183 340 ≤ 986767347842251824 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_183 t22250R_174 (by norm_num)

theorem t22250R_172 : rows2 182 340 ≤ 990490366186326439 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_182 t22250R_173 (by norm_num)

theorem t22250R_171 : rows2 181 340 ≤ 994084460588019161 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_181 t22250R_172 (by norm_num)

theorem t22250R_170 : rows2 180 340 ≤ 997548463092781686 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_180 t22250R_171 (by norm_num)

theorem t22250R_169 : rows2 179 340 ≤ 1000879456148311965 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_179 t22250R_170 (by norm_num)

theorem t22250R_168 : rows2 178 340 ≤ 1004076309740414580 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_178 t22250R_169 (by norm_num)

theorem t22250R_167 : rows2 177 340 ≤ 1007248506494840642 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_177 t22250R_168 (by norm_num)

theorem t22250R_166 : rows2 176 340 ≤ 1010397856059108561 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_176 t22250R_167 (by norm_num)

theorem t22250R_165 : rows2 175 340 ≤ 1013524268233572420 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_175 t22250R_166 (by norm_num)

theorem t22250R_164 : rows2 174 340 ≤ 1016628939576757186 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_174 t22250R_165 (by norm_num)

theorem t22250R_163 : rows2 173 340 ≤ 1019705402060665631 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_173 t22250R_164 (by norm_num)

theorem t22250R_162 : rows2 172 340 ≤ 1022755036411536013 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_172 t22250R_163 (by norm_num)

theorem t22250R_161 : rows2 171 340 ≤ 1025786419722451886 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_171 t22250R_162 (by norm_num)

theorem t22250R_160 : rows2 170 340 ≤ 1028794154160734598 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_170 t22250R_161 (by norm_num)

theorem t22250R_159 : rows2 169 340 ≤ 1031779430149621851 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_169 t22250R_160 (by norm_num)

theorem t22250R_158 : rows2 168 340 ≤ 1034751764307348556 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_168 t22250R_159 (by norm_num)

theorem t22250R_157 : rows2 167 340 ≤ 1037705052861643063 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_167 t22250R_158 (by norm_num)

theorem t22250R_156 : rows2 166 340 ≤ 1040641235322428917 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_166 t22250R_157 (by norm_num)

theorem t22250R_155 : rows2 165 340 ≤ 1043569309664619909 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_165 t22250R_156 (by norm_num)

theorem t22250R_154 : rows2 164 340 ≤ 1046483744789249148 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_164 t22250R_155 (by norm_num)

theorem t22250R_153 : rows2 163 340 ≤ 1049386058728612484 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_163 t22250R_154 (by norm_num)

theorem t22250R_152 : rows2 162 340 ≤ 1052285740658449246 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_162 t22250R_153 (by norm_num)

theorem t22250R_151 : rows2 161 340 ≤ 1055176927631814819 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_161 t22250R_152 (by norm_num)

theorem t22250R_150 : rows2 160 340 ≤ 1058061470976798313 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_160 t22250R_151 (by norm_num)

theorem t22250R_149 : rows2 159 340 ≤ 1060948699113941284 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_159 t22250R_150 (by norm_num)

theorem t22250R_148 : rows2 158 340 ≤ 1063832266230857912 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_158 t22250R_149 (by norm_num)

theorem t22250R_147 : rows2 157 340 ≤ 1066712597977719568 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_157 t22250R_148 (by norm_num)

theorem t22250R_146 : rows2 156 340 ≤ 1069597832133594471 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_156 t22250R_147 (by norm_num)

theorem t22250R_145 : rows2 155 340 ≤ 1072421299735101031 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_155 t22250R_146 (by norm_num)

theorem t22250R_144 : rows2 154 340 ≤ 1075123401656377701 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_154 t22250R_145 (by norm_num)

theorem t22250R_143 : rows2 153 340 ≤ 1077710586933612303 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_153 t22250R_144 (by norm_num)

theorem t22250R_142 : rows2 152 340 ≤ 1080173860471857066 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_152 t22250R_143 (by norm_num)

theorem t22250R_141 : rows2 151 340 ≤ 1082511982056788818 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_151 t22250R_142 (by norm_num)

theorem t22250R_140 : rows2 150 340 ≤ 1084731216419983504 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_150 t22250R_141 (by norm_num)

theorem t22250R_139 : rows2 149 340 ≤ 1086822735601978420 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_149 t22250R_140 (by norm_num)

theorem t22250R_138 : rows2 148 340 ≤ 1088784990230369175 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_148 t22250R_139 (by norm_num)

theorem t22250R_137 : rows2 147 340 ≤ 1090624642388496026 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_147 t22250R_138 (by norm_num)

theorem t22250R_136 : rows2 146 340 ≤ 1092332486148709622 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_146 t22250R_137 (by norm_num)

theorem t22250R_135 : rows2 145 340 ≤ 1094000329445202214 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_145 t22250R_136 (by norm_num)

theorem t22250R_134 : rows2 144 340 ≤ 1095523873140757602 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_144 t22250R_135 (by norm_num)

theorem t22250R_133 : rows2 143 340 ≤ 1096999395208059033 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_143 t22250R_134 (by norm_num)

theorem t22250R_132 : rows2 142 340 ≤ 1098325056810937708 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_142 t22250R_133 (by norm_num)

theorem t22250R_131 : rows2 141 340 ≤ 1099593331519405465 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_141 t22250R_132 (by norm_num)

theorem t22250R_130 : rows2 140 340 ≤ 1100705655388327742 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_140 t22250R_131 (by norm_num)

theorem t22250R_129 : rows2 139 340 ≤ 1101751678479930477 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_139 t22250R_130 (by norm_num)

theorem t22250R_128 : rows2 138 340 ≤ 1102635085477430439 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_138 t22250R_129 (by norm_num)

theorem t22250R_127 : rows2 137 340 ≤ 1103442290389563801 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_137 t22250R_128 (by norm_num)

theorem t22250R_126 : rows2 136 340 ≤ 1104079637052386015 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_136 t22250R_127 (by norm_num)

theorem t22250R_125 : rows2 135 340 ≤ 1104799823532576449 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_135 t22250R_126 (by norm_num)

theorem t22250R_124 : rows2 134 340 ≤ 1105517055593593588 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_134 t22250R_125 (by norm_num)

theorem t22250R_123 : rows2 133 340 ≤ 1106318409736545160 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_133 t22250R_124 (by norm_num)

theorem t22250R_122 : rows2 132 340 ≤ 1107120010825409080 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_132 t22250R_123 (by norm_num)

theorem t22250R_121 : rows2 131 340 ≤ 1108006896358005062 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_131 t22250R_122 (by norm_num)

theorem t22250R_120 : rows2 130 340 ≤ 1108895596531653004 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_130 t22250R_121 (by norm_num)

theorem t22250R_119 : rows2 129 340 ≤ 1109871461045598413 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_129 t22250R_120 (by norm_num)

theorem t22250R_118 : rows2 128 340 ≤ 1110851662631907298 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_128 t22250R_119 (by norm_num)

theorem t22250R_117 : rows2 127 340 ≤ 1111922224085596726 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_127 t22250R_118 (by norm_num)

theorem t22250R_116 : rows2 126 340 ≤ 1112999320580900440 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_126 t22250R_117 (by norm_num)

theorem t22250R_115 : rows2 125 340 ≤ 1114169038224269703 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_125 t22250R_116 (by norm_num)

theorem t22250R_114 : rows2 124 340 ≤ 1115346354923294257 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_124 t22250R_115 (by norm_num)

theorem t22250R_113 : rows2 123 340 ≤ 1116618800318893867 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_123 t22250R_114 (by norm_num)

theorem t22250R_112 : rows2 122 340 ≤ 1117900198806780965 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_122 t22250R_113 (by norm_num)

theorem t22250R_111 : rows2 121 340 ≤ 1119279730210264069 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_121 t22250R_112 (by norm_num)

theorem t22250R_110 : rows2 120 340 ≤ 1120669905482567160 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_120 t22250R_111 (by norm_num)

theorem t22250R_109 : rows2 119 340 ≤ 1122161688302580586 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_119 t22250R_110 (by norm_num)

theorem t22250R_108 : rows2 118 340 ≤ 1123666312385741797 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_118 t22250R_109 (by norm_num)

theorem t22250R_107 : rows2 117 340 ≤ 1125276561511136002 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_117 t22250R_108 (by norm_num)

theorem t22250R_106 : rows2 116 340 ≤ 1126902875124449449 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_116 t22250R_107 (by norm_num)

theorem t22250R_105 : rows2 115 340 ≤ 1128639543569389518 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_115 t22250R_106 (by norm_num)

theorem t22250R_104 : rows2 114 340 ≤ 1130395311464590057 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_114 t22250R_105 (by norm_num)

theorem t22250R_103 : rows2 113 340 ≤ 1132205371177264032 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_113 t22250R_104 (by norm_num)

theorem t22250R_102 : rows2 112 340 ≤ 1133848616902903640 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_112 t22250R_103 (by norm_num)

theorem t22250R_101 : rows2 111 340 ≤ 1135416712623452209 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_111 t22250R_102 (by norm_num)

theorem t22250R_100 : rows2 110 340 ≤ 1136807749661818059 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_110 t22250R_101 (by norm_num)

theorem t22250R_99 : rows2 109 340 ≤ 1138114929610246189 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_109 t22250R_100 (by norm_num)

theorem t22250R_98 : rows2 108 340 ≤ 1139234280346996966 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_108 t22250R_99 (by norm_num)

theorem t22250R_97 : rows2 107 340 ≤ 1140260519385818892 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_107 t22250R_98 (by norm_num)

theorem t22250R_96 : rows2 106 340 ≤ 1141087513098309138 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_106 t22250R_97 (by norm_num)

theorem t22250R_95 : rows2 105 340 ≤ 1141811646400381916 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_105 t22250R_96 (by norm_num)

theorem t22250R_94 : rows2 104 340 ≤ 1142325944337051389 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_104 t22250R_95 (by norm_num)

theorem t22250R_93 : rows2 103 340 ≤ 1142728554530528089 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_103 t22250R_94 (by norm_num)

theorem t22250R_92 : rows2 102 340 ≤ 1142982388240416876 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_102 t22250R_93 (by norm_num)

theorem t22250R_91 : rows2 101 340 ≤ 1143227576132498942 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_101 t22250R_92 (by norm_num)

theorem t22250R_90 : rows2 100 340 ≤ 1143465125044823020 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_100 t22250R_91 (by norm_num)

theorem t22250R_89 : rows2 99 340 ≤ 1143699636867052062 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_99 t22250R_90 (by norm_num)

theorem t22250R_88 : rows2 98 340 ≤ 1143931329229350115 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_98 t22250R_89 (by norm_num)

theorem t22250R_87 : rows2 97 340 ≤ 1144163577765665589 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_97 t22250R_88 (by norm_num)

theorem t22250R_86 : rows2 96 340 ≤ 1144395058926598172 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_96 t22250R_87 (by norm_num)

theorem t22250R_85 : rows2 95 340 ≤ 1144627246890068823 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_95 t22250R_86 (by norm_num)

theorem t22250R_84 : rows2 94 340 ≤ 1144857007299369225 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_94 t22250R_85 (by norm_num)

theorem t22250R_83 : rows2 93 340 ≤ 1145084473487646698 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_93 t22250R_84 (by norm_num)

theorem t22250R_82 : rows2 92 340 ≤ 1145306348062387618 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_92 t22250R_83 (by norm_num)

theorem t22250R_81 : rows2 91 340 ≤ 1145520781671650410 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_91 t22250R_82 (by norm_num)

theorem t22250R_80 : rows2 90 340 ≤ 1145722813503919145 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_90 t22250R_81 (by norm_num)

theorem t22250R_79 : rows2 89 340 ≤ 1145908848606902920 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_89 t22250R_80 (by norm_num)

theorem t22250R_78 : rows2 88 340 ≤ 1146069400377545685 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_88 t22250R_79 (by norm_num)

theorem t22250R_77 : rows2 87 340 ≤ 1146201096435465704 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_87 t22250R_78 (by norm_num)

theorem t22250R_76 : rows2 86 340 ≤ 1146304065775871700 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_86 t22250R_77 (by norm_num)

theorem t22250R_75 : rows2 85 340 ≤ 1146383688382127813 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_85 t22250R_76 (by norm_num)

theorem t22250R_74 : rows2 84 340 ≤ 1146443984864193873 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_84 t22250R_75 (by norm_num)

theorem t22250R_73 : rows2 83 340 ≤ 1146490008524211043 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_83 t22250R_74 (by norm_num)

theorem t22250R_72 : rows2 82 340 ≤ 1146524779913256248 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_82 t22250R_73 (by norm_num)

theorem t22250R_71 : rows2 81 340 ≤ 1146552249515111983 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_81 t22250R_72 (by norm_num)

theorem t22250R_70 : rows2 80 340 ≤ 1146575079800675732 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_80 t22250R_71 (by norm_num)

theorem t22250R_69 : rows2 79 340 ≤ 1146596438897046031 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_79 t22250R_70 (by norm_num)

theorem t22250R_68 : rows2 78 340 ≤ 1146619128967421863 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_78 t22250R_69 (by norm_num)

theorem t22250R_67 : rows2 77 340 ≤ 1146645115704844649 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_77 t22250R_68 (by norm_num)

theorem t22250R_66 : rows2 76 340 ≤ 1146677243809650299 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_76 t22250R_67 (by norm_num)

theorem t22250R_65 : rows2 75 340 ≤ 1146716148450524167 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_75 t22250R_66 (by norm_num)

theorem t22250R_64 : rows2 74 340 ≤ 1146762239907724758 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_74 t22250R_65 (by norm_num)

theorem t22250R_63 : rows2 73 340 ≤ 1146817250630921249 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_73 t22250R_64 (by norm_num)

theorem t22250R_62 : rows2 72 340 ≤ 1146882783618857446 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_72 t22250R_63 (by norm_num)

theorem t22250R_61 : rows2 71 340 ≤ 1146960241998623684 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_71 t22250R_62 (by norm_num)

theorem t22250R_60 : rows2 70 340 ≤ 1147049981079140943 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_70 t22250R_61 (by norm_num)

theorem t22250R_59 : rows2 69 340 ≤ 1147151228793431899 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_69 t22250R_60 (by norm_num)

theorem t22250R_58 : rows2 68 340 ≤ 1147262583246337986 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_68 t22250R_59 (by norm_num)

theorem t22250R_57 : rows2 67 340 ≤ 1147382840592147475 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_67 t22250R_58 (by norm_num)

theorem t22250R_56 : rows2 66 340 ≤ 1147510126346881268 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_66 t22250R_57 (by norm_num)

theorem t22250R_55 : rows2 65 340 ≤ 1147643370974976979 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_65 t22250R_56 (by norm_num)

theorem t22250R_54 : rows2 64 340 ≤ 1147780551593939557 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_64 t22250R_55 (by norm_num)

theorem t22250R_53 : rows2 63 340 ≤ 1147919727661124015 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_63 t22250R_54 (by norm_num)

theorem t22250R_52 : rows2 62 340 ≤ 1148057829391112016 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_62 t22250R_53 (by norm_num)

theorem t22250R_51 : rows2 61 340 ≤ 1148191803980580181 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_61 t22250R_52 (by norm_num)

theorem t22250R_50 : rows2 60 340 ≤ 1148317624825540291 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_60 t22250R_51 (by norm_num)

theorem t22250R_49 : rows2 59 340 ≤ 1148431780387548453 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_59 t22250R_50 (by norm_num)

theorem t22250R_48 : rows2 58 340 ≤ 1148532894491974516 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_58 t22250R_49 (by norm_num)

theorem t22250R_47 : rows2 57 340 ≤ 1148620878781298013 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_57 t22250R_48 (by norm_num)

theorem t22250R_46 : rows2 56 340 ≤ 1148696005714176041 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_56 t22250R_47 (by norm_num)

theorem t22250R_45 : rows2 55 340 ≤ 1148758823169644537 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_55 t22250R_46 (by norm_num)

theorem t22250R_44 : rows2 54 340 ≤ 1148810328331933513 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_54 t22250R_45 (by norm_num)

theorem t22250R_43 : rows2 53 340 ≤ 1148852083632262082 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_53 t22250R_44 (by norm_num)

theorem t22250R_42 : rows2 52 340 ≤ 1148885645479277113 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_52 t22250R_43 (by norm_num)

theorem t22250R_41 : rows2 51 340 ≤ 1148912380912602468 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_51 t22250R_42 (by norm_num)

theorem t22250R_40 : rows2 50 340 ≤ 1148933647044542769 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_50 t22250R_41 (by norm_num)

theorem t22250R_39 : rows2 49 340 ≤ 1148950862051668317 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_49 t22250R_40 (by norm_num)

theorem t22250R_38 : rows2 48 340 ≤ 1148965226808890914 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_48 t22250R_39 (by norm_num)

theorem t22250R_37 : rows2 47 340 ≤ 1148977703920205095 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_47 t22250R_38 (by norm_num)

theorem t22250R_36 : rows2 46 340 ≤ 1148989239449890332 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_46 t22250R_37 (by norm_num)

theorem t22250R_35 : rows2 45 340 ≤ 1149000778519595606 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_45 t22250R_36 (by norm_num)

theorem t22250R_34 : rows2 44 340 ≤ 1149012984034448295 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_44 t22250R_35 (by norm_num)

theorem t22250R_33 : rows2 43 340 ≤ 1149026137406949621 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_43 t22250R_34 (by norm_num)

theorem t22250R_32 : rows2 42 340 ≤ 1149040549300819987 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_42 t22250R_33 (by norm_num)

theorem t22250R_31 : rows2 41 340 ≤ 1149056207483225509 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_41 t22250R_32 (by norm_num)

theorem t22250R_30 : rows2 40 340 ≤ 1149073070572267235 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_40 t22250R_31 (by norm_num)

theorem t22250R_29 : rows2 39 340 ≤ 1149091056107458962 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_39 t22250R_30 (by norm_num)

theorem t22250R_28 : rows2 38 340 ≤ 1149110180147591133 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_38 t22250R_29 (by norm_num)

theorem t22250R_27 : rows2 37 340 ≤ 1149130217126276627 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_37 t22250R_28 (by norm_num)

theorem t22250R_26 : rows2 36 340 ≤ 1149150630061356492 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_36 t22250R_27 (by norm_num)

theorem t22250R_25 : rows2 35 340 ≤ 1149171242906352255 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_35 t22250R_26 (by norm_num)

theorem t22250R_24 : rows2 34 340 ≤ 1149191911762826287 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_34 t22250R_25 (by norm_num)

theorem t22250R_23 : rows2 33 340 ≤ 1149212547090132661 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_33 t22250R_24 (by norm_num)

theorem t22250R_22 : rows2 32 340 ≤ 1149233129456631396 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_32 t22250R_23 (by norm_num)

theorem t22250R_21 : rows2 31 340 ≤ 1149253673670090761 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_31 t22250R_22 (by norm_num)

theorem t22250R_20 : rows2 30 340 ≤ 1149274091794663001 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_30 t22250R_21 (by norm_num)

theorem t22250R_19 : rows2 29 340 ≤ 1149294207216512960 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_29 t22250R_20 (by norm_num)

theorem t22250R_18 : rows2 28 340 ≤ 1149313766684154137 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_28 t22250R_19 (by norm_num)

theorem t22250R_17 : rows2 27 340 ≤ 1149332474804355916 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_27 t22250R_18 (by norm_num)

theorem t22250R_16 : rows2 26 340 ≤ 1149350047758316118 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_26 t22250R_17 (by norm_num)

theorem t22250R_15 : rows2 25 340 ≤ 1149366205282681692 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_25 t22250R_16 (by norm_num)

theorem t22250R_14 : rows2 24 340 ≤ 1149380730807702364 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_24 t22250R_15 (by norm_num)

theorem t22250R_13 : rows2 23 340 ≤ 1149393473300451753 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_23 t22250R_14 (by norm_num)

theorem t22250R_12 : rows2 22 340 ≤ 1149404330731146609 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_22 t22250R_13 (by norm_num)

theorem t22250R_11 : rows2 21 340 ≤ 1149413330235182777 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_21 t22250R_12 (by norm_num)

theorem t22250R_10 : rows2 20 340 ≤ 1149420656506877777 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_20 t22250R_11 (by norm_num)

theorem t22250R_9 : rows2 19 340 ≤ 1149426619291962184 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_19 t22250R_10 (by norm_num)

theorem t22250R_8 : rows2 18 340 ≤ 1149431659242786028 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_18 t22250R_9 (by norm_num)

theorem t22250R_7 : rows2 17 340 ≤ 1149436164916848382 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_17 t22250R_8 (by norm_num)

theorem t22250R_6 : rows2 16 340 ≤ 1149440482700384148 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_16 t22250R_7 (by norm_num)

theorem t22250R_5 : rows2 15 340 ≤ 1149444836380066512 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_15 t22250R_6 (by norm_num)

theorem t22250R_4 : rows2 14 340 ≤ 1149449298767371833 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_14 t22250R_5 (by norm_num)

theorem t22250R_3 : rows2 13 340 ≤ 1149453799866809815 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_3 t22250R_4 (by norm_num)

theorem t22250R_2 : rows2 12 340 ≤ 1149458189766853676 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_2 t22250R_3 (by norm_num)

theorem t22250R_1 : rows2 10 340 ≤ 1149465908796568128 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_1 t22250R_2 (by norm_num)

theorem t22250R_0 : rows2 0 340 ≤ 1149475836901239458 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_0 t22250R_1 (by norm_num)

/-- **The refined certificate on `grid22250R`**: the loss's bound is less than `K`, the 4715 parts checked by the
kernel. -/
theorem total2_lt_22250R : total2 < K := by
  rw [total2_eq_rows2_full]
  exact lt_of_le_of_lt t22250R_0 (by decide +kernel)

end

end SieveCert

#print axioms SieveCert.total2_lt_22250R
