/-
# The refined certificate of the sieve route's loss at `L = 278/125` with `n = 340`: `total2 < K`

On `SieveGrid22240R.grid22240R` (`U1 = ⌈(41556/100000)DEN⌉`, `U2 = ⌊(47531/100000)DEN⌋`, `n = 340`),
`SieveCert.total2` is less than `K` (it is below `0.99754K`, rounded up; the certificate of `SieveCertDefs.lean` on
the same grid totals `1.12341K`): `total2` is `rows2 0 n` (`SieveCert2.total2_eq_rows2_full`), and its bound is
assembled one step at a time from the 5066 parts' bounds (`rows22240R_0` … `rows22240R_5065`, each by `decide
+kernel` in one of the 387 part files): a heavy row's bound from its column pieces' (`rowsJ2_le_of_split`,
`rows2_le_of_rowsJ2`), then the 238 ranges of rows from the last to the first (`rows2_le_of_split`), every bound a
literal and every step a theorem of its own (`c22240R_…`, `hr22240R_…`, `t22240R_…`); the bounds, `⌈1.001 × part⌉`
computed exactly in integers, sum to `1151230848467235036`, less than `K` by `decide +kernel` (`total2_lt_22240R`).

The file imports `SieveCert2.lean` and `SieveCert22240RP1.lean` … `SieveCert22240RP387.lean`.
-/
import SieveCert2
import SieveCert22240RP1
import SieveCert22240RP2
import SieveCert22240RP3
import SieveCert22240RP4
import SieveCert22240RP5
import SieveCert22240RP6
import SieveCert22240RP7
import SieveCert22240RP8
import SieveCert22240RP9
import SieveCert22240RP10
import SieveCert22240RP11
import SieveCert22240RP12
import SieveCert22240RP13
import SieveCert22240RP14
import SieveCert22240RP15
import SieveCert22240RP16
import SieveCert22240RP17
import SieveCert22240RP18
import SieveCert22240RP19
import SieveCert22240RP20
import SieveCert22240RP21
import SieveCert22240RP22
import SieveCert22240RP23
import SieveCert22240RP24
import SieveCert22240RP25
import SieveCert22240RP26
import SieveCert22240RP27
import SieveCert22240RP28
import SieveCert22240RP29
import SieveCert22240RP30
import SieveCert22240RP31
import SieveCert22240RP32
import SieveCert22240RP33
import SieveCert22240RP34
import SieveCert22240RP35
import SieveCert22240RP36
import SieveCert22240RP37
import SieveCert22240RP38
import SieveCert22240RP39
import SieveCert22240RP40
import SieveCert22240RP41
import SieveCert22240RP42
import SieveCert22240RP43
import SieveCert22240RP44
import SieveCert22240RP45
import SieveCert22240RP46
import SieveCert22240RP47
import SieveCert22240RP48
import SieveCert22240RP49
import SieveCert22240RP50
import SieveCert22240RP51
import SieveCert22240RP52
import SieveCert22240RP53
import SieveCert22240RP54
import SieveCert22240RP55
import SieveCert22240RP56
import SieveCert22240RP57
import SieveCert22240RP58
import SieveCert22240RP59
import SieveCert22240RP60
import SieveCert22240RP61
import SieveCert22240RP62
import SieveCert22240RP63
import SieveCert22240RP64
import SieveCert22240RP65
import SieveCert22240RP66
import SieveCert22240RP67
import SieveCert22240RP68
import SieveCert22240RP69
import SieveCert22240RP70
import SieveCert22240RP71
import SieveCert22240RP72
import SieveCert22240RP73
import SieveCert22240RP74
import SieveCert22240RP75
import SieveCert22240RP76
import SieveCert22240RP77
import SieveCert22240RP78
import SieveCert22240RP79
import SieveCert22240RP80
import SieveCert22240RP81
import SieveCert22240RP82
import SieveCert22240RP83
import SieveCert22240RP84
import SieveCert22240RP85
import SieveCert22240RP86
import SieveCert22240RP87
import SieveCert22240RP88
import SieveCert22240RP89
import SieveCert22240RP90
import SieveCert22240RP91
import SieveCert22240RP92
import SieveCert22240RP93
import SieveCert22240RP94
import SieveCert22240RP95
import SieveCert22240RP96
import SieveCert22240RP97
import SieveCert22240RP98
import SieveCert22240RP99
import SieveCert22240RP100
import SieveCert22240RP101
import SieveCert22240RP102
import SieveCert22240RP103
import SieveCert22240RP104
import SieveCert22240RP105
import SieveCert22240RP106
import SieveCert22240RP107
import SieveCert22240RP108
import SieveCert22240RP109
import SieveCert22240RP110
import SieveCert22240RP111
import SieveCert22240RP112
import SieveCert22240RP113
import SieveCert22240RP114
import SieveCert22240RP115
import SieveCert22240RP116
import SieveCert22240RP117
import SieveCert22240RP118
import SieveCert22240RP119
import SieveCert22240RP120
import SieveCert22240RP121
import SieveCert22240RP122
import SieveCert22240RP123
import SieveCert22240RP124
import SieveCert22240RP125
import SieveCert22240RP126
import SieveCert22240RP127
import SieveCert22240RP128
import SieveCert22240RP129
import SieveCert22240RP130
import SieveCert22240RP131
import SieveCert22240RP132
import SieveCert22240RP133
import SieveCert22240RP134
import SieveCert22240RP135
import SieveCert22240RP136
import SieveCert22240RP137
import SieveCert22240RP138
import SieveCert22240RP139
import SieveCert22240RP140
import SieveCert22240RP141
import SieveCert22240RP142
import SieveCert22240RP143
import SieveCert22240RP144
import SieveCert22240RP145
import SieveCert22240RP146
import SieveCert22240RP147
import SieveCert22240RP148
import SieveCert22240RP149
import SieveCert22240RP150
import SieveCert22240RP151
import SieveCert22240RP152
import SieveCert22240RP153
import SieveCert22240RP154
import SieveCert22240RP155
import SieveCert22240RP156
import SieveCert22240RP157
import SieveCert22240RP158
import SieveCert22240RP159
import SieveCert22240RP160
import SieveCert22240RP161
import SieveCert22240RP162
import SieveCert22240RP163
import SieveCert22240RP164
import SieveCert22240RP165
import SieveCert22240RP166
import SieveCert22240RP167
import SieveCert22240RP168
import SieveCert22240RP169
import SieveCert22240RP170
import SieveCert22240RP171
import SieveCert22240RP172
import SieveCert22240RP173
import SieveCert22240RP174
import SieveCert22240RP175
import SieveCert22240RP176
import SieveCert22240RP177
import SieveCert22240RP178
import SieveCert22240RP179
import SieveCert22240RP180
import SieveCert22240RP181
import SieveCert22240RP182
import SieveCert22240RP183
import SieveCert22240RP184
import SieveCert22240RP185
import SieveCert22240RP186
import SieveCert22240RP187
import SieveCert22240RP188
import SieveCert22240RP189
import SieveCert22240RP190
import SieveCert22240RP191
import SieveCert22240RP192
import SieveCert22240RP193
import SieveCert22240RP194
import SieveCert22240RP195
import SieveCert22240RP196
import SieveCert22240RP197
import SieveCert22240RP198
import SieveCert22240RP199
import SieveCert22240RP200
import SieveCert22240RP201
import SieveCert22240RP202
import SieveCert22240RP203
import SieveCert22240RP204
import SieveCert22240RP205
import SieveCert22240RP206
import SieveCert22240RP207
import SieveCert22240RP208
import SieveCert22240RP209
import SieveCert22240RP210
import SieveCert22240RP211
import SieveCert22240RP212
import SieveCert22240RP213
import SieveCert22240RP214
import SieveCert22240RP215
import SieveCert22240RP216
import SieveCert22240RP217
import SieveCert22240RP218
import SieveCert22240RP219
import SieveCert22240RP220
import SieveCert22240RP221
import SieveCert22240RP222
import SieveCert22240RP223
import SieveCert22240RP224
import SieveCert22240RP225
import SieveCert22240RP226
import SieveCert22240RP227
import SieveCert22240RP228
import SieveCert22240RP229
import SieveCert22240RP230
import SieveCert22240RP231
import SieveCert22240RP232
import SieveCert22240RP233
import SieveCert22240RP234
import SieveCert22240RP235
import SieveCert22240RP236
import SieveCert22240RP237
import SieveCert22240RP238
import SieveCert22240RP239
import SieveCert22240RP240
import SieveCert22240RP241
import SieveCert22240RP242
import SieveCert22240RP243
import SieveCert22240RP244
import SieveCert22240RP245
import SieveCert22240RP246
import SieveCert22240RP247
import SieveCert22240RP248
import SieveCert22240RP249
import SieveCert22240RP250
import SieveCert22240RP251
import SieveCert22240RP252
import SieveCert22240RP253
import SieveCert22240RP254
import SieveCert22240RP255
import SieveCert22240RP256
import SieveCert22240RP257
import SieveCert22240RP258
import SieveCert22240RP259
import SieveCert22240RP260
import SieveCert22240RP261
import SieveCert22240RP262
import SieveCert22240RP263
import SieveCert22240RP264
import SieveCert22240RP265
import SieveCert22240RP266
import SieveCert22240RP267
import SieveCert22240RP268
import SieveCert22240RP269
import SieveCert22240RP270
import SieveCert22240RP271
import SieveCert22240RP272
import SieveCert22240RP273
import SieveCert22240RP274
import SieveCert22240RP275
import SieveCert22240RP276
import SieveCert22240RP277
import SieveCert22240RP278
import SieveCert22240RP279
import SieveCert22240RP280
import SieveCert22240RP281
import SieveCert22240RP282
import SieveCert22240RP283
import SieveCert22240RP284
import SieveCert22240RP285
import SieveCert22240RP286
import SieveCert22240RP287
import SieveCert22240RP288
import SieveCert22240RP289
import SieveCert22240RP290
import SieveCert22240RP291
import SieveCert22240RP292
import SieveCert22240RP293
import SieveCert22240RP294
import SieveCert22240RP295
import SieveCert22240RP296
import SieveCert22240RP297
import SieveCert22240RP298
import SieveCert22240RP299
import SieveCert22240RP300
import SieveCert22240RP301
import SieveCert22240RP302
import SieveCert22240RP303
import SieveCert22240RP304
import SieveCert22240RP305
import SieveCert22240RP306
import SieveCert22240RP307
import SieveCert22240RP308
import SieveCert22240RP309
import SieveCert22240RP310
import SieveCert22240RP311
import SieveCert22240RP312
import SieveCert22240RP313
import SieveCert22240RP314
import SieveCert22240RP315
import SieveCert22240RP316
import SieveCert22240RP317
import SieveCert22240RP318
import SieveCert22240RP319
import SieveCert22240RP320
import SieveCert22240RP321
import SieveCert22240RP322
import SieveCert22240RP323
import SieveCert22240RP324
import SieveCert22240RP325
import SieveCert22240RP326
import SieveCert22240RP327
import SieveCert22240RP328
import SieveCert22240RP329
import SieveCert22240RP330
import SieveCert22240RP331
import SieveCert22240RP332
import SieveCert22240RP333
import SieveCert22240RP334
import SieveCert22240RP335
import SieveCert22240RP336
import SieveCert22240RP337
import SieveCert22240RP338
import SieveCert22240RP339
import SieveCert22240RP340
import SieveCert22240RP341
import SieveCert22240RP342
import SieveCert22240RP343
import SieveCert22240RP344
import SieveCert22240RP345
import SieveCert22240RP346
import SieveCert22240RP347
import SieveCert22240RP348
import SieveCert22240RP349
import SieveCert22240RP350
import SieveCert22240RP351
import SieveCert22240RP352
import SieveCert22240RP353
import SieveCert22240RP354
import SieveCert22240RP355
import SieveCert22240RP356
import SieveCert22240RP357
import SieveCert22240RP358
import SieveCert22240RP359
import SieveCert22240RP360
import SieveCert22240RP361
import SieveCert22240RP362
import SieveCert22240RP363
import SieveCert22240RP364
import SieveCert22240RP365
import SieveCert22240RP366
import SieveCert22240RP367
import SieveCert22240RP368
import SieveCert22240RP369
import SieveCert22240RP370
import SieveCert22240RP371
import SieveCert22240RP372
import SieveCert22240RP373
import SieveCert22240RP374
import SieveCert22240RP375
import SieveCert22240RP376
import SieveCert22240RP377
import SieveCert22240RP378
import SieveCert22240RP379
import SieveCert22240RP380
import SieveCert22240RP381
import SieveCert22240RP382
import SieveCert22240RP383
import SieveCert22240RP384
import SieveCert22240RP385
import SieveCert22240RP386
import SieveCert22240RP387

namespace SieveCert

section

attribute [local instance] grid22240R

/-! The chain of bounds: `c22240R_{i}_{m}` for the heavy row `i` from its `m`-th column piece on, `hr22240R_{i}` for
the heavy row `i`, `t22240R_{m}` for the rows from the `m`-th range on; each a theorem of its own, its name distinct
from the other certificates' chains in the same namespace. -/

theorem c22240R_14_0 : rowsJ2 14 15 0 340 ≤ 6242667275026 :=
  rowsJ2_le_of_split 14 15 (by norm_num) (by norm_num) rows22240R_4 rows22240R_5 (by norm_num)

theorem hr22240R_14 : rows2 14 15 ≤ 6242667275026 := rows2_le_of_rowsJ2 14 15 c22240R_14_0

theorem c22240R_15_0 : rowsJ2 15 16 0 340 ≤ 6350322324568 :=
  rowsJ2_le_of_split 15 16 (by norm_num) (by norm_num) rows22240R_6 rows22240R_7 (by norm_num)

theorem hr22240R_15 : rows2 15 16 ≤ 6350322324568 := rows2_le_of_rowsJ2 15 16 c22240R_15_0

theorem c22240R_16_0 : rowsJ2 16 17 0 340 ≤ 6339331748175 :=
  rowsJ2_le_of_split 16 17 (by norm_num) (by norm_num) rows22240R_8 rows22240R_9 (by norm_num)

theorem hr22240R_16 : rows2 16 17 ≤ 6339331748175 := rows2_le_of_rowsJ2 16 17 c22240R_16_0

theorem c22240R_17_1 : rowsJ2 17 18 14 340 ≤ 1758069018384 :=
  rowsJ2_le_of_split 17 18 (by norm_num) (by norm_num) rows22240R_11 rows22240R_12 (by norm_num)

theorem c22240R_17_0 : rowsJ2 17 18 0 340 ≤ 6334102414377 :=
  rowsJ2_le_of_split 17 18 (by norm_num) (by norm_num) rows22240R_10 c22240R_17_1 (by norm_num)

theorem hr22240R_17 : rows2 17 18 ≤ 6334102414377 := rows2_le_of_rowsJ2 17 18 c22240R_17_0

theorem c22240R_18_1 : rowsJ2 18 19 14 340 ≤ 2262971225186 :=
  rowsJ2_le_of_split 18 19 (by norm_num) (by norm_num) rows22240R_14 rows22240R_15 (by norm_num)

theorem c22240R_18_0 : rowsJ2 18 19 0 340 ≤ 6508449887405 :=
  rowsJ2_le_of_split 18 19 (by norm_num) (by norm_num) rows22240R_13 c22240R_18_1 (by norm_num)

theorem hr22240R_18 : rows2 18 19 ≤ 6508449887405 := rows2_le_of_rowsJ2 18 19 c22240R_18_0

theorem c22240R_19_2 : rowsJ2 19 20 17 340 ≤ 2054033881910 :=
  rowsJ2_le_of_split 19 20 (by norm_num) (by norm_num) rows22240R_18 rows22240R_19 (by norm_num)

theorem c22240R_19_1 : rowsJ2 19 20 14 340 ≤ 3080415861962 :=
  rowsJ2_le_of_split 19 20 (by norm_num) (by norm_num) rows22240R_17 c22240R_19_2 (by norm_num)

theorem c22240R_19_0 : rowsJ2 19 20 0 340 ≤ 6999926845303 :=
  rowsJ2_le_of_split 19 20 (by norm_num) (by norm_num) rows22240R_16 c22240R_19_1 (by norm_num)

theorem hr22240R_19 : rows2 19 20 ≤ 6999926845303 := rows2_le_of_rowsJ2 19 20 c22240R_19_0

theorem c22240R_20_3 : rowsJ2 20 21 19 340 ≤ 2113197296332 :=
  rowsJ2_le_of_split 20 21 (by norm_num) (by norm_num) rows22240R_23 rows22240R_24 (by norm_num)

theorem c22240R_20_2 : rowsJ2 20 21 17 340 ≤ 3287235180449 :=
  rowsJ2_le_of_split 20 21 (by norm_num) (by norm_num) rows22240R_22 c22240R_20_3 (by norm_num)

theorem c22240R_20_1 : rowsJ2 20 21 14 340 ≤ 4226465768009 :=
  rowsJ2_le_of_split 20 21 (by norm_num) (by norm_num) rows22240R_21 c22240R_20_2 (by norm_num)

theorem c22240R_20_0 : rowsJ2 20 21 0 340 ≤ 7830518303698 :=
  rowsJ2_le_of_split 20 21 (by norm_num) (by norm_num) rows22240R_20 c22240R_20_1 (by norm_num)

theorem hr22240R_20 : rows2 20 21 ≤ 7830518303698 := rows2_le_of_rowsJ2 20 21 c22240R_20_0

theorem c22240R_21_4 : rowsJ2 21 22 20 340 ≤ 2688598741223 :=
  rowsJ2_le_of_split 21 22 (by norm_num) (by norm_num) rows22240R_29 rows22240R_30 (by norm_num)

theorem c22240R_21_3 : rowsJ2 21 22 19 340 ≤ 3635693805502 :=
  rowsJ2_le_of_split 21 22 (by norm_num) (by norm_num) rows22240R_28 c22240R_21_4 (by norm_num)

theorem c22240R_21_2 : rowsJ2 21 22 17 340 ≤ 4843727041733 :=
  rowsJ2_le_of_split 21 22 (by norm_num) (by norm_num) rows22240R_27 c22240R_21_3 (by norm_num)

theorem c22240R_21_1 : rowsJ2 21 22 14 340 ≤ 5716825010895 :=
  rowsJ2_le_of_split 21 22 (by norm_num) (by norm_num) rows22240R_26 c22240R_21_2 (by norm_num)

theorem c22240R_21_0 : rowsJ2 21 22 0 340 ≤ 9015900844470 :=
  rowsJ2_le_of_split 21 22 (by norm_num) (by norm_num) rows22240R_25 c22240R_21_1 (by norm_num)

theorem hr22240R_21 : rows2 21 22 ≤ 9015900844470 := rows2_le_of_rowsJ2 21 22 c22240R_21_0

theorem c22240R_22_5 : rowsJ2 22 23 21 340 ≤ 3230788335878 :=
  rowsJ2_le_of_split 22 23 (by norm_num) (by norm_num) rows22240R_36 rows22240R_37 (by norm_num)

theorem c22240R_22_4 : rowsJ2 22 23 20 340 ≤ 4469824755578 :=
  rowsJ2_le_of_split 22 23 (by norm_num) (by norm_num) rows22240R_35 c22240R_22_5 (by norm_num)

theorem c22240R_22_3 : rowsJ2 22 23 19 340 ≤ 5439386147822 :=
  rowsJ2_le_of_split 22 23 (by norm_num) (by norm_num) rows22240R_34 c22240R_22_4 (by norm_num)

theorem c22240R_22_2 : rowsJ2 22 23 17 340 ≤ 6688173319477 :=
  rowsJ2_le_of_split 22 23 (by norm_num) (by norm_num) rows22240R_33 c22240R_22_3 (by norm_num)

theorem c22240R_22_1 : rowsJ2 22 23 14 340 ≤ 7512952315719 :=
  rowsJ2_le_of_split 22 23 (by norm_num) (by norm_num) rows22240R_32 c22240R_22_2 (by norm_num)

theorem c22240R_22_0 : rowsJ2 22 23 0 340 ≤ 10523837896444 :=
  rowsJ2_le_of_split 22 23 (by norm_num) (by norm_num) rows22240R_31 c22240R_22_1 (by norm_num)

theorem hr22240R_22 : rows2 22 23 ≤ 10523837896444 := rows2_le_of_rowsJ2 22 23 c22240R_22_0

theorem c22240R_23_6 : rowsJ2 23 24 22 340 ≤ 3625390363210 :=
  rowsJ2_le_of_split 23 24 (by norm_num) (by norm_num) rows22240R_44 rows22240R_45 (by norm_num)

theorem c22240R_23_5 : rowsJ2 23 24 21 340 ≤ 5147321139459 :=
  rowsJ2_le_of_split 23 24 (by norm_num) (by norm_num) rows22240R_43 c22240R_23_6 (by norm_num)

theorem c22240R_23_4 : rowsJ2 23 24 20 340 ≤ 6414823908418 :=
  rowsJ2_le_of_split 23 24 (by norm_num) (by norm_num) rows22240R_42 c22240R_23_5 (by norm_num)

theorem c22240R_23_3 : rowsJ2 23 24 19 340 ≤ 7414910127686 :=
  rowsJ2_le_of_split 23 24 (by norm_num) (by norm_num) rows22240R_41 c22240R_23_4 (by norm_num)

theorem c22240R_23_2 : rowsJ2 23 24 17 340 ≤ 8703563034702 :=
  rowsJ2_le_of_split 23 24 (by norm_num) (by norm_num) rows22240R_40 c22240R_23_3 (by norm_num)

theorem c22240R_23_1 : rowsJ2 23 24 14 340 ≤ 9507277669111 :=
  rowsJ2_le_of_split 23 24 (by norm_num) (by norm_num) rows22240R_39 c22240R_23_2 (by norm_num)

theorem c22240R_23_0 : rowsJ2 23 24 0 340 ≤ 12239781952228 :=
  rowsJ2_le_of_split 23 24 (by norm_num) (by norm_num) rows22240R_38 c22240R_23_1 (by norm_num)

theorem hr22240R_23 : rows2 23 24 ≤ 12239781952228 := rows2_le_of_rowsJ2 23 24 c22240R_23_0

theorem c22240R_24_7 : rowsJ2 24 25 23 340 ≤ 3865081779305 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22240R_53 rows22240R_54 (by norm_num)

theorem c22240R_24_6 : rowsJ2 24 25 22 340 ≤ 5590221330318 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22240R_52 c22240R_24_7 (by norm_num)

theorem c22240R_24_5 : rowsJ2 24 25 21 340 ≤ 7122646449470 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22240R_51 c22240R_24_6 (by norm_num)

theorem c22240R_24_4 : rowsJ2 24 25 20 340 ≤ 8423123904332 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22240R_50 c22240R_24_5 (by norm_num)

theorem c22240R_24_3 : rowsJ2 24 25 19 340 ≤ 9458330888660 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22240R_49 c22240R_24_4 (by norm_num)

theorem c22240R_24_2 : rowsJ2 24 25 17 340 ≤ 10797360560194 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22240R_48 c22240R_24_3 (by norm_num)

theorem c22240R_24_1 : rowsJ2 24 25 14 340 ≤ 11590431655313 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22240R_47 c22240R_24_2 (by norm_num)

theorem c22240R_24_0 : rowsJ2 24 25 0 340 ≤ 14064027426455 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22240R_46 c22240R_24_1 (by norm_num)

theorem hr22240R_24 : rows2 24 25 ≤ 14064027426455 := rows2_le_of_rowsJ2 24 25 c22240R_24_0

theorem c22240R_25_8 : rowsJ2 25 26 24 340 ≤ 3908024446250 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22240R_63 rows22240R_64 (by norm_num)

theorem c22240R_25_7 : rowsJ2 25 26 23 340 ≤ 5760263423793 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22240R_62 c22240R_25_8 (by norm_num)

theorem c22240R_25_6 : rowsJ2 25 26 22 340 ≤ 7475445428921 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22240R_61 c22240R_25_7 (by norm_num)

theorem c22240R_25_5 : rowsJ2 25 26 21 340 ≤ 9015592515967 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22240R_60 c22240R_25_6 (by norm_num)

theorem c22240R_25_4 : rowsJ2 25 26 20 340 ≤ 10342285218795 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22240R_59 c22240R_25_5 (by norm_num)

theorem c22240R_25_3 : rowsJ2 25 26 19 340 ≤ 11420666346020 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22240R_58 c22240R_25_4 (by norm_num)

theorem c22240R_25_2 : rowsJ2 25 26 17 340 ≤ 12814625304491 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22240R_57 c22240R_25_3 (by norm_num)

theorem c22240R_25_1 : rowsJ2 25 26 14 340 ≤ 13620947241009 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22240R_56 c22240R_25_2 (by norm_num)

theorem c22240R_25_0 : rowsJ2 25 26 0 340 ≤ 15845364903049 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22240R_55 c22240R_25_1 (by norm_num)

theorem hr22240R_25 : rows2 25 26 ≤ 15845364903049 := rows2_le_of_rowsJ2 25 26 c22240R_25_0

theorem c22240R_26_9 : rowsJ2 26 27 25 340 ≤ 3800524993855 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22240R_74 rows22240R_75 (by norm_num)

theorem c22240R_26_8 : rowsJ2 26 27 24 340 ≤ 5680883713979 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22240R_73 c22240R_26_9 (by norm_num)

theorem c22240R_26_7 : rowsJ2 26 27 23 340 ≤ 7496162325985 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22240R_72 c22240R_26_8 (by norm_num)

theorem c22240R_26_6 : rowsJ2 26 27 22 340 ≤ 9198199995219 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22240R_71 c22240R_26_7 (by norm_num)

theorem c22240R_26_5 : rowsJ2 26 27 21 340 ≤ 10740388388490 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22240R_70 c22240R_26_6 (by norm_num)

theorem c22240R_26_4 : rowsJ2 26 27 20 340 ≤ 12090265961074 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22240R_69 c22240R_26_5 (by norm_num)

theorem c22240R_26_3 : rowsJ2 26 27 19 340 ≤ 13204873974577 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22240R_68 c22240R_26_4 (by norm_num)

theorem c22240R_26_2 : rowsJ2 26 27 17 340 ≤ 14672337051466 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22240R_67 c22240R_26_3 (by norm_num)

theorem c22240R_26_1 : rowsJ2 26 27 14 340 ≤ 15505721764159 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22240R_66 c22240R_26_2 (by norm_num)

theorem c22240R_26_0 : rowsJ2 26 27 0 340 ≤ 17499690118309 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22240R_65 c22240R_26_1 (by norm_num)

theorem hr22240R_26 : rows2 26 27 ≤ 17499690118309 := rows2_le_of_rowsJ2 26 27 c22240R_26_0

theorem c22240R_27_10 : rowsJ2 27 28 26 340 ≤ 3618701044936 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22240R_86 rows22240R_87 (by norm_num)

theorem c22240R_27_9 : rowsJ2 27 28 25 340 ≤ 5447772198676 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22240R_85 c22240R_27_10 (by norm_num)

theorem c22240R_27_8 : rowsJ2 27 28 24 340 ≤ 7260784153408 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22240R_84 c22240R_27_9 (by norm_num)

theorem c22240R_27_7 : rowsJ2 27 28 23 340 ≤ 9035510025455 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22240R_83 c22240R_27_8 (by norm_num)

theorem c22240R_27_6 : rowsJ2 27 28 22 340 ≤ 10715891756145 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22240R_82 c22240R_27_7 (by norm_num)

theorem c22240R_27_5 : rowsJ2 27 28 21 340 ≤ 12256726039166 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22240R_81 c22240R_27_6 (by norm_num)

theorem c22240R_27_4 : rowsJ2 27 28 20 340 ≤ 13617540665073 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22240R_80 c22240R_27_5 (by norm_num)

theorem c22240R_27_3 : rowsJ2 27 28 19 340 ≤ 14765168399878 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22240R_79 c22240R_27_4 (by norm_num)

theorem c22240R_27_2 : rowsJ2 27 28 17 340 ≤ 16318687734306 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22240R_78 c22240R_27_3 (by norm_num)

theorem c22240R_27_1 : rowsJ2 27 28 14 340 ≤ 17191766437007 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22240R_77 c22240R_27_2 (by norm_num)

theorem c22240R_27_0 : rowsJ2 27 28 0 340 ≤ 18967565557273 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22240R_76 c22240R_27_1 (by norm_num)

theorem hr22240R_27 : rows2 27 28 ≤ 18967565557273 := rows2_le_of_rowsJ2 27 28 c22240R_27_0

theorem c22240R_28_11 : rowsJ2 28 29 27 340 ≤ 3342434414757 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22240R_99 rows22240R_100 (by norm_num)

theorem c22240R_28_10 : rowsJ2 28 29 26 340 ≤ 5090595519722 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22240R_98 c22240R_28_11 (by norm_num)

theorem c22240R_28_9 : rowsJ2 28 29 25 340 ≤ 6846809188786 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22240R_97 c22240R_28_10 (by norm_num)

theorem c22240R_28_8 : rowsJ2 28 29 24 340 ≤ 8597158441970 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22240R_96 c22240R_28_9 (by norm_num)

theorem c22240R_28_7 : rowsJ2 28 29 23 340 ≤ 10319278860088 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22240R_95 c22240R_28_8 (by norm_num)

theorem c22240R_28_6 : rowsJ2 28 29 22 340 ≤ 11974191028837 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22240R_94 c22240R_28_7 (by norm_num)

theorem c22240R_28_5 : rowsJ2 28 29 21 340 ≤ 13504954402056 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22240R_93 c22240R_28_6 (by norm_num)

theorem c22240R_28_4 : rowsJ2 28 29 20 340 ≤ 14873146511504 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22240R_92 c22240R_28_5 (by norm_num)

theorem c22240R_28_3 : rowsJ2 28 29 19 340 ≤ 16047055636219 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22240R_91 c22240R_28_4 (by norm_num)

theorem c22240R_28_2 : rowsJ2 28 29 17 340 ≤ 17687775223709 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22240R_90 c22240R_28_3 (by norm_num)

theorem c22240R_28_1 : rowsJ2 28 29 14 340 ≤ 18618995118466 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22240R_89 c22240R_28_2 (by norm_num)

theorem c22240R_28_0 : rowsJ2 28 29 0 340 ≤ 20199141627400 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22240R_88 c22240R_28_1 (by norm_num)

theorem hr22240R_28 : rows2 28 29 ≤ 20199141627400 := rows2_le_of_rowsJ2 28 29 c22240R_28_0

theorem c22240R_29_12 : rowsJ2 29 30 28 340 ≤ 3019230609331 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22240R_113 rows22240R_114 (by norm_num)

theorem c22240R_29_11 : rowsJ2 29 30 27 340 ≤ 4633358444587 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22240R_112 c22240R_29_12 (by norm_num)

theorem c22240R_29_10 : rowsJ2 29 30 26 340 ≤ 6298760332658 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22240R_111 c22240R_29_11 (by norm_num)

theorem c22240R_29_9 : rowsJ2 29 30 25 340 ≤ 7990240633147 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22240R_110 c22240R_29_10 (by norm_num)

theorem c22240R_29_8 : rowsJ2 29 30 24 340 ≤ 9674078103872 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22240R_109 c22240R_29_9 (by norm_num)

theorem c22240R_29_7 : rowsJ2 29 30 23 340 ≤ 11340034560486 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22240R_108 c22240R_29_8 (by norm_num)

theorem c22240R_29_6 : rowsJ2 29 30 22 340 ≤ 12957206829628 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22240R_107 c22240R_29_7 (by norm_num)

theorem c22240R_29_5 : rowsJ2 29 30 21 340 ≤ 14477730133404 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22240R_106 c22240R_29_6 (by norm_num)

theorem c22240R_29_4 : rowsJ2 29 30 20 340 ≤ 15847558632408 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22240R_105 c22240R_29_5 (by norm_num)

theorem c22240R_29_3 : rowsJ2 29 30 19 340 ≤ 17037618615203 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22240R_104 c22240R_29_4 (by norm_num)

theorem c22240R_29_2 : rowsJ2 29 30 17 340 ≤ 18758934179566 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22240R_103 c22240R_29_3 (by norm_num)

theorem c22240R_29_1 : rowsJ2 29 30 14 340 ≤ 19769232903971 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22240R_102 c22240R_29_2 (by norm_num)

theorem c22240R_29_0 : rowsJ2 29 30 0 340 ≤ 21165561852112 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22240R_101 c22240R_29_1 (by norm_num)

theorem hr22240R_29 : rows2 29 30 ≤ 21165561852112 := rows2_le_of_rowsJ2 29 30 c22240R_29_0

theorem c22240R_30_13 : rowsJ2 30 31 29 340 ≤ 2684011101809 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22240R_128 rows22240R_129 (by norm_num)

theorem c22240R_30_12 : rowsJ2 30 31 28 340 ≤ 4139068261271 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22240R_127 c22240R_30_13 (by norm_num)

theorem c22240R_30_11 : rowsJ2 30 31 27 340 ≤ 5662764883525 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22240R_126 c22240R_30_12 (by norm_num)

theorem c22240R_30_10 : rowsJ2 30 31 26 340 ≤ 7249503027893 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22240R_125 c22240R_30_11 (by norm_num)

theorem c22240R_30_9 : rowsJ2 30 31 25 340 ≤ 8868330356112 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22240R_124 c22240R_30_10 (by norm_num)

theorem c22240R_30_8 : rowsJ2 30 31 24 340 ≤ 10493669543151 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22240R_123 c22240R_30_9 (by norm_num)

theorem c22240R_30_7 : rowsJ2 30 31 23 340 ≤ 12099488012466 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22240R_122 c22240R_30_8 (by norm_num)

theorem c22240R_30_6 : rowsJ2 30 31 22 340 ≤ 13675164147052 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22240R_121 c22240R_30_7 (by norm_num)

theorem c22240R_30_5 : rowsJ2 30 31 21 340 ≤ 15172958182875 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22240R_120 c22240R_30_6 (by norm_num)

theorem c22240R_30_4 : rowsJ2 30 31 20 340 ≤ 16544070602993 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22240R_119 c22240R_30_5 (by norm_num)

theorem c22240R_30_3 : rowsJ2 30 31 19 340 ≤ 17744381369469 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22240R_118 c22240R_30_4 (by norm_num)

theorem c22240R_30_2 : rowsJ2 30 31 17 340 ≤ 19536885260473 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22240R_117 c22240R_30_3 (by norm_num)

theorem c22240R_30_1 : rowsJ2 30 31 14 340 ≤ 20637261418890 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22240R_116 c22240R_30_2 (by norm_num)

theorem c22240R_30_0 : rowsJ2 30 31 0 340 ≤ 21871643638679 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22240R_115 c22240R_30_1 (by norm_num)

theorem hr22240R_30 : rows2 30 31 ≤ 21871643638679 := rows2_le_of_rowsJ2 30 31 c22240R_30_0

theorem c22240R_31_14 : rowsJ2 31 32 30 340 ≤ 2359526978351 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22240R_144 rows22240R_145 (by norm_num)

theorem c22240R_31_13 : rowsJ2 31 32 29 340 ≤ 3648336871383 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22240R_143 c22240R_31_14 (by norm_num)

theorem c22240R_31_12 : rowsJ2 31 32 28 340 ≤ 5012475694654 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22240R_142 c22240R_31_13 (by norm_num)

theorem c22240R_31_11 : rowsJ2 31 32 27 340 ≤ 6449614303794 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22240R_141 c22240R_31_12 (by norm_num)

theorem c22240R_31_10 : rowsJ2 31 32 26 340 ≤ 7949748712240 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22240R_140 c22240R_31_11 (by norm_num)

theorem c22240R_31_9 : rowsJ2 31 32 25 340 ≤ 9499901836612 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22240R_139 c22240R_31_10 (by norm_num)

theorem c22240R_31_8 : rowsJ2 31 32 24 340 ≤ 11062746522652 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22240R_138 c22240R_31_9 (by norm_num)

theorem c22240R_31_7 : rowsJ2 31 32 23 340 ≤ 12616335586221 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22240R_137 c22240R_31_8 (by norm_num)

theorem c22240R_31_6 : rowsJ2 31 32 22 340 ≤ 14138284427105 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22240R_136 c22240R_31_7 (by norm_num)

theorem c22240R_31_5 : rowsJ2 31 32 21 340 ≤ 15609396864425 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22240R_135 c22240R_31_6 (by norm_num)

theorem c22240R_31_4 : rowsJ2 31 32 20 340 ≤ 16972957314123 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22240R_134 c22240R_31_5 (by norm_num)

theorem c22240R_31_3 : rowsJ2 31 32 19 340 ≤ 18183023708129 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22240R_133 c22240R_31_4 (by norm_num)

theorem c22240R_31_2 : rowsJ2 31 32 17 340 ≤ 20029541677324 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22240R_132 c22240R_31_3 (by norm_num)

theorem c22240R_31_1 : rowsJ2 31 32 14 340 ≤ 21235342680846 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22240R_131 c22240R_31_2 (by norm_num)

theorem c22240R_31_0 : rowsJ2 31 32 0 340 ≤ 22326433741919 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22240R_130 c22240R_31_1 (by norm_num)

theorem hr22240R_31 : rows2 31 32 ≤ 22326433741919 := rows2_le_of_rowsJ2 31 32 c22240R_31_0

theorem c22240R_32_15 : rowsJ2 32 33 31 340 ≤ 2105660094753 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22240R_161 rows22240R_162 (by norm_num)

theorem c22240R_32_14 : rowsJ2 32 33 30 340 ≤ 3230323595668 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22240R_160 c22240R_32_15 (by norm_num)

theorem c22240R_32_13 : rowsJ2 32 33 29 340 ≤ 4428201828359 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22240R_159 c22240R_32_14 (by norm_num)

theorem c22240R_32_12 : rowsJ2 32 33 28 340 ≤ 5704448353239 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22240R_158 c22240R_32_13 (by norm_num)

theorem c22240R_32_11 : rowsJ2 32 33 27 340 ≤ 7053021705566 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22240R_157 c22240R_32_12 (by norm_num)

theorem c22240R_32_10 : rowsJ2 32 33 26 340 ≤ 8470360966427 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22240R_156 c22240R_32_11 (by norm_num)

theorem c22240R_32_9 : rowsJ2 32 33 25 340 ≤ 9943783460820 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22240R_155 c22240R_32_10 (by norm_num)

theorem c22240R_32_8 : rowsJ2 32 33 24 340 ≤ 11447998936004 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22240R_154 c22240R_32_9 (by norm_num)

theorem c22240R_32_7 : rowsJ2 32 33 23 340 ≤ 12945250325825 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22240R_153 c22240R_32_8 (by norm_num)

theorem c22240R_32_6 : rowsJ2 32 33 22 340 ≤ 14421280993745 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22240R_152 c22240R_32_7 (by norm_num)

theorem c22240R_32_5 : rowsJ2 32 33 21 340 ≤ 15853280975128 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22240R_151 c22240R_32_6 (by norm_num)

theorem c22240R_32_4 : rowsJ2 32 33 20 340 ≤ 17205142285602 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22240R_150 c22240R_32_5 (by norm_num)

theorem c22240R_32_3 : rowsJ2 32 33 19 340 ≤ 18419134052276 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22240R_149 c22240R_32_4 (by norm_num)

theorem c22240R_32_2 : rowsJ2 32 33 17 340 ≤ 20312174462350 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22240R_148 c22240R_32_3 (by norm_num)

theorem c22240R_32_1 : rowsJ2 32 33 14 340 ≤ 21623941650664 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22240R_147 c22240R_32_2 (by norm_num)

theorem c22240R_32_0 : rowsJ2 32 33 0 340 ≤ 22593678915573 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22240R_146 c22240R_32_1 (by norm_num)

theorem hr22240R_32 : rows2 32 33 ≤ 22593678915573 := rows2_le_of_rowsJ2 32 33 c22240R_32_0

theorem c22240R_33_15 : rowsJ2 33 34 32 340 ≤ 1960866301457 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22240R_178 rows22240R_179 (by norm_num)

theorem c22240R_33_14 : rowsJ2 33 34 31 340 ≤ 2953568011250 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22240R_177 c22240R_33_15 (by norm_num)

theorem c22240R_33_13 : rowsJ2 33 34 30 340 ≤ 3995400888280 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22240R_176 c22240R_33_14 (by norm_num)

theorem c22240R_33_12 : rowsJ2 33 34 29 340 ≤ 5105923516764 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22240R_175 c22240R_33_13 (by norm_num)

theorem c22240R_33_11 : rowsJ2 33 34 28 340 ≤ 6292801464015 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22240R_174 c22240R_33_12 (by norm_num)

theorem c22240R_33_10 : rowsJ2 33 34 27 340 ≤ 7556503561985 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22240R_173 c22240R_33_11 (by norm_num)

theorem c22240R_33_9 : rowsJ2 33 34 26 340 ≤ 8888976497058 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22240R_172 c22240R_33_10 (by norm_num)

theorem c22240R_33_8 : rowsJ2 33 34 25 340 ≤ 10283360064456 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22240R_171 c22240R_33_9 (by norm_num)

theorem c22240R_33_7 : rowsJ2 33 34 24 340 ≤ 11720771902178 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22240R_170 c22240R_33_8 (by norm_num)

theorem c22240R_33_6 : rowsJ2 33 34 23 340 ≤ 13169508180274 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22240R_169 c22240R_33_7 (by norm_num)

theorem c22240R_33_5 : rowsJ2 33 34 22 340 ≤ 14595401029298 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22240R_168 c22240R_33_6 (by norm_num)

theorem c22240R_33_4 : rowsJ2 33 34 21 340 ≤ 15987845251335 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22240R_167 c22240R_33_5 (by norm_num)

theorem c22240R_33_3 : rowsJ2 33 34 19 340 ≤ 18532839481235 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22240R_166 c22240R_33_4 (by norm_num)

theorem c22240R_33_2 : rowsJ2 33 34 17 340 ≤ 20459252242620 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22240R_165 c22240R_33_3 (by norm_num)

theorem c22240R_33_1 : rowsJ2 33 34 14 340 ≤ 21881948563798 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22240R_164 c22240R_33_2 (by norm_num)

theorem c22240R_33_0 : rowsJ2 33 34 0 340 ≤ 22748818723611 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22240R_163 c22240R_33_1 (by norm_num)

theorem hr22240R_33 : rows2 33 34 ≤ 22748818723611 := rows2_le_of_rowsJ2 33 34 c22240R_33_0

theorem c22240R_34_16 : rowsJ2 34 35 33 340 ≤ 1965150018476 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22240R_196 rows22240R_197 (by norm_num)

theorem c22240R_34_15 : rowsJ2 34 35 32 340 ≤ 2877765014032 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22240R_195 c22240R_34_16 (by norm_num)

theorem c22240R_34_14 : rowsJ2 34 35 31 340 ≤ 3800442324731 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22240R_194 c22240R_34_15 (by norm_num)

theorem c22240R_34_13 : rowsJ2 34 35 30 340 ≤ 4764832983922 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22240R_193 c22240R_34_14 (by norm_num)

theorem c22240R_34_12 : rowsJ2 34 35 29 340 ≤ 5789831985885 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22240R_192 c22240R_34_13 (by norm_num)

theorem c22240R_34_11 : rowsJ2 34 35 28 340 ≤ 6890894309628 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22240R_191 c22240R_34_12 (by norm_num)

theorem c22240R_34_10 : rowsJ2 34 35 27 340 ≤ 8068201497358 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22240R_190 c22240R_34_11 (by norm_num)

theorem c22240R_34_9 : rowsJ2 34 35 26 340 ≤ 9319448780713 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22240R_189 c22240R_34_10 (by norm_num)

theorem c22240R_34_8 : rowsJ2 34 35 25 340 ≤ 10632658700620 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22240R_188 c22240R_34_9 (by norm_num)

theorem c22240R_34_7 : rowsJ2 34 35 24 340 ≤ 12000856308325 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22240R_187 c22240R_34_8 (by norm_num)

theorem c22240R_34_6 : rowsJ2 34 35 23 340 ≤ 13392783316255 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22240R_186 c22240R_34_7 (by norm_num)

theorem c22240R_34_5 : rowsJ2 34 35 22 340 ≤ 14776277188434 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22240R_185 c22240R_34_6 (by norm_num)

theorem c22240R_34_4 : rowsJ2 34 35 21 340 ≤ 16124835052604 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22240R_184 c22240R_34_5 (by norm_num)

theorem c22240R_34_3 : rowsJ2 34 35 19 340 ≤ 18635523565139 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22240R_183 c22240R_34_4 (by norm_num)

theorem c22240R_34_2 : rowsJ2 34 35 17 340 ≤ 20594441074316 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22240R_182 c22240R_34_3 (by norm_num)

theorem c22240R_34_1 : rowsJ2 34 35 14 340 ≤ 22114886221535 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22240R_181 c22240R_34_2 (by norm_num)

theorem c22240R_34_0 : rowsJ2 34 35 0 340 ≤ 22908374538858 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22240R_180 c22240R_34_1 (by norm_num)

theorem hr22240R_34 : rows2 34 35 ≤ 22908374538858 := rows2_le_of_rowsJ2 34 35 c22240R_34_0

theorem c22240R_35_16 : rowsJ2 35 36 34 340 ≤ 1993916112173 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22240R_214 rows22240R_215 (by norm_num)

theorem c22240R_35_15 : rowsJ2 35 36 33 340 ≤ 2899177035350 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22240R_213 c22240R_35_16 (by norm_num)

theorem c22240R_35_14 : rowsJ2 35 36 32 340 ≤ 3762352917840 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22240R_212 c22240R_35_15 (by norm_num)

theorem c22240R_35_13 : rowsJ2 35 36 31 340 ≤ 4623136832693 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22240R_211 c22240R_35_14 (by norm_num)

theorem c22240R_35_12 : rowsJ2 35 36 30 340 ≤ 5514015191255 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22240R_210 c22240R_35_13 (by norm_num)

theorem c22240R_35_11 : rowsJ2 35 36 29 340 ≤ 6458882805497 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22240R_209 c22240R_35_12 (by norm_num)

theorem c22240R_35_10 : rowsJ2 35 36 28 340 ≤ 7473925648234 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22240R_208 c22240R_35_11 (by norm_num)

theorem c22240R_35_9 : rowsJ2 35 36 27 340 ≤ 8568352922929 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22240R_207 c22240R_35_10 (by norm_num)

theorem c22240R_35_8 : rowsJ2 35 36 26 340 ≤ 9736128613730 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22240R_206 c22240R_35_9 (by norm_num)

theorem c22240R_35_7 : rowsJ2 35 36 25 340 ≤ 10971754421533 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22240R_205 c22240R_35_8 (by norm_num)

theorem c22240R_35_6 : rowsJ2 35 36 24 340 ≤ 12262469786744 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22240R_204 c22240R_35_7 (by norm_num)

theorem c22240R_35_5 : rowsJ2 35 36 23 340 ≤ 13595074659169 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22240R_203 c22240R_35_6 (by norm_num)

theorem c22240R_35_4 : rowsJ2 35 36 21 340 ≤ 16244166174440 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22240R_202 c22240R_35_5 (by norm_num)

theorem c22240R_35_3 : rowsJ2 35 36 19 340 ≤ 18707142634964 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22240R_201 c22240R_35_4 (by norm_num)

theorem c22240R_35_2 : rowsJ2 35 36 17 340 ≤ 20691941789764 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22240R_200 c22240R_35_3 (by norm_num)

theorem c22240R_35_1 : rowsJ2 35 36 14 340 ≤ 22306779463501 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22240R_199 c22240R_35_2 (by norm_num)

theorem c22240R_35_0 : rowsJ2 35 36 0 340 ≤ 23045721441808 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22240R_198 c22240R_35_1 (by norm_num)

theorem hr22240R_35 : rows2 35 36 ≤ 23045721441808 := rows2_le_of_rowsJ2 35 36 c22240R_35_0

theorem c22240R_36_16 : rowsJ2 36 37 35 340 ≤ 1904139025503 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22240R_232 rows22240R_233 (by norm_num)

theorem c22240R_36_15 : rowsJ2 36 37 34 340 ≤ 2843026311250 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22240R_231 c22240R_36_16 (by norm_num)

theorem c22240R_36_14 : rowsJ2 36 37 33 340 ≤ 3718777924976 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22240R_230 c22240R_36_15 (by norm_num)

theorem c22240R_36_13 : rowsJ2 36 37 32 340 ≤ 4537706017431 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22240R_229 c22240R_36_14 (by norm_num)

theorem c22240R_36_12 : rowsJ2 36 37 31 340 ≤ 5341261910539 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22240R_228 c22240R_36_13 (by norm_num)

theorem c22240R_36_11 : rowsJ2 36 37 30 340 ≤ 6166775744327 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22240R_227 c22240R_36_12 (by norm_num)

theorem c22240R_36_10 : rowsJ2 36 37 29 340 ≤ 7035445703010 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22240R_226 c22240R_36_11 (by norm_num)

theorem c22240R_36_9 : rowsJ2 36 37 28 340 ≤ 7969842036533 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22240R_225 c22240R_36_10 (by norm_num)

theorem c22240R_36_8 : rowsJ2 36 37 27 340 ≤ 8979678014257 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22240R_224 c22240R_36_9 (by norm_num)

theorem c22240R_36_7 : rowsJ2 36 37 26 340 ≤ 10067461648730 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22240R_223 c22240R_36_8 (by norm_num)

theorem c22240R_36_6 : rowsJ2 36 37 25 340 ≤ 11223202471016 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22240R_222 c22240R_36_7 (by norm_num)

theorem c22240R_36_5 : rowsJ2 36 37 23 340 ≤ 13704885299490 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22240R_221 c22240R_36_6 (by norm_num)

theorem c22240R_36_4 : rowsJ2 36 37 21 340 ≤ 16263966441338 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22240R_220 c22240R_36_5 (by norm_num)

theorem c22240R_36_3 : rowsJ2 36 37 19 340 ≤ 18673995904369 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22240R_219 c22240R_36_4 (by norm_num)

theorem c22240R_36_2 : rowsJ2 36 37 17 340 ≤ 20677684796026 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22240R_218 c22240R_36_3 (by norm_num)

theorem c22240R_36_1 : rowsJ2 36 37 14 340 ≤ 22379777386714 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22240R_217 c22240R_36_2 (by norm_num)

theorem c22240R_36_0 : rowsJ2 36 37 0 340 ≤ 23086799544868 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22240R_216 c22240R_36_1 (by norm_num)

theorem hr22240R_36 : rows2 36 37 ≤ 23086799544868 := rows2_le_of_rowsJ2 36 37 c22240R_36_0

theorem c22240R_37_17 : rowsJ2 37 38 36 340 ≤ 1719760957386 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22240R_251 rows22240R_252 (by norm_num)

theorem c22240R_37_16 : rowsJ2 37 38 35 340 ≤ 2620192382143 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22240R_250 c22240R_37_17 (by norm_num)

theorem c22240R_37_15 : rowsJ2 37 38 34 340 ≤ 3506643025100 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22240R_249 c22240R_37_16 (by norm_num)

theorem c22240R_37_14 : rowsJ2 37 38 33 340 ≤ 4356143059086 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22240R_248 c22240R_37_15 (by norm_num)

theorem c22240R_37_13 : rowsJ2 37 38 32 340 ≤ 5137103990377 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22240R_247 c22240R_37_14 (by norm_num)

theorem c22240R_37_12 : rowsJ2 37 38 31 340 ≤ 5891441493954 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22240R_246 c22240R_37_13 (by norm_num)

theorem c22240R_37_11 : rowsJ2 37 38 30 340 ≤ 6656271523209 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22240R_245 c22240R_37_12 (by norm_num)

theorem c22240R_37_10 : rowsJ2 37 38 29 340 ≤ 7458434998523 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22240R_244 c22240R_37_11 (by norm_num)

theorem c22240R_37_9 : rowsJ2 37 38 28 340 ≤ 8313804462740 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22240R_243 c22240R_37_10 (by norm_num)

theorem c22240R_37_8 : rowsJ2 37 38 27 340 ≤ 9242391522200 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22240R_242 c22240R_37_9 (by norm_num)

theorem c22240R_37_7 : rowsJ2 37 38 26 340 ≤ 10248433226274 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22240R_241 c22240R_37_8 (by norm_num)

theorem c22240R_37_6 : rowsJ2 37 38 25 340 ≤ 11327727590693 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22240R_240 c22240R_37_7 (by norm_num)

theorem c22240R_37_5 : rowsJ2 37 38 23 340 ≤ 13662819224917 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22240R_239 c22240R_37_6 (by norm_num)

theorem c22240R_37_4 : rowsJ2 37 38 21 340 ≤ 16124789370265 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22240R_238 c22240R_37_5 (by norm_num)

theorem c22240R_37_3 : rowsJ2 37 38 19 340 ≤ 18476616894357 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22240R_237 c22240R_37_4 (by norm_num)

theorem c22240R_37_2 : rowsJ2 37 38 17 340 ≤ 20489049746080 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22240R_236 c22240R_37_3 (by norm_num)

theorem c22240R_37_1 : rowsJ2 37 38 14 340 ≤ 22271778132015 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22240R_235 c22240R_37_2 (by norm_num)

theorem c22240R_37_0 : rowsJ2 37 38 0 340 ≤ 22965641405941 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22240R_234 c22240R_37_1 (by norm_num)

theorem hr22240R_37 : rows2 37 38 ≤ 22965641405941 := rows2_le_of_rowsJ2 37 38 c22240R_37_0

theorem c22240R_38_18 : rowsJ2 38 39 37 340 ≤ 1377725494887 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22240R_271 rows22240R_272 (by norm_num)

theorem c22240R_38_17 : rowsJ2 38 39 36 340 ≤ 2141348577646 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22240R_270 c22240R_38_18 (by norm_num)

theorem c22240R_38_16 : rowsJ2 38 39 35 340 ≤ 2926757872788 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22240R_269 c22240R_38_17 (by norm_num)

theorem c22240R_38_15 : rowsJ2 38 39 34 340 ≤ 3726885786443 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22240R_268 c22240R_38_16 (by norm_num)

theorem c22240R_38_14 : rowsJ2 38 39 33 340 ≤ 4499500435149 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22240R_267 c22240R_38_15 (by norm_num)

theorem c22240R_38_13 : rowsJ2 38 39 32 340 ≤ 5224282335315 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22240R_266 c22240R_38_14 (by norm_num)

theorem c22240R_38_12 : rowsJ2 38 39 31 340 ≤ 5917612561530 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22240R_265 c22240R_38_13 (by norm_num)

theorem c22240R_38_11 : rowsJ2 38 39 30 340 ≤ 6621440729567 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22240R_264 c22240R_38_12 (by norm_num)

theorem c22240R_38_10 : rowsJ2 38 39 29 340 ≤ 7352698025738 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22240R_263 c22240R_38_11 (by norm_num)

theorem c22240R_38_9 : rowsJ2 38 39 28 340 ≤ 8136649660451 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22240R_262 c22240R_38_10 (by norm_num)

theorem c22240R_38_8 : rowsJ2 38 39 27 340 ≤ 8983532092146 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22240R_261 c22240R_38_9 (by norm_num)

theorem c22240R_38_7 : rowsJ2 38 39 26 340 ≤ 9910476297396 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22240R_260 c22240R_38_8 (by norm_num)

theorem c22240R_38_6 : rowsJ2 38 39 25 340 ≤ 10910857104249 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22240R_259 c22240R_38_7 (by norm_num)

theorem c22240R_38_5 : rowsJ2 38 39 23 340 ≤ 13100345562187 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22240R_258 c22240R_38_6 (by norm_num)

theorem c22240R_38_4 : rowsJ2 38 39 21 340 ≤ 15453927417745 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22240R_257 c22240R_38_5 (by norm_num)

theorem c22240R_38_3 : rowsJ2 38 39 19 340 ≤ 17744218174874 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22240R_256 c22240R_38_4 (by norm_num)

theorem c22240R_38_2 : rowsJ2 38 39 17 340 ≤ 19754574673083 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22240R_255 c22240R_38_3 (by norm_num)

theorem c22240R_38_1 : rowsJ2 38 39 14 340 ≤ 21612886255168 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22240R_254 c22240R_38_2 (by norm_num)

theorem c22240R_38_0 : rowsJ2 38 39 0 340 ≤ 22316248803050 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22240R_253 c22240R_38_1 (by norm_num)

theorem hr22240R_38 : rows2 38 39 ≤ 22316248803050 := rows2_le_of_rowsJ2 38 39 c22240R_38_0

theorem c22240R_39_19 : rowsJ2 39 40 38 340 ≤ 1019743785554 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22240R_292 rows22240R_293 (by norm_num)

theorem c22240R_39_18 : rowsJ2 39 40 37 340 ≤ 1615551400427 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22240R_291 c22240R_39_19 (by norm_num)

theorem c22240R_39_17 : rowsJ2 39 40 36 340 ≤ 2258968415525 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22240R_290 c22240R_39_18 (by norm_num)

theorem c22240R_39_16 : rowsJ2 39 40 35 340 ≤ 2941530028702 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22240R_289 c22240R_39_17 (by norm_num)

theorem c22240R_39_15 : rowsJ2 39 40 34 340 ≤ 3642065624145 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22240R_288 c22240R_39_16 (by norm_num)

theorem c22240R_39_14 : rowsJ2 39 40 33 340 ≤ 4343929931922 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22240R_287 c22240R_39_15 (by norm_num)

theorem c22240R_39_13 : rowsJ2 39 40 32 340 ≤ 5013104454954 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22240R_286 c22240R_39_14 (by norm_num)

theorem c22240R_39_12 : rowsJ2 39 40 31 340 ≤ 5651337230425 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22240R_285 c22240R_39_13 (by norm_num)

theorem c22240R_39_11 : rowsJ2 39 40 30 340 ≤ 6294788492799 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22240R_284 c22240R_39_12 (by norm_num)

theorem c22240R_39_10 : rowsJ2 39 40 29 340 ≤ 6965469275263 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22240R_283 c22240R_39_11 (by norm_num)

theorem c22240R_39_9 : rowsJ2 39 40 28 340 ≤ 7678741955546 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22240R_282 c22240R_39_10 (by norm_num)

theorem c22240R_39_8 : rowsJ2 39 40 27 340 ≤ 8454316723631 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22240R_281 c22240R_39_9 (by norm_num)

theorem c22240R_39_7 : rowsJ2 39 40 26 340 ≤ 9299567142895 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22240R_280 c22240R_39_8 (by norm_num)

theorem c22240R_39_6 : rowsJ2 39 40 25 340 ≤ 10224325788231 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22240R_279 c22240R_39_7 (by norm_num)

theorem c22240R_39_5 : rowsJ2 39 40 23 340 ≤ 12269058176630 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22240R_278 c22240R_39_6 (by norm_num)

theorem c22240R_39_4 : rowsJ2 39 40 21 340 ≤ 14502893125257 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22240R_277 c22240R_39_5 (by norm_num)

theorem c22240R_39_3 : rowsJ2 39 40 19 340 ≤ 16728285509297 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22240R_276 c22240R_39_4 (by norm_num)

theorem c22240R_39_2 : rowsJ2 39 40 17 340 ≤ 18722538316171 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22240R_275 c22240R_39_3 (by norm_num)

theorem c22240R_39_1 : rowsJ2 39 40 14 340 ≤ 20654183019426 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22240R_274 c22240R_39_2 (by norm_num)

theorem c22240R_39_0 : rowsJ2 39 40 0 340 ≤ 21378258243344 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22240R_273 c22240R_39_1 (by norm_num)

theorem hr22240R_39 : rows2 39 40 ≤ 21378258243344 := rows2_le_of_rowsJ2 39 40 c22240R_39_0

theorem c22240R_40_20 : rowsJ2 40 41 39 340 ≤ 739829366410 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22240R_314 rows22240R_315 (by norm_num)

theorem c22240R_40_19 : rowsJ2 40 41 38 340 ≤ 1191253826742 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22240R_313 c22240R_40_20 (by norm_num)

theorem c22240R_40_18 : rowsJ2 40 41 37 340 ≤ 1689740218249 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22240R_312 c22240R_40_19 (by norm_num)

theorem c22240R_40_17 : rowsJ2 40 41 36 340 ≤ 2244338463946 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22240R_311 c22240R_40_18 (by norm_num)

theorem c22240R_40_16 : rowsJ2 40 41 35 340 ≤ 2834019641436 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22240R_310 c22240R_40_17 (by norm_num)

theorem c22240R_40_15 : rowsJ2 40 41 34 340 ≤ 3458154820516 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22240R_309 c22240R_40_16 (by norm_num)

theorem c22240R_40_14 : rowsJ2 40 41 33 340 ≤ 4083254198660 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22240R_308 c22240R_40_15 (by norm_num)

theorem c22240R_40_13 : rowsJ2 40 41 32 340 ≤ 4702697357437 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22240R_307 c22240R_40_14 (by norm_num)

theorem c22240R_40_12 : rowsJ2 40 41 31 340 ≤ 5286363342219 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22240R_306 c22240R_40_13 (by norm_num)

theorem c22240R_40_11 : rowsJ2 40 41 30 340 ≤ 5875322606670 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22240R_305 c22240R_40_12 (by norm_num)

theorem c22240R_40_10 : rowsJ2 40 41 29 340 ≤ 6486024346367 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22240R_304 c22240R_40_11 (by norm_num)

theorem c22240R_40_9 : rowsJ2 40 41 28 340 ≤ 7138938133003 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22240R_303 c22240R_40_10 (by norm_num)

theorem c22240R_40_8 : rowsJ2 40 41 27 340 ≤ 7843920568914 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22240R_302 c22240R_40_9 (by norm_num)

theorem c22240R_40_7 : rowsJ2 40 41 26 340 ≤ 8617869427054 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22240R_301 c22240R_40_8 (by norm_num)

theorem c22240R_40_6 : rowsJ2 40 41 25 340 ≤ 9464370390046 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22240R_300 c22240R_40_7 (by norm_num)

theorem c22240R_40_5 : rowsJ2 40 41 23 340 ≤ 11365045705940 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22240R_299 c22240R_40_6 (by norm_num)

theorem c22240R_40_4 : rowsJ2 40 41 21 340 ≤ 13473775683813 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22240R_298 c22240R_40_5 (by norm_num)

theorem c22240R_40_3 : rowsJ2 40 41 19 340 ≤ 15626729724866 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22240R_297 c22240R_40_4 (by norm_num)

theorem c22240R_40_2 : rowsJ2 40 41 17 340 ≤ 17592822914583 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22240R_296 c22240R_40_3 (by norm_num)

theorem c22240R_40_1 : rowsJ2 40 41 14 340 ≤ 19599040427362 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22240R_295 c22240R_40_2 (by norm_num)

theorem c22240R_40_0 : rowsJ2 40 41 0 340 ≤ 20356543676250 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22240R_294 c22240R_40_1 (by norm_num)

theorem hr22240R_40 : rows2 40 41 ≤ 20356543676250 := rows2_le_of_rowsJ2 40 41 c22240R_40_0

theorem c22240R_41_21 : rowsJ2 41 42 40 340 ≤ 509323553505 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_337 rows22240R_338 (by norm_num)

theorem c22240R_41_20 : rowsJ2 41 42 39 340 ≤ 828229771527 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_336 c22240R_41_21 (by norm_num)

theorem c22240R_41_19 : rowsJ2 41 42 38 340 ≤ 1191200176994 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_335 c22240R_41_20 (by norm_num)

theorem c22240R_41_18 : rowsJ2 41 42 37 340 ≤ 1606507706257 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_334 c22240R_41_19 (by norm_num)

theorem c22240R_41_17 : rowsJ2 41 42 36 340 ≤ 2067072161128 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_333 c22240R_41_18 (by norm_num)

theorem c22240R_41_16 : rowsJ2 41 42 35 340 ≤ 2574639345510 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_332 c22240R_41_17 (by norm_num)

theorem c22240R_41_15 : rowsJ2 41 42 34 340 ≤ 3112623871616 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_331 c22240R_41_16 (by norm_num)

theorem c22240R_41_14 : rowsJ2 41 42 33 340 ≤ 3672684135257 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_330 c22240R_41_15 (by norm_num)

theorem c22240R_41_13 : rowsJ2 41 42 32 340 ≤ 4226782055746 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_329 c22240R_41_14 (by norm_num)

theorem c22240R_41_12 : rowsJ2 41 42 31 340 ≤ 4761724941095 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_328 c22240R_41_13 (by norm_num)

theorem c22240R_41_11 : rowsJ2 41 42 30 340 ≤ 5296693432291 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_327 c22240R_41_12 (by norm_num)

theorem c22240R_41_10 : rowsJ2 41 42 29 340 ≤ 5853283505400 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_326 c22240R_41_11 (by norm_num)

theorem c22240R_41_9 : rowsJ2 41 42 28 340 ≤ 6446413475899 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_325 c22240R_41_10 (by norm_num)

theorem c22240R_41_8 : rowsJ2 41 42 27 340 ≤ 7091120548300 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_324 c22240R_41_9 (by norm_num)

theorem c22240R_41_7 : rowsJ2 41 42 26 340 ≤ 7794462205867 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_323 c22240R_41_8 (by norm_num)

theorem c22240R_41_6 : rowsJ2 41 42 25 340 ≤ 8569611609784 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_322 c22240R_41_7 (by norm_num)

theorem c22240R_41_5 : rowsJ2 41 42 23 340 ≤ 10326786908825 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_321 c22240R_41_6 (by norm_num)

theorem c22240R_41_4 : rowsJ2 41 42 21 340 ≤ 12304939294034 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_320 c22240R_41_5 (by norm_num)

theorem c22240R_41_3 : rowsJ2 41 42 19 340 ≤ 14377865940676 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_319 c22240R_41_4 (by norm_num)

theorem c22240R_41_2 : rowsJ2 41 42 17 340 ≤ 16303751468603 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_318 c22240R_41_3 (by norm_num)

theorem c22240R_41_1 : rowsJ2 41 42 14 340 ≤ 18376823541022 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_317 c22240R_41_2 (by norm_num)

theorem c22240R_41_0 : rowsJ2 41 42 0 340 ≤ 19182668539750 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22240R_316 c22240R_41_1 (by norm_num)

theorem hr22240R_41 : rows2 41 42 ≤ 19182668539750 := rows2_le_of_rowsJ2 41 42 c22240R_41_0

theorem c22240R_42_21 : rowsJ2 42 43 41 340 ≤ 327201523177 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_360 rows22240R_361 (by norm_num)

theorem c22240R_42_20 : rowsJ2 42 43 40 340 ≤ 540502961660 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_359 c22240R_42_21 (by norm_num)

theorem c22240R_42_19 : rowsJ2 42 43 39 340 ≤ 785961709955 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_358 c22240R_42_20 (by norm_num)

theorem c22240R_42_18 : rowsJ2 42 43 38 340 ≤ 1076654576294 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_357 c22240R_42_19 (by norm_num)

theorem c22240R_42_17 : rowsJ2 42 43 37 340 ≤ 1406741958156 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_356 c22240R_42_18 (by norm_num)

theorem c22240R_42_16 : rowsJ2 42 43 36 340 ≤ 1787364057852 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_355 c22240R_42_17 (by norm_num)

theorem c22240R_42_15 : rowsJ2 42 43 35 340 ≤ 2207506944737 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_354 c22240R_42_16 (by norm_num)

theorem c22240R_42_14 : rowsJ2 42 43 34 340 ≤ 2670022253888 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_353 c22240R_42_15 (by norm_num)

theorem c22240R_42_13 : rowsJ2 42 43 33 340 ≤ 3155142901133 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_352 c22240R_42_14 (by norm_num)

theorem c22240R_42_12 : rowsJ2 42 43 32 340 ≤ 3655491872834 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_351 c22240R_42_13 (by norm_num)

theorem c22240R_42_11 : rowsJ2 42 43 31 340 ≤ 4142130411540 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_350 c22240R_42_12 (by norm_num)

theorem c22240R_42_10 : rowsJ2 42 43 30 340 ≤ 4628932220059 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_349 c22240R_42_11 (by norm_num)

theorem c22240R_42_9 : rowsJ2 42 43 29 340 ≤ 5131887909793 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_348 c22240R_42_10 (by norm_num)

theorem c22240R_42_8 : rowsJ2 42 43 28 340 ≤ 5671090432030 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_347 c22240R_42_9 (by norm_num)

theorem c22240R_42_7 : rowsJ2 42 43 27 340 ≤ 6256078071103 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_346 c22240R_42_8 (by norm_num)

theorem c22240R_42_6 : rowsJ2 42 43 26 340 ≤ 6899131940225 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_345 c22240R_42_7 (by norm_num)

theorem c22240R_42_5 : rowsJ2 42 43 24 340 ≤ 8380858777263 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_344 c22240R_42_6 (by norm_num)

theorem c22240R_42_4 : rowsJ2 42 43 22 340 ≤ 10122078902106 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_343 c22240R_42_5 (by norm_num)

theorem c22240R_42_3 : rowsJ2 42 43 20 340 ≤ 12056532220475 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_342 c22240R_42_4 (by norm_num)

theorem c22240R_42_2 : rowsJ2 42 43 17 340 ≤ 14932590092003 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_341 c22240R_42_3 (by norm_num)

theorem c22240R_42_1 : rowsJ2 42 43 14 340 ≤ 17057566347086 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_340 c22240R_42_2 (by norm_num)

theorem c22240R_42_0 : rowsJ2 42 43 0 340 ≤ 17927130484293 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22240R_339 c22240R_42_1 (by norm_num)

theorem hr22240R_42 : rows2 42 43 ≤ 17927130484293 := rows2_le_of_rowsJ2 42 43 c22240R_42_0

theorem c22240R_43_22 : rowsJ2 43 44 42 340 ≤ 181701500202 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_384 rows22240R_385 (by norm_num)

theorem c22240R_43_21 : rowsJ2 43 44 41 340 ≤ 309284203773 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_383 c22240R_43_22 (by norm_num)

theorem c22240R_43_20 : rowsJ2 43 44 40 340 ≤ 463367012168 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_382 c22240R_43_21 (by norm_num)

theorem c22240R_43_19 : rowsJ2 43 44 39 340 ≤ 649430702745 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_381 c22240R_43_20 (by norm_num)

theorem c22240R_43_18 : rowsJ2 43 44 38 340 ≤ 867733936268 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_380 c22240R_43_19 (by norm_num)

theorem c22240R_43_17 : rowsJ2 43 44 37 340 ≤ 1126645219828 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_379 c22240R_43_18 (by norm_num)

theorem c22240R_43_16 : rowsJ2 43 44 36 340 ≤ 1425228251487 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_378 c22240R_43_17 (by norm_num)

theorem c22240R_43_15 : rowsJ2 43 44 35 340 ≤ 1768659456110 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_377 c22240R_43_16 (by norm_num)

theorem c22240R_43_14 : rowsJ2 43 44 34 340 ≤ 2150302028846 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_376 c22240R_43_15 (by norm_num)

theorem c22240R_43_13 : rowsJ2 43 44 33 340 ≤ 2566582346233 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_375 c22240R_43_14 (by norm_num)

theorem c22240R_43_12 : rowsJ2 43 44 32 340 ≤ 3003134516251 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_374 c22240R_43_13 (by norm_num)

theorem c22240R_43_11 : rowsJ2 43 44 31 340 ≤ 3447267911565 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_373 c22240R_43_12 (by norm_num)

theorem c22240R_43_10 : rowsJ2 43 44 30 340 ≤ 3886295920731 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_372 c22240R_43_11 (by norm_num)

theorem c22240R_43_9 : rowsJ2 43 44 29 340 ≤ 4341428606117 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_371 c22240R_43_10 (by norm_num)

theorem c22240R_43_8 : rowsJ2 43 44 28 340 ≤ 4827161674705 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_370 c22240R_43_9 (by norm_num)

theorem c22240R_43_7 : rowsJ2 43 44 27 340 ≤ 5358280005709 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_369 c22240R_43_8 (by norm_num)

theorem c22240R_43_6 : rowsJ2 43 44 26 340 ≤ 5941585144115 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_368 c22240R_43_7 (by norm_num)

theorem c22240R_43_5 : rowsJ2 43 44 24 340 ≤ 7292182726605 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_367 c22240R_43_6 (by norm_num)

theorem c22240R_43_4 : rowsJ2 43 44 22 340 ≤ 8900960317865 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_366 c22240R_43_5 (by norm_num)

theorem c22240R_43_3 : rowsJ2 43 44 20 340 ≤ 10712447408839 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_365 c22240R_43_4 (by norm_num)

theorem c22240R_43_2 : rowsJ2 43 44 17 340 ≤ 13498324714337 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_364 c22240R_43_3 (by norm_num)

theorem c22240R_43_1 : rowsJ2 43 44 14 340 ≤ 15653934860449 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_363 c22240R_43_2 (by norm_num)

theorem c22240R_43_0 : rowsJ2 43 44 0 340 ≤ 16602336612067 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22240R_362 c22240R_43_1 (by norm_num)

theorem hr22240R_43 : rows2 43 44 ≤ 16602336612067 := rows2_le_of_rowsJ2 43 44 c22240R_43_0

theorem c22240R_44_23 : rowsJ2 44 45 43 340 ≤ 97844527219 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_409 rows22240R_410 (by norm_num)

theorem c22240R_44_22 : rowsJ2 44 45 42 340 ≤ 174004107559 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_408 c22240R_44_23 (by norm_num)

theorem c22240R_44_21 : rowsJ2 44 45 41 340 ≤ 268834859440 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_407 c22240R_44_22 (by norm_num)

theorem c22240R_44_20 : rowsJ2 44 45 40 340 ≤ 390020102743 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_406 c22240R_44_21 (by norm_num)

theorem c22240R_44_19 : rowsJ2 44 45 39 340 ≤ 535572916071 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_405 c22240R_44_20 (by norm_num)

theorem c22240R_44_18 : rowsJ2 44 45 38 340 ≤ 713164826252 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_404 c22240R_44_19 (by norm_num)

theorem c22240R_44_17 : rowsJ2 44 45 37 340 ≤ 920175169163 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_403 c22240R_44_18 (by norm_num)

theorem c22240R_44_16 : rowsJ2 44 45 36 340 ≤ 1167878788633 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_402 c22240R_44_17 (by norm_num)

theorem c22240R_44_15 : rowsJ2 44 45 35 340 ≤ 1449826080467 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_401 c22240R_44_16 (by norm_num)

theorem c22240R_44_14 : rowsJ2 44 45 34 340 ≤ 1774760143572 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_400 c22240R_44_15 (by norm_num)

theorem c22240R_44_13 : rowsJ2 44 45 33 340 ≤ 2128795874648 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_399 c22240R_44_14 (by norm_num)

theorem c22240R_44_12 : rowsJ2 44 45 32 340 ≤ 2514033673676 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_398 c22240R_44_13 (by norm_num)

theorem c22240R_44_11 : rowsJ2 44 45 31 340 ≤ 2908718653884 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_397 c22240R_44_12 (by norm_num)

theorem c22240R_44_10 : rowsJ2 44 45 30 340 ≤ 3305757304866 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_396 c22240R_44_11 (by norm_num)

theorem c22240R_44_9 : rowsJ2 44 45 29 340 ≤ 3713439035351 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_395 c22240R_44_10 (by norm_num)

theorem c22240R_44_8 : rowsJ2 44 45 28 340 ≤ 4151507418959 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_394 c22240R_44_9 (by norm_num)

theorem c22240R_44_7 : rowsJ2 44 45 27 340 ≤ 4629198091014 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_393 c22240R_44_8 (by norm_num)

theorem c22240R_44_6 : rowsJ2 44 45 26 340 ≤ 5158602234633 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_392 c22240R_44_7 (by norm_num)

theorem c22240R_44_5 : rowsJ2 44 45 25 340 ≤ 5742897250456 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_391 c22240R_44_6 (by norm_num)

theorem c22240R_44_4 : rowsJ2 44 45 23 340 ≤ 7097645241176 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_390 c22240R_44_5 (by norm_num)

theorem c22240R_44_3 : rowsJ2 44 45 20 340 ≤ 9558139651883 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_389 c22240R_44_4 (by norm_num)

theorem c22240R_44_2 : rowsJ2 44 45 17 340 ≤ 12236842023071 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_388 c22240R_44_3 (by norm_num)

theorem c22240R_44_1 : rowsJ2 44 45 14 340 ≤ 14406163484499 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_387 c22240R_44_2 (by norm_num)

theorem c22240R_44_0 : rowsJ2 44 45 0 340 ≤ 15451038662270 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22240R_386 c22240R_44_1 (by norm_num)

theorem hr22240R_44 : rows2 44 45 ≤ 15451038662270 := rows2_le_of_rowsJ2 44 45 c22240R_44_0

theorem c22240R_45_24 : rowsJ2 45 46 44 340 ≤ 201379545523 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_435 rows22240R_436 (by norm_num)

theorem c22240R_45_23 : rowsJ2 45 46 43 340 ≤ 239550286259 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_434 c22240R_45_24 (by norm_num)

theorem c22240R_45_22 : rowsJ2 45 46 42 340 ≤ 290754369443 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_433 c22240R_45_23 (by norm_num)

theorem c22240R_45_21 : rowsJ2 45 46 41 340 ≤ 360551016967 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_432 c22240R_45_22 (by norm_num)

theorem c22240R_45_20 : rowsJ2 45 46 40 340 ≤ 449053688819 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_431 c22240R_45_21 (by norm_num)

theorem c22240R_45_19 : rowsJ2 45 46 39 340 ≤ 561800693863 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_430 c22240R_45_20 (by norm_num)

theorem c22240R_45_18 : rowsJ2 45 46 38 340 ≤ 698966824516 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_429 c22240R_45_19 (by norm_num)

theorem c22240R_45_17 : rowsJ2 45 46 37 340 ≤ 865380376660 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_428 c22240R_45_18 (by norm_num)

theorem c22240R_45_16 : rowsJ2 45 46 36 340 ≤ 1061284717483 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_427 c22240R_45_17 (by norm_num)

theorem c22240R_45_15 : rowsJ2 45 46 35 340 ≤ 1293811253136 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_426 c22240R_45_16 (by norm_num)

theorem c22240R_45_14 : rowsJ2 45 46 34 340 ≤ 1558718927297 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_425 c22240R_45_15 (by norm_num)

theorem c22240R_45_13 : rowsJ2 45 46 33 340 ≤ 1860061898502 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_424 c22240R_45_14 (by norm_num)

theorem c22240R_45_12 : rowsJ2 45 46 32 340 ≤ 2187086586546 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_423 c22240R_45_13 (by norm_num)

theorem c22240R_45_11 : rowsJ2 45 46 31 340 ≤ 2538163423112 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_422 c22240R_45_12 (by norm_num)

theorem c22240R_45_10 : rowsJ2 45 46 30 340 ≤ 2893511553036 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_421 c22240R_45_11 (by norm_num)

theorem c22240R_45_9 : rowsJ2 45 46 29 340 ≤ 3259518456698 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_420 c22240R_45_10 (by norm_num)

theorem c22240R_45_8 : rowsJ2 45 46 28 340 ≤ 3650277634913 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_419 c22240R_45_9 (by norm_num)

theorem c22240R_45_7 : rowsJ2 45 46 27 340 ≤ 4080343280827 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_418 c22240R_45_8 (by norm_num)

theorem c22240R_45_6 : rowsJ2 45 46 26 340 ≤ 4556273778001 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_417 c22240R_45_7 (by norm_num)

theorem c22240R_45_5 : rowsJ2 45 46 25 340 ≤ 5086589840994 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_416 c22240R_45_6 (by norm_num)

theorem c22240R_45_4 : rowsJ2 45 46 23 340 ≤ 6320850208781 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_415 c22240R_45_5 (by norm_num)

theorem c22240R_45_3 : rowsJ2 45 46 20 340 ≤ 8598788090011 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_414 c22240R_45_4 (by norm_num)

theorem c22240R_45_2 : rowsJ2 45 46 17 340 ≤ 11159156676068 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_413 c22240R_45_3 (by norm_num)

theorem c22240R_45_1 : rowsJ2 45 46 14 340 ≤ 13319255084726 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_412 c22240R_45_2 (by norm_num)

theorem c22240R_45_0 : rowsJ2 45 46 0 340 ≤ 14468517756344 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22240R_411 c22240R_45_1 (by norm_num)

theorem hr22240R_45 : rows2 45 46 ≤ 14468517756344 := rows2_le_of_rowsJ2 45 46 c22240R_45_0

theorem c22240R_46_25 : rowsJ2 46 47 45 340 ≤ 711971043636 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_462 rows22240R_463 (by norm_num)

theorem c22240R_46_24 : rowsJ2 46 47 44 340 ≤ 727755215883 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_461 c22240R_46_25 (by norm_num)

theorem c22240R_46_23 : rowsJ2 46 47 43 340 ≤ 748760221038 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_460 c22240R_46_24 (by norm_num)

theorem c22240R_46_22 : rowsJ2 46 47 42 340 ≤ 782752633191 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_459 c22240R_46_23 (by norm_num)

theorem c22240R_46_21 : rowsJ2 46 47 41 340 ≤ 827659554188 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_458 c22240R_46_22 (by norm_num)

theorem c22240R_46_20 : rowsJ2 46 47 40 340 ≤ 891192650416 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_457 c22240R_46_21 (by norm_num)

theorem c22240R_46_19 : rowsJ2 46 47 39 340 ≤ 971338728485 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_456 c22240R_46_20 (by norm_num)

theorem c22240R_46_18 : rowsJ2 46 47 38 340 ≤ 1075778856606 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_455 c22240R_46_19 (by norm_num)

theorem c22240R_46_17 : rowsJ2 46 47 37 340 ≤ 1201868474598 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_454 c22240R_46_18 (by norm_num)

theorem c22240R_46_16 : rowsJ2 46 47 36 340 ≤ 1357275222113 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_453 c22240R_46_17 (by norm_num)

theorem c22240R_46_15 : rowsJ2 46 47 35 340 ≤ 1539434246158 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_452 c22240R_46_16 (by norm_num)

theorem c22240R_46_14 : rowsJ2 46 47 34 340 ≤ 1756367149679 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_451 c22240R_46_15 (by norm_num)

theorem c22240R_46_13 : rowsJ2 46 47 33 340 ≤ 2001644495937 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_450 c22240R_46_14 (by norm_num)

theorem c22240R_46_12 : rowsJ2 46 47 32 340 ≤ 2279971733632 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_449 c22240R_46_13 (by norm_num)

theorem c22240R_46_11 : rowsJ2 46 47 31 340 ≤ 2580444123526 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_448 c22240R_46_12 (by norm_num)

theorem c22240R_46_10 : rowsJ2 46 47 30 340 ≤ 2899866884134 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_447 c22240R_46_11 (by norm_num)

theorem c22240R_46_9 : rowsJ2 46 47 29 340 ≤ 3224479704092 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_446 c22240R_46_10 (by norm_num)

theorem c22240R_46_8 : rowsJ2 46 47 28 340 ≤ 3573703220955 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_445 c22240R_46_9 (by norm_num)

theorem c22240R_46_7 : rowsJ2 46 47 27 340 ≤ 3956485426818 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_444 c22240R_46_8 (by norm_num)

theorem c22240R_46_6 : rowsJ2 46 47 26 340 ≤ 4384746407930 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_443 c22240R_46_7 (by norm_num)

theorem c22240R_46_5 : rowsJ2 46 47 25 340 ≤ 4861497592455 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_442 c22240R_46_6 (by norm_num)

theorem c22240R_46_4 : rowsJ2 46 47 23 340 ≤ 5981615031880 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_441 c22240R_46_5 (by norm_num)

theorem c22240R_46_3 : rowsJ2 46 47 21 340 ≤ 7335328583608 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_440 c22240R_46_4 (by norm_num)

theorem c22240R_46_2 : rowsJ2 46 47 18 340 ≤ 9695809010323 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_439 c22240R_46_3 (by norm_num)

theorem c22240R_46_1 : rowsJ2 46 47 14 340 ≤ 12653614019295 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_438 c22240R_46_2 (by norm_num)

theorem c22240R_46_0 : rowsJ2 46 47 0 340 ≤ 13914682490722 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22240R_437 c22240R_46_1 (by norm_num)

theorem hr22240R_46 : rows2 46 47 ≤ 13914682490722 := rows2_le_of_rowsJ2 46 47 c22240R_46_0

theorem c22240R_47_25 : rowsJ2 47 48 46 340 ≤ 1431016622663 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_489 rows22240R_490 (by norm_num)

theorem c22240R_47_24 : rowsJ2 47 48 45 340 ≤ 1669158052498 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_488 c22240R_47_25 (by norm_num)

theorem c22240R_47_23 : rowsJ2 47 48 44 340 ≤ 1755244535393 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_487 c22240R_47_24 (by norm_num)

theorem c22240R_47_22 : rowsJ2 47 48 43 340 ≤ 1766874641238 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_486 c22240R_47_23 (by norm_num)

theorem c22240R_47_21 : rowsJ2 47 48 42 340 ≤ 1783742265558 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_485 c22240R_47_22 (by norm_num)

theorem c22240R_47_20 : rowsJ2 47 48 41 340 ≤ 1811500517465 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_484 c22240R_47_21 (by norm_num)

theorem c22240R_47_19 : rowsJ2 47 48 40 340 ≤ 1850200972453 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_483 c22240R_47_20 (by norm_num)

theorem c22240R_47_18 : rowsJ2 47 48 39 340 ≤ 1905455957049 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_482 c22240R_47_19 (by norm_num)

theorem c22240R_47_17 : rowsJ2 47 48 38 340 ≤ 1977365187069 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_481 c22240R_47_18 (by norm_num)

theorem c22240R_47_16 : rowsJ2 47 48 37 340 ≤ 2070826997280 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_480 c22240R_47_17 (by norm_num)

theorem c22240R_47_15 : rowsJ2 47 48 36 340 ≤ 2185996748705 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_479 c22240R_47_16 (by norm_num)

theorem c22240R_47_14 : rowsJ2 47 48 35 340 ≤ 2327772320820 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_478 c22240R_47_15 (by norm_num)

theorem c22240R_47_13 : rowsJ2 47 48 34 340 ≤ 2495757190643 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_477 c22240R_47_14 (by norm_num)

theorem c22240R_47_12 : rowsJ2 47 48 33 340 ≤ 2694517858092 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_476 c22240R_47_13 (by norm_num)

theorem c22240R_47_11 : rowsJ2 47 48 32 340 ≤ 2920720496611 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_475 c22240R_47_12 (by norm_num)

theorem c22240R_47_10 : rowsJ2 47 48 31 340 ≤ 3176476513185 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_474 c22240R_47_11 (by norm_num)

theorem c22240R_47_9 : rowsJ2 47 48 30 340 ≤ 3452881166158 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_473 c22240R_47_10 (by norm_num)

theorem c22240R_47_8 : rowsJ2 47 48 29 340 ≤ 3741860787823 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_472 c22240R_47_9 (by norm_num)

theorem c22240R_47_7 : rowsJ2 47 48 28 340 ≤ 4049815210484 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_471 c22240R_47_8 (by norm_num)

theorem c22240R_47_6 : rowsJ2 47 48 27 340 ≤ 4391089157164 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_470 c22240R_47_7 (by norm_num)

theorem c22240R_47_5 : rowsJ2 47 48 26 340 ≤ 4772010158317 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_469 c22240R_47_6 (by norm_num)

theorem c22240R_47_4 : rowsJ2 47 48 24 340 ≤ 5679341788777 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_468 c22240R_47_5 (by norm_num)

theorem c22240R_47_3 : rowsJ2 47 48 21 340 ≤ 7453031183858 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_467 c22240R_47_4 (by norm_num)

theorem c22240R_47_2 : rowsJ2 47 48 18 340 ≤ 9651896552254 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_466 c22240R_47_3 (by norm_num)

theorem c22240R_47_1 : rowsJ2 47 48 14 340 ≤ 12539510334314 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_465 c22240R_47_2 (by norm_num)

theorem c22240R_47_0 : rowsJ2 47 48 0 340 ≤ 13911942184858 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22240R_464 c22240R_47_1 (by norm_num)

theorem hr22240R_47 : rows2 47 48 ≤ 13911942184858 := rows2_le_of_rowsJ2 47 48 c22240R_47_0

theorem c22240R_48_26 : rowsJ2 48 49 47 340 ≤ 2795796498287 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_517 rows22240R_518 (by norm_num)

theorem c22240R_48_25 : rowsJ2 48 49 46 340 ≤ 3247966254674 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_516 c22240R_48_26 (by norm_num)

theorem c22240R_48_24 : rowsJ2 48 49 45 340 ≤ 3481717937659 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_515 c22240R_48_25 (by norm_num)

theorem c22240R_48_23 : rowsJ2 48 49 44 340 ≤ 3565027507554 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_514 c22240R_48_24 (by norm_num)

theorem c22240R_48_22 : rowsJ2 48 49 43 340 ≤ 3570126370008 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_513 c22240R_48_23 (by norm_num)

theorem c22240R_48_21 : rowsJ2 48 49 42 340 ≤ 3580453274074 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_512 c22240R_48_22 (by norm_num)

theorem c22240R_48_20 : rowsJ2 48 49 41 340 ≤ 3595374163348 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_511 c22240R_48_21 (by norm_num)

theorem c22240R_48_19 : rowsJ2 48 49 40 340 ≤ 3621202622212 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_510 c22240R_48_20 (by norm_num)

theorem c22240R_48_18 : rowsJ2 48 49 39 340 ≤ 3657343622454 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_509 c22240R_48_19 (by norm_num)

theorem c22240R_48_17 : rowsJ2 48 49 38 340 ≤ 3710068789557 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_508 c22240R_48_18 (by norm_num)

theorem c22240R_48_16 : rowsJ2 48 49 37 340 ≤ 3778147627331 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_507 c22240R_48_17 (by norm_num)

theorem c22240R_48_15 : rowsJ2 48 49 36 340 ≤ 3867826379847 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_506 c22240R_48_16 (by norm_num)

theorem c22240R_48_14 : rowsJ2 48 49 35 340 ≤ 3977936899543 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_505 c22240R_48_15 (by norm_num)

theorem c22240R_48_13 : rowsJ2 48 49 34 340 ≤ 4114722027269 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_504 c22240R_48_14 (by norm_num)

theorem c22240R_48_12 : rowsJ2 48 49 33 340 ≤ 4274575458036 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_503 c22240R_48_13 (by norm_num)

theorem c22240R_48_11 : rowsJ2 48 49 32 340 ≤ 4464667251249 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_502 c22240R_48_12 (by norm_num)

theorem c22240R_48_10 : rowsJ2 48 49 31 340 ≤ 4678089703816 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_501 c22240R_48_11 (by norm_num)

theorem c22240R_48_9 : rowsJ2 48 49 30 340 ≤ 4919521211867 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_500 c22240R_48_10 (by norm_num)

theorem c22240R_48_8 : rowsJ2 48 49 29 340 ≤ 5173070192534 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_499 c22240R_48_9 (by norm_num)

theorem c22240R_48_7 : rowsJ2 48 49 28 340 ≤ 5445517540849 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_498 c22240R_48_8 (by norm_num)

theorem c22240R_48_6 : rowsJ2 48 49 27 340 ≤ 5745538060596 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_497 c22240R_48_7 (by norm_num)

theorem c22240R_48_5 : rowsJ2 48 49 26 340 ≤ 6084899343816 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_496 c22240R_48_6 (by norm_num)

theorem c22240R_48_4 : rowsJ2 48 49 24 340 ≤ 6896926455272 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_495 c22240R_48_5 (by norm_num)

theorem c22240R_48_3 : rowsJ2 48 49 21 340 ≤ 8505648724276 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_494 c22240R_48_4 (by norm_num)

theorem c22240R_48_2 : rowsJ2 48 49 18 340 ≤ 10553595791168 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_493 c22240R_48_3 (by norm_num)

theorem c22240R_48_1 : rowsJ2 48 49 14 340 ≤ 13354131634432 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_492 c22240R_48_2 (by norm_num)

theorem c22240R_48_0 : rowsJ2 48 49 0 340 ≤ 14827653760503 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22240R_491 c22240R_48_1 (by norm_num)

theorem hr22240R_48 : rows2 48 49 ≤ 14827653760503 := rows2_le_of_rowsJ2 48 49 c22240R_48_0

theorem c22240R_49_27 : rowsJ2 49 50 48 340 ≤ 4613371866122 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_546 rows22240R_547 (by norm_num)

theorem c22240R_49_26 : rowsJ2 49 50 47 340 ≤ 5563903656219 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_545 c22240R_49_27 (by norm_num)

theorem c22240R_49_25 : rowsJ2 49 50 46 340 ≤ 6010086867579 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_544 c22240R_49_26 (by norm_num)

theorem c22240R_49_24 : rowsJ2 49 50 45 340 ≤ 6240140452136 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_543 c22240R_49_25 (by norm_num)

theorem c22240R_49_23 : rowsJ2 49 50 44 340 ≤ 6320704642706 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_542 c22240R_49_24 (by norm_num)

theorem c22240R_49_22 : rowsJ2 49 50 43 340 ≤ 6323881820216 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_541 c22240R_49_23 (by norm_num)

theorem c22240R_49_21 : rowsJ2 49 50 42 340 ≤ 6327687856234 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_540 c22240R_49_22 (by norm_num)

theorem c22240R_49_20 : rowsJ2 49 50 41 340 ≤ 6336084929993 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_539 c22240R_49_21 (by norm_num)

theorem c22240R_49_19 : rowsJ2 49 50 40 340 ≤ 6349087159312 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_538 c22240R_49_20 (by norm_num)

theorem c22240R_49_18 : rowsJ2 49 50 39 340 ≤ 6372373505143 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_537 c22240R_49_19 (by norm_num)

theorem c22240R_49_17 : rowsJ2 49 50 38 340 ≤ 6405994351681 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_536 c22240R_49_18 (by norm_num)

theorem c22240R_49_16 : rowsJ2 49 50 37 340 ≤ 6454911784444 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_535 c22240R_49_17 (by norm_num)

theorem c22240R_49_15 : rowsJ2 49 50 36 340 ≤ 6519220404089 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_534 c22240R_49_16 (by norm_num)

theorem c22240R_49_14 : rowsJ2 49 50 35 340 ≤ 6603865130159 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_533 c22240R_49_15 (by norm_num)

theorem c22240R_49_13 : rowsJ2 49 50 34 340 ≤ 6708998283905 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_532 c22240R_49_14 (by norm_num)

theorem c22240R_49_12 : rowsJ2 49 50 33 340 ≤ 6838311577834 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_531 c22240R_49_13 (by norm_num)

theorem c22240R_49_11 : rowsJ2 49 50 32 340 ≤ 6990141936542 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_530 c22240R_49_12 (by norm_num)

theorem c22240R_49_10 : rowsJ2 49 50 31 340 ≤ 7169884371816 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_529 c22240R_49_11 (by norm_num)

theorem c22240R_49_9 : rowsJ2 49 50 30 340 ≤ 7371408268657 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_528 c22240R_49_10 (by norm_num)

theorem c22240R_49_8 : rowsJ2 49 50 29 340 ≤ 7595291764536 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_527 c22240R_49_9 (by norm_num)

theorem c22240R_49_7 : rowsJ2 49 50 28 340 ≤ 7832422541487 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_526 c22240R_49_8 (by norm_num)

theorem c22240R_49_6 : rowsJ2 49 50 27 340 ≤ 8096956788718 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_525 c22240R_49_7 (by norm_num)

theorem c22240R_49_5 : rowsJ2 49 50 26 340 ≤ 8395003118738 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_524 c22240R_49_6 (by norm_num)

theorem c22240R_49_4 : rowsJ2 49 50 24 340 ≤ 9117821282386 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_523 c22240R_49_5 (by norm_num)

theorem c22240R_49_3 : rowsJ2 49 50 21 340 ≤ 10570075579219 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_522 c22240R_49_4 (by norm_num)

theorem c22240R_49_2 : rowsJ2 49 50 18 340 ≤ 12467768573515 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_521 c22240R_49_3 (by norm_num)

theorem c22240R_49_1 : rowsJ2 49 50 14 340 ≤ 15168042863631 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_520 c22240R_49_2 (by norm_num)

theorem c22240R_49_0 : rowsJ2 49 50 0 340 ≤ 16738602643534 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22240R_519 c22240R_49_1 (by norm_num)

theorem hr22240R_49 : rows2 49 50 ≤ 16738602643534 := rows2_le_of_rowsJ2 49 50 c22240R_49_0

theorem c22240R_50_29 : rowsJ2 50 51 49 340 ≤ 6548809606069 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_577 rows22240R_578 (by norm_num)

theorem c22240R_50_28 : rowsJ2 50 51 48 340 ≤ 8344796221630 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_576 c22240R_50_29 (by norm_num)

theorem c22240R_50_27 : rowsJ2 50 51 47 340 ≤ 9284857381723 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_575 c22240R_50_28 (by norm_num)

theorem c22240R_50_26 : rowsJ2 50 51 46 340 ≤ 9725791487961 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_574 c22240R_50_27 (by norm_num)

theorem c22240R_50_25 : rowsJ2 50 51 45 340 ≤ 9952205295200 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_573 c22240R_50_26 (by norm_num)

theorem c22240R_50_24 : rowsJ2 50 51 44 340 ≤ 10030681115238 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_572 c22240R_50_25 (by norm_num)

theorem c22240R_50_23 : rowsJ2 50 51 43 340 ≤ 10031949822231 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_571 c22240R_50_24 (by norm_num)

theorem c22240R_50_22 : rowsJ2 50 51 42 340 ≤ 10033846576002 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_570 c22240R_50_23 (by norm_num)

theorem c22240R_50_21 : rowsJ2 50 51 41 340 ≤ 10035737810682 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_569 c22240R_50_22 (by norm_num)

theorem c22240R_50_20 : rowsJ2 50 51 40 340 ≤ 10042230847508 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_568 c22240R_50_21 (by norm_num)

theorem c22240R_50_19 : rowsJ2 50 51 39 340 ≤ 10052704891060 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_567 c22240R_50_20 (by norm_num)

theorem c22240R_50_18 : rowsJ2 50 51 38 340 ≤ 10073484291371 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_566 c22240R_50_19 (by norm_num)

theorem c22240R_50_17 : rowsJ2 50 51 37 340 ≤ 10103314963750 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_565 c22240R_50_18 (by norm_num)

theorem c22240R_50_16 : rowsJ2 50 51 36 340 ≤ 10148478523373 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_564 c22240R_50_17 (by norm_num)

theorem c22240R_50_15 : rowsJ2 50 51 35 340 ≤ 10207771552277 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_563 c22240R_50_16 (by norm_num)

theorem c22240R_50_14 : rowsJ2 50 51 34 340 ≤ 10287455526415 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_562 c22240R_50_15 (by norm_num)

theorem c22240R_50_13 : rowsJ2 50 51 33 340 ≤ 10385762870543 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_561 c22240R_50_14 (by norm_num)

theorem c22240R_50_12 : rowsJ2 50 51 32 340 ≤ 10507702824839 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_560 c22240R_50_13 (by norm_num)

theorem c22240R_50_11 : rowsJ2 50 51 31 340 ≤ 10651582476080 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_559 c22240R_50_12 (by norm_num)

theorem c22240R_50_10 : rowsJ2 50 51 30 340 ≤ 10821844823807 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_558 c22240R_50_11 (by norm_num)

theorem c22240R_50_9 : rowsJ2 50 51 29 340 ≤ 11011063370690 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_557 c22240R_50_10 (by norm_num)

theorem c22240R_50_8 : rowsJ2 50 51 28 340 ≤ 11218647333047 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_556 c22240R_50_9 (by norm_num)

theorem c22240R_50_7 : rowsJ2 50 51 27 340 ≤ 11447875989526 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_555 c22240R_50_8 (by norm_num)

theorem c22240R_50_6 : rowsJ2 50 51 26 340 ≤ 11710382937348 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_554 c22240R_50_7 (by norm_num)

theorem c22240R_50_5 : rowsJ2 50 51 25 340 ≤ 12008874264455 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_553 c22240R_50_6 (by norm_num)

theorem c22240R_50_4 : rowsJ2 50 51 24 340 ≤ 12350025328132 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_552 c22240R_50_5 (by norm_num)

theorem c22240R_50_3 : rowsJ2 50 51 22 340 ≤ 13168262491767 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_551 c22240R_50_4 (by norm_num)

theorem c22240R_50_2 : rowsJ2 50 51 18 340 ≤ 15405751517927 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_550 c22240R_50_3 (by norm_num)

theorem c22240R_50_1 : rowsJ2 50 51 14 340 ≤ 17994509536037 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_549 c22240R_50_2 (by norm_num)

theorem c22240R_50_0 : rowsJ2 50 51 0 340 ≤ 19651869919003 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22240R_548 c22240R_50_1 (by norm_num)

theorem hr22240R_50 : rows2 50 51 ≤ 19651869919003 := rows2_le_of_rowsJ2 50 51 c22240R_50_0

theorem c22240R_51_30 : rowsJ2 51 52 50 340 ≤ 8661961731577 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_609 rows22240R_610 (by norm_num)

theorem c22240R_51_29 : rowsJ2 51 52 49 340 ≤ 11403242629547 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_608 c22240R_51_30 (by norm_num)

theorem c22240R_51_28 : rowsJ2 51 52 48 340 ≤ 13180835109828 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_607 c22240R_51_29 (by norm_num)

theorem c22240R_51_27 : rowsJ2 51 52 47 340 ≤ 14111268351763 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_606 c22240R_51_28 (by norm_num)

theorem c22240R_51_26 : rowsJ2 51 52 46 340 ≤ 14547051487421 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_605 c22240R_51_27 (by norm_num)

theorem c22240R_51_25 : rowsJ2 51 52 45 340 ≤ 14770513959527 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_604 c22240R_51_26 (by norm_num)

theorem c22240R_51_24 : rowsJ2 51 52 44 340 ≤ 14846925959954 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_603 c22240R_51_25 (by norm_num)

theorem c22240R_51_23 : rowsJ2 51 52 43 340 ≤ 14846925959954 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_602 c22240R_51_24 (by norm_num)

theorem c22240R_51_22 : rowsJ2 51 52 42 340 ≤ 14846925959954 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_601 c22240R_51_23 (by norm_num)

theorem c22240R_51_21 : rowsJ2 51 52 41 340 ≤ 14846925959954 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_600 c22240R_51_22 (by norm_num)

theorem c22240R_51_20 : rowsJ2 51 52 40 340 ≤ 14846925959954 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_599 c22240R_51_21 (by norm_num)

theorem c22240R_51_19 : rowsJ2 51 52 39 340 ≤ 14850909695702 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_598 c22240R_51_20 (by norm_num)

theorem c22240R_51_18 : rowsJ2 51 52 38 340 ≤ 14858886681702 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_597 c22240R_51_19 (by norm_num)

theorem c22240R_51_17 : rowsJ2 51 52 37 340 ≤ 14875898399755 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_596 c22240R_51_18 (by norm_num)

theorem c22240R_51_16 : rowsJ2 51 52 36 340 ≤ 14901986588894 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_595 c22240R_51_17 (by norm_num)

theorem c22240R_51_15 : rowsJ2 51 52 35 340 ≤ 14942157965063 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_594 c22240R_51_16 (by norm_num)

theorem c22240R_51_14 : rowsJ2 51 52 34 340 ≤ 14996500278470 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_593 c22240R_51_15 (by norm_num)

theorem c22240R_51_13 : rowsJ2 51 52 33 340 ≤ 15069386230269 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_592 c22240R_51_14 (by norm_num)

theorem c22240R_51_12 : rowsJ2 51 52 32 340 ≤ 15160956595596 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_591 c22240R_51_13 (by norm_num)

theorem c22240R_51_11 : rowsJ2 51 52 31 340 ≤ 15275586791765 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_590 c22240R_51_12 (by norm_num)

theorem c22240R_51_10 : rowsJ2 51 52 30 340 ≤ 15412372956553 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_589 c22240R_51_11 (by norm_num)

theorem c22240R_51_9 : rowsJ2 51 52 29 340 ≤ 15572752326988 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_588 c22240R_51_10 (by norm_num)

theorem c22240R_51_8 : rowsJ2 51 52 28 340 ≤ 15750916201679 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_587 c22240R_51_9 (by norm_num)

theorem c22240R_51_7 : rowsJ2 51 52 27 340 ≤ 15950617433129 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_586 c22240R_51_8 (by norm_num)

theorem c22240R_51_6 : rowsJ2 51 52 26 340 ≤ 16177757372312 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_585 c22240R_51_7 (by norm_num)

theorem c22240R_51_5 : rowsJ2 51 52 25 340 ≤ 16440620338882 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_584 c22240R_51_6 (by norm_num)

theorem c22240R_51_4 : rowsJ2 51 52 24 340 ≤ 16740236994275 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_583 c22240R_51_5 (by norm_num)

theorem c22240R_51_3 : rowsJ2 51 52 22 340 ≤ 17468740518117 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_582 c22240R_51_4 (by norm_num)

theorem c22240R_51_2 : rowsJ2 51 52 19 340 ≤ 18930357390743 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_581 c22240R_51_3 (by norm_num)

theorem c22240R_51_1 : rowsJ2 51 52 15 340 ≤ 21380789087907 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_580 c22240R_51_2 (by norm_num)

theorem c22240R_51_0 : rowsJ2 51 52 0 340 ≤ 23718086151404 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22240R_579 c22240R_51_1 (by norm_num)

theorem hr22240R_51 : rows2 51 52 ≤ 23718086151404 := rows2_le_of_rowsJ2 51 52 c22240R_51_0

theorem c22240R_52_31 : rowsJ2 52 53 51 340 ≤ 11239020301899 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_642 rows22240R_643 (by norm_num)

theorem c22240R_52_30 : rowsJ2 52 53 50 340 ≤ 14941556796385 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_641 c22240R_52_31 (by norm_num)

theorem c22240R_52_29 : rowsJ2 52 53 49 340 ≤ 17655046689163 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_640 c22240R_52_30 (by norm_num)

theorem c22240R_52_28 : rowsJ2 52 53 48 340 ≤ 19414618002084 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_639 c22240R_52_29 (by norm_num)

theorem c22240R_52_27 : rowsJ2 52 53 47 340 ≤ 20335618545940 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_638 c22240R_52_28 (by norm_num)

theorem c22240R_52_26 : rowsJ2 52 53 46 340 ≤ 20766983728153 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_637 c22240R_52_27 (by norm_num)

theorem c22240R_52_25 : rowsJ2 52 53 45 340 ≤ 20988180745913 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_636 c22240R_52_26 (by norm_num)

theorem c22240R_52_24 : rowsJ2 52 53 44 340 ≤ 21063818084282 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_635 c22240R_52_25 (by norm_num)

theorem c22240R_52_23 : rowsJ2 52 53 43 340 ≤ 21063818084282 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_634 c22240R_52_24 (by norm_num)

theorem c22240R_52_22 : rowsJ2 52 53 42 340 ≤ 21063818084282 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_633 c22240R_52_23 (by norm_num)

theorem c22240R_52_21 : rowsJ2 52 53 41 340 ≤ 21063818084282 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_632 c22240R_52_22 (by norm_num)

theorem c22240R_52_20 : rowsJ2 52 53 40 340 ≤ 21063818084282 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_631 c22240R_52_21 (by norm_num)

theorem c22240R_52_19 : rowsJ2 52 53 39 340 ≤ 21063818084282 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_630 c22240R_52_20 (by norm_num)

theorem c22240R_52_18 : rowsJ2 52 53 38 340 ≤ 21067808023624 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_629 c22240R_52_19 (by norm_num)

theorem c22240R_52_17 : rowsJ2 52 53 37 340 ≤ 21075798547131 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_628 c22240R_52_18 (by norm_num)

theorem c22240R_52_16 : rowsJ2 52 53 36 340 ≤ 21092841571777 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_627 c22240R_52_17 (by norm_num)

theorem c22240R_52_15 : rowsJ2 52 53 35 340 ≤ 21118981598936 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_626 c22240R_52_16 (by norm_num)

theorem c22240R_52_14 : rowsJ2 52 53 34 340 ≤ 21159238837590 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_625 c22240R_52_15 (by norm_num)

theorem c22240R_52_13 : rowsJ2 52 53 33 340 ≤ 21213091099462 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_624 c22240R_52_14 (by norm_num)

theorem c22240R_52_12 : rowsJ2 52 53 32 340 ≤ 21285541887624 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_623 c22240R_52_13 (by norm_num)

theorem c22240R_52_11 : rowsJ2 52 53 31 340 ≤ 21376125425232 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_622 c22240R_52_12 (by norm_num)

theorem c22240R_52_10 : rowsJ2 52 53 30 340 ≤ 21489849077776 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_621 c22240R_52_11 (by norm_num)

theorem c22240R_52_9 : rowsJ2 52 53 29 340 ≤ 21622383732524 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_620 c22240R_52_10 (by norm_num)

theorem c22240R_52_8 : rowsJ2 52 53 28 340 ≤ 21776924056690 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_619 c22240R_52_9 (by norm_num)

theorem c22240R_52_7 : rowsJ2 52 53 27 340 ≤ 21947216479575 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_618 c22240R_52_8 (by norm_num)

theorem c22240R_52_6 : rowsJ2 52 53 26 340 ≤ 22144779128305 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_617 c22240R_52_7 (by norm_num)

theorem c22240R_52_5 : rowsJ2 52 53 25 340 ≤ 22372178486917 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_616 c22240R_52_6 (by norm_num)

theorem c22240R_52_4 : rowsJ2 52 53 24 340 ≤ 22636060142114 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_615 c22240R_52_5 (by norm_num)

theorem c22240R_52_3 : rowsJ2 52 53 22 340 ≤ 23280871294727 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_614 c22240R_52_4 (by norm_num)

theorem c22240R_52_2 : rowsJ2 52 53 19 340 ≤ 24595092224260 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_613 c22240R_52_3 (by norm_num)

theorem c22240R_52_1 : rowsJ2 52 53 15 340 ≤ 26889576128766 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_612 c22240R_52_2 (by norm_num)

theorem c22240R_52_0 : rowsJ2 52 53 0 340 ≤ 29286802159606 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22240R_611 c22240R_52_1 (by norm_num)

theorem hr22240R_52 : rows2 52 53 ≤ 29286802159606 := rows2_le_of_rowsJ2 52 53 c22240R_52_0

theorem c22240R_53_31 : rowsJ2 53 54 52 340 ≤ 14105772406427 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_675 rows22240R_676 (by norm_num)

theorem c22240R_53_30 : rowsJ2 53 54 51 340 ≤ 18928490479744 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_674 c22240R_53_31 (by norm_num)

theorem c22240R_53_29 : rowsJ2 53 54 50 340 ≤ 22593867535447 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_673 c22240R_53_30 (by norm_num)

theorem c22240R_53_28 : rowsJ2 53 54 49 340 ≤ 25280124270169 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_672 c22240R_53_29 (by norm_num)

theorem c22240R_53_27 : rowsJ2 53 54 48 340 ≤ 27022036153508 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_671 c22240R_53_28 (by norm_num)

theorem c22240R_53_26 : rowsJ2 53 54 47 340 ≤ 27933793341253 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_670 c22240R_53_27 (by norm_num)

theorem c22240R_53_25 : rowsJ2 53 54 46 340 ≤ 28360829251331 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_669 c22240R_53_26 (by norm_num)

theorem c22240R_53_24 : rowsJ2 53 54 45 340 ≤ 28579806289072 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_668 c22240R_53_25 (by norm_num)

theorem c22240R_53_23 : rowsJ2 53 54 44 340 ≤ 28654684515128 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_667 c22240R_53_24 (by norm_num)

theorem c22240R_53_22 : rowsJ2 53 54 43 340 ≤ 28654684515128 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_666 c22240R_53_23 (by norm_num)

theorem c22240R_53_21 : rowsJ2 53 54 42 340 ≤ 28654684515128 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_665 c22240R_53_22 (by norm_num)

theorem c22240R_53_20 : rowsJ2 53 54 41 340 ≤ 28654684515128 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_664 c22240R_53_21 (by norm_num)

theorem c22240R_53_19 : rowsJ2 53 54 40 340 ≤ 28654684515128 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_663 c22240R_53_20 (by norm_num)

theorem c22240R_53_18 : rowsJ2 53 54 39 340 ≤ 28654684515128 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_662 c22240R_53_19 (by norm_num)

theorem c22240R_53_17 : rowsJ2 53 54 38 340 ≤ 28654684515128 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_661 c22240R_53_18 (by norm_num)

theorem c22240R_53_16 : rowsJ2 53 54 37 340 ≤ 28658681636517 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_660 c22240R_53_17 (by norm_num)

theorem c22240R_53_15 : rowsJ2 53 54 36 340 ≤ 28666687687842 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_659 c22240R_53_16 (by norm_num)

theorem c22240R_53_14 : rowsJ2 53 54 35 340 ≤ 28683766332896 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_658 c22240R_53_15 (by norm_num)

theorem c22240R_53_13 : rowsJ2 53 54 34 340 ≤ 28709964924654 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_657 c22240R_53_14 (by norm_num)

theorem c22240R_53_12 : rowsJ2 53 54 33 340 ≤ 28749710150781 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_656 c22240R_53_13 (by norm_num)

theorem c22240R_53_11 : rowsJ2 53 54 32 340 ≤ 28803092332098 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_655 c22240R_53_12 (by norm_num)

theorem c22240R_53_10 : rowsJ2 53 54 31 340 ≤ 28874526127777 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_654 c22240R_53_11 (by norm_num)

theorem c22240R_53_9 : rowsJ2 53 54 30 340 ≤ 28964157948217 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_653 c22240R_53_10 (by norm_num)

theorem c22240R_53_8 : rowsJ2 53 54 29 340 ≤ 29074722091519 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_652 c22240R_53_9 (by norm_num)

theorem c22240R_53_7 : rowsJ2 53 54 28 340 ≤ 29202508368170 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_651 c22240R_53_8 (by norm_num)

theorem c22240R_53_6 : rowsJ2 53 54 27 340 ≤ 29349200025289 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_650 c22240R_53_7 (by norm_num)

theorem c22240R_53_5 : rowsJ2 53 54 26 340 ≤ 29517297267187 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_649 c22240R_53_6 (by norm_num)

theorem c22240R_53_4 : rowsJ2 53 54 25 340 ≤ 29715036666831 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_648 c22240R_53_5 (by norm_num)

theorem c22240R_53_3 : rowsJ2 53 54 23 340 ≤ 30208325380537 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_647 c22240R_53_4 (by norm_num)

theorem c22240R_53_2 : rowsJ2 53 54 20 340 ≤ 31245640969133 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_646 c22240R_53_3 (by norm_num)

theorem c22240R_53_1 : rowsJ2 53 54 15 340 ≤ 33820338985372 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_645 c22240R_53_2 (by norm_num)

theorem c22240R_53_0 : rowsJ2 53 54 0 340 ≤ 36262118343369 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22240R_644 c22240R_53_1 (by norm_num)

theorem hr22240R_53 : rows2 53 54 ≤ 36262118343369 := rows2_le_of_rowsJ2 53 54 c22240R_53_0

theorem c22240R_54_32 : rowsJ2 54 55 53 340 ≤ 16946528047635 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_709 rows22240R_710 (by norm_num)

theorem c22240R_54_31 : rowsJ2 54 55 52 340 ≤ 23187398430610 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_708 c22240R_54_32 (by norm_num)

theorem c22240R_54_30 : rowsJ2 54 55 51 340 ≤ 27962195654064 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_707 c22240R_54_31 (by norm_num)

theorem c22240R_54_29 : rowsJ2 54 55 50 340 ≤ 31591151757740 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_706 c22240R_54_30 (by norm_num)

theorem c22240R_54_28 : rowsJ2 54 55 49 340 ≤ 34250716551586 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_705 c22240R_54_29 (by norm_num)

theorem c22240R_54_27 : rowsJ2 54 55 48 340 ≤ 35975319959382 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_704 c22240R_54_28 (by norm_num)

theorem c22240R_54_26 : rowsJ2 54 55 47 340 ≤ 36878017488521 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_703 c22240R_54_27 (by norm_num)

theorem c22240R_54_25 : rowsJ2 54 55 46 340 ≤ 37300810164094 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_702 c22240R_54_26 (by norm_num)

theorem c22240R_54_24 : rowsJ2 54 55 45 340 ≤ 37517611340508 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_701 c22240R_54_25 (by norm_num)

theorem c22240R_54_23 : rowsJ2 54 55 44 340 ≤ 37591745540441 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_700 c22240R_54_24 (by norm_num)

theorem c22240R_54_22 : rowsJ2 54 55 43 340 ≤ 37591745540441 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_699 c22240R_54_23 (by norm_num)

theorem c22240R_54_21 : rowsJ2 54 55 42 340 ≤ 37591745540441 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_698 c22240R_54_22 (by norm_num)

theorem c22240R_54_20 : rowsJ2 54 55 41 340 ≤ 37591745540441 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_697 c22240R_54_21 (by norm_num)

theorem c22240R_54_19 : rowsJ2 54 55 40 340 ≤ 37591745540441 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_696 c22240R_54_20 (by norm_num)

theorem c22240R_54_18 : rowsJ2 54 55 39 340 ≤ 37591745540441 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_695 c22240R_54_19 (by norm_num)

theorem c22240R_54_17 : rowsJ2 54 55 38 340 ≤ 37591745540441 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_694 c22240R_54_18 (by norm_num)

theorem c22240R_54_16 : rowsJ2 54 55 37 340 ≤ 37591745540441 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_693 c22240R_54_17 (by norm_num)

theorem c22240R_54_15 : rowsJ2 54 55 36 340 ≤ 37595750832807 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_692 c22240R_54_16 (by norm_num)

theorem c22240R_54_14 : rowsJ2 54 55 35 340 ≤ 37603774425228 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_691 c22240R_54_15 (by norm_num)

theorem c22240R_54_13 : rowsJ2 54 55 34 340 ≤ 37620893057964 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_690 c22240R_54_14 (by norm_num)

theorem c22240R_54_12 : rowsJ2 54 55 33 340 ≤ 37646554663616 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_689 c22240R_54_13 (by norm_num)

theorem c22240R_54_11 : rowsJ2 54 55 32 340 ≤ 37685803849584 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_688 c22240R_54_12 (by norm_num)

theorem c22240R_54_10 : rowsJ2 54 55 31 340 ≤ 37738134722376 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_687 c22240R_54_11 (by norm_num)

theorem c22240R_54_9 : rowsJ2 54 55 30 340 ≤ 37808580893142 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_686 c22240R_54_10 (by norm_num)

theorem c22240R_54_8 : rowsJ2 54 55 29 340 ≤ 37896129638399 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_685 c22240R_54_9 (by norm_num)

theorem c22240R_54_7 : rowsJ2 54 55 28 340 ≤ 38003041533014 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_684 c22240R_54_8 (by norm_num)

theorem c22240R_54_6 : rowsJ2 54 55 27 340 ≤ 38126200719139 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_683 c22240R_54_7 (by norm_num)

theorem c22240R_54_5 : rowsJ2 54 55 26 340 ≤ 38270655128802 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_682 c22240R_54_6 (by norm_num)

theorem c22240R_54_4 : rowsJ2 54 55 25 340 ≤ 38438840325108 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_681 c22240R_54_5 (by norm_num)

theorem c22240R_54_3 : rowsJ2 54 55 23 340 ≤ 38866667887038 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_680 c22240R_54_4 (by norm_num)

theorem c22240R_54_2 : rowsJ2 54 55 20 340 ≤ 39783676188371 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_679 c22240R_54_3 (by norm_num)

theorem c22240R_54_1 : rowsJ2 54 55 15 340 ≤ 42148060119481 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_678 c22240R_54_2 (by norm_num)

theorem c22240R_54_0 : rowsJ2 54 55 0 340 ≤ 44624147715212 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22240R_677 c22240R_54_1 (by norm_num)

theorem hr22240R_54 : rows2 54 55 ≤ 44624147715212 := rows2_le_of_rowsJ2 54 55 c22240R_54_0

theorem c22240R_55_33 : rowsJ2 55 56 54 340 ≤ 19900665466566 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_744 rows22240R_745 (by norm_num)

theorem c22240R_55_32 : rowsJ2 55 56 53 340 ≤ 27549404225290 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_743 c22240R_55_33 (by norm_num)

theorem c22240R_55_31 : rowsJ2 55 56 52 340 ≤ 33728872465318 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_742 c22240R_55_32 (by norm_num)

theorem c22240R_55_30 : rowsJ2 55 56 51 340 ≤ 38456691821319 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_741 c22240R_55_31 (by norm_num)

theorem c22240R_55_29 : rowsJ2 55 56 50 340 ≤ 42049943661370 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_740 c22240R_55_30 (by norm_num)

theorem c22240R_55_28 : rowsJ2 55 56 49 340 ≤ 44683341756085 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_739 c22240R_55_29 (by norm_num)

theorem c22240R_55_27 : rowsJ2 55 56 48 340 ≤ 46390977283044 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_738 c22240R_55_28 (by norm_num)

theorem c22240R_55_26 : rowsJ2 55 56 47 340 ≤ 47284793428766 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_737 c22240R_55_27 (by norm_num)

theorem c22240R_55_25 : rowsJ2 55 56 46 340 ≤ 47703426367843 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_736 c22240R_55_26 (by norm_num)

theorem c22240R_55_24 : rowsJ2 55 56 45 340 ≤ 47918094499343 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_735 c22240R_55_25 (by norm_num)

theorem c22240R_55_23 : rowsJ2 55 56 44 340 ≤ 47991499314037 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_734 c22240R_55_24 (by norm_num)

theorem c22240R_55_22 : rowsJ2 55 56 43 340 ≤ 47991499314037 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_733 c22240R_55_23 (by norm_num)

theorem c22240R_55_21 : rowsJ2 55 56 42 340 ≤ 47991499314037 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_732 c22240R_55_22 (by norm_num)

theorem c22240R_55_20 : rowsJ2 55 56 41 340 ≤ 47991499314037 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_731 c22240R_55_21 (by norm_num)

theorem c22240R_55_19 : rowsJ2 55 56 40 340 ≤ 47991499314037 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_730 c22240R_55_20 (by norm_num)

theorem c22240R_55_18 : rowsJ2 55 56 39 340 ≤ 47991499314037 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_729 c22240R_55_19 (by norm_num)

theorem c22240R_55_17 : rowsJ2 55 56 38 340 ≤ 47991499314037 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_728 c22240R_55_18 (by norm_num)

theorem c22240R_55_16 : rowsJ2 55 56 37 340 ≤ 47991499314037 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_727 c22240R_55_17 (by norm_num)

theorem c22240R_55_15 : rowsJ2 55 56 36 340 ≤ 47991499314037 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_726 c22240R_55_16 (by norm_num)

theorem c22240R_55_14 : rowsJ2 55 56 35 340 ≤ 47995513778300 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_725 c22240R_55_15 (by norm_num)

theorem c22240R_55_13 : rowsJ2 55 56 34 340 ≤ 48003556951210 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_724 c22240R_55_14 (by norm_num)

theorem c22240R_55_12 : rowsJ2 55 56 33 340 ≤ 48020123559352 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_723 c22240R_55_13 (by norm_num)

theorem c22240R_55_11 : rowsJ2 55 56 32 340 ≤ 48045260210389 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_722 c22240R_55_12 (by norm_num)

theorem c22240R_55_10 : rowsJ2 55 56 31 340 ≤ 48083434000572 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_721 c22240R_55_11 (by norm_num)

theorem c22240R_55_9 : rowsJ2 55 56 30 340 ≤ 48134737274464 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_720 c22240R_55_10 (by norm_num)

theorem c22240R_55_8 : rowsJ2 55 56 29 340 ≤ 48203070129994 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_719 c22240R_55_9 (by norm_num)

theorem c22240R_55_7 : rowsJ2 55 56 28 340 ≤ 48288047078287 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_718 c22240R_55_8 (by norm_num)

theorem c22240R_55_6 : rowsJ2 55 56 27 340 ≤ 48391427183772 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_717 c22240R_55_7 (by norm_num)

theorem c22240R_55_5 : rowsJ2 55 56 26 340 ≤ 48512301749054 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_716 c22240R_55_6 (by norm_num)

theorem c22240R_55_4 : rowsJ2 55 56 25 340 ≤ 48656772162175 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_715 c22240R_55_5 (by norm_num)

theorem c22240R_55_3 : rowsJ2 55 56 23 340 ≤ 49025075957919 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_714 c22240R_55_4 (by norm_num)

theorem c22240R_55_2 : rowsJ2 55 56 20 340 ≤ 49827963424145 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_713 c22240R_55_3 (by norm_num)

theorem c22240R_55_1 : rowsJ2 55 56 15 340 ≤ 51985651882383 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_712 c22240R_55_2 (by norm_num)

theorem c22240R_55_0 : rowsJ2 55 56 0 340 ≤ 54481580875919 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22240R_711 c22240R_55_1 (by norm_num)

theorem hr22240R_55 : rows2 55 56 ≤ 54481580875919 := rows2_le_of_rowsJ2 55 56 c22240R_55_0

theorem c22240R_56_34 : rowsJ2 56 57 55 340 ≤ 22932675057264 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_780 rows22240R_781 (by norm_num)

theorem c22240R_56_33 : rowsJ2 56 57 54 340 ≤ 31974769744971 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_779 c22240R_56_34 (by norm_num)

theorem c22240R_56_32 : rowsJ2 56 57 53 340 ≤ 39548987967299 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_778 c22240R_56_33 (by norm_num)

theorem c22240R_56_31 : rowsJ2 56 57 52 340 ≤ 45668250557427 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_777 c22240R_56_32 (by norm_num)

theorem c22240R_56_30 : rowsJ2 56 57 51 340 ≤ 50350007465028 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_776 c22240R_56_31 (by norm_num)

theorem c22240R_56_29 : rowsJ2 56 57 50 340 ≤ 53908250781066 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_775 c22240R_56_30 (by norm_num)

theorem c22240R_56_28 : rowsJ2 56 57 49 340 ≤ 56515992065583 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_774 c22240R_56_29 (by norm_num)

theorem c22240R_56_27 : rowsJ2 56 57 48 340 ≤ 58206990350842 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_773 c22240R_56_28 (by norm_num)

theorem c22240R_56_26 : rowsJ2 56 57 47 340 ≤ 59092098177360 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_772 c22240R_56_27 (by norm_num)

theorem c22240R_56_25 : rowsJ2 56 57 46 340 ≤ 59506652437303 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_771 c22240R_56_26 (by norm_num)

theorem c22240R_56_24 : rowsJ2 56 57 45 340 ≤ 59719229088782 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_770 c22240R_56_25 (by norm_num)

theorem c22240R_56_23 : rowsJ2 56 57 44 340 ≤ 59791918731166 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_769 c22240R_56_24 (by norm_num)

theorem c22240R_56_22 : rowsJ2 56 57 43 340 ≤ 59791918731166 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_768 c22240R_56_23 (by norm_num)

theorem c22240R_56_21 : rowsJ2 56 57 42 340 ≤ 59791918731166 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_767 c22240R_56_22 (by norm_num)

theorem c22240R_56_20 : rowsJ2 56 57 41 340 ≤ 59791918731166 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_766 c22240R_56_21 (by norm_num)

theorem c22240R_56_19 : rowsJ2 56 57 40 340 ≤ 59791918731166 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_765 c22240R_56_20 (by norm_num)

theorem c22240R_56_18 : rowsJ2 56 57 39 340 ≤ 59791918731166 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_764 c22240R_56_19 (by norm_num)

theorem c22240R_56_17 : rowsJ2 56 57 38 340 ≤ 59791918731166 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_763 c22240R_56_18 (by norm_num)

theorem c22240R_56_16 : rowsJ2 56 57 37 340 ≤ 59791918731166 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_762 c22240R_56_17 (by norm_num)

theorem c22240R_56_15 : rowsJ2 56 57 36 340 ≤ 59791918731166 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_761 c22240R_56_16 (by norm_num)

theorem c22240R_56_14 : rowsJ2 56 57 35 340 ≤ 59791918731166 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_760 c22240R_56_15 (by norm_num)

theorem c22240R_56_13 : rowsJ2 56 57 34 340 ≤ 59795943381790 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_759 c22240R_56_14 (by norm_num)

theorem c22240R_56_12 : rowsJ2 56 57 33 340 ≤ 59804008203929 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_758 c22240R_56_13 (by norm_num)

theorem c22240R_56_11 : rowsJ2 56 57 32 340 ≤ 59820622022987 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_757 c22240R_56_12 (by norm_num)

theorem c22240R_56_10 : rowsJ2 56 57 31 340 ≤ 59845834384953 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_756 c22240R_56_11 (by norm_num)

theorem c22240R_56_9 : rowsJ2 56 57 30 340 ≤ 59884129507376 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_755 c22240R_56_10 (by norm_num)

theorem c22240R_56_8 : rowsJ2 56 57 29 340 ≤ 59935049843619 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_754 c22240R_56_9 (by norm_num)

theorem c22240R_56_7 : rowsJ2 56 57 28 340 ≤ 60003069200369 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_753 c22240R_56_8 (by norm_num)

theorem c22240R_56_6 : rowsJ2 56 57 27 340 ≤ 60086181738038 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_752 c22240R_56_7 (by norm_num)

theorem c22240R_56_5 : rowsJ2 56 57 26 340 ≤ 60187239060112 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_751 c22240R_56_6 (by norm_num)

theorem c22240R_56_4 : rowsJ2 56 57 25 340 ≤ 60308052905713 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_750 c22240R_56_5 (by norm_num)

theorem c22240R_56_3 : rowsJ2 56 57 23 340 ≤ 60622785278614 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_749 c22240R_56_4 (by norm_num)

theorem c22240R_56_2 : rowsJ2 56 57 20 340 ≤ 61323417097577 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_748 c22240R_56_3 (by norm_num)

theorem c22240R_56_1 : rowsJ2 56 57 15 340 ≤ 63275898757616 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_747 c22240R_56_2 (by norm_num)

theorem c22240R_56_0 : rowsJ2 56 57 0 340 ≤ 65778383981261 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22240R_746 c22240R_56_1 (by norm_num)

theorem hr22240R_56 : rows2 56 57 ≤ 65778383981261 := rows2_le_of_rowsJ2 56 57 c22240R_56_0

theorem c22240R_57_36 : rowsJ2 57 58 56 340 ≤ 25513362862092 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_818 rows22240R_819 (by norm_num)

theorem c22240R_57_35 : rowsJ2 57 58 55 340 ≤ 35983176300856 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_817 c22240R_57_36 (by norm_num)

theorem c22240R_57_34 : rowsJ2 57 58 54 340 ≤ 44938025253049 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_816 c22240R_57_35 (by norm_num)

theorem c22240R_57_33 : rowsJ2 57 58 53 340 ≤ 52439161046745 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_815 c22240R_57_34 (by norm_num)

theorem c22240R_57_32 : rowsJ2 57 58 52 340 ≤ 58499379844044 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_814 c22240R_57_33 (by norm_num)

theorem c22240R_57_31 : rowsJ2 57 58 51 340 ≤ 63135963222840 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_813 c22240R_57_32 (by norm_num)

theorem c22240R_57_30 : rowsJ2 57 58 50 340 ≤ 66659873614268 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_812 c22240R_57_31 (by norm_num)

theorem c22240R_57_29 : rowsJ2 57 58 49 340 ≤ 69242453217312 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_811 c22240R_57_30 (by norm_num)

theorem c22240R_57_28 : rowsJ2 57 58 48 340 ≤ 70917135328693 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_810 c22240R_57_29 (by norm_num)

theorem c22240R_57_27 : rowsJ2 57 58 47 340 ≤ 71793702890372 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_809 c22240R_57_28 (by norm_num)

theorem c22240R_57_26 : rowsJ2 57 58 46 340 ≤ 72204257182104 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_808 c22240R_57_27 (by norm_num)

theorem c22240R_57_25 : rowsJ2 57 58 45 340 ≤ 72414782715234 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_807 c22240R_57_26 (by norm_num)

theorem c22240R_57_24 : rowsJ2 57 58 44 340 ≤ 72486770986804 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_806 c22240R_57_25 (by norm_num)

theorem c22240R_57_23 : rowsJ2 57 58 43 340 ≤ 72486770986804 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_805 c22240R_57_24 (by norm_num)

theorem c22240R_57_22 : rowsJ2 57 58 42 340 ≤ 72486770986804 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_804 c22240R_57_23 (by norm_num)

theorem c22240R_57_21 : rowsJ2 57 58 41 340 ≤ 72486770986804 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_803 c22240R_57_22 (by norm_num)

theorem c22240R_57_20 : rowsJ2 57 58 40 340 ≤ 72486770986804 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_802 c22240R_57_21 (by norm_num)

theorem c22240R_57_19 : rowsJ2 57 58 39 340 ≤ 72486770986804 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_801 c22240R_57_20 (by norm_num)

theorem c22240R_57_18 : rowsJ2 57 58 38 340 ≤ 72486770986804 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_800 c22240R_57_19 (by norm_num)

theorem c22240R_57_17 : rowsJ2 57 58 37 340 ≤ 72486770986804 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_799 c22240R_57_18 (by norm_num)

theorem c22240R_57_16 : rowsJ2 57 58 36 340 ≤ 72486770986804 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_798 c22240R_57_17 (by norm_num)

theorem c22240R_57_15 : rowsJ2 57 58 35 340 ≤ 72486770986804 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_797 c22240R_57_16 (by norm_num)

theorem c22240R_57_14 : rowsJ2 57 58 34 340 ≤ 72486770986804 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_796 c22240R_57_15 (by norm_num)

theorem c22240R_57_13 : rowsJ2 57 58 33 340 ≤ 72490806853405 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_795 c22240R_57_14 (by norm_num)

theorem c22240R_57_12 : rowsJ2 57 58 32 340 ≤ 72498895426210 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_794 c22240R_57_13 (by norm_num)

theorem c22240R_57_11 : rowsJ2 57 58 31 340 ≤ 72515560867663 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_793 c22240R_57_12 (by norm_num)

theorem c22240R_57_10 : rowsJ2 57 58 30 340 ≤ 72540855766224 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_792 c22240R_57_11 (by norm_num)

theorem c22240R_57_9 : rowsJ2 57 58 29 340 ≤ 72578733383910 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_791 c22240R_57_10 (by norm_num)

theorem c22240R_57_8 : rowsJ2 57 58 28 340 ≤ 72629289047767 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_790 c22240R_57_9 (by norm_num)

theorem c22240R_57_7 : rowsJ2 57 58 27 340 ≤ 72695935312136 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_789 c22240R_57_8 (by norm_num)

theorem c22240R_57_6 : rowsJ2 57 58 26 340 ≤ 72777206877055 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_788 c22240R_57_7 (by norm_num)

theorem c22240R_57_5 : rowsJ2 57 58 25 340 ≤ 72878137596100 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_787 c22240R_57_6 (by norm_num)

theorem c22240R_57_4 : rowsJ2 57 58 24 340 ≤ 72999479568139 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_786 c22240R_57_5 (by norm_num)

theorem c22240R_57_3 : rowsJ2 57 58 23 340 ≤ 73145231199365 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_785 c22240R_57_4 (by norm_num)

theorem c22240R_57_2 : rowsJ2 57 58 20 340 ≤ 73749704689712 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_784 c22240R_57_3 (by norm_num)

theorem c22240R_57_1 : rowsJ2 57 58 15 340 ≤ 75504041580685 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_783 c22240R_57_2 (by norm_num)

theorem c22240R_57_0 : rowsJ2 57 58 0 340 ≤ 77998414218779 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22240R_782 c22240R_57_1 (by norm_num)

theorem hr22240R_57 : rows2 57 58 ≤ 77998414218779 := rows2_le_of_rowsJ2 57 58 c22240R_57_0

theorem c22240R_58_37 : rowsJ2 58 59 57 340 ≤ 27293899763097 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_857 rows22240R_858 (by norm_num)

theorem c22240R_58_36 : rowsJ2 58 59 56 340 ≤ 39090838714746 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_856 c22240R_58_37 (by norm_num)

theorem c22240R_58_35 : rowsJ2 58 59 55 340 ≤ 49367223271294 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_855 c22240R_58_36 (by norm_num)

theorem c22240R_58_34 : rowsJ2 58 59 54 340 ≤ 58236494076607 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_854 c22240R_58_35 (by norm_num)

theorem c22240R_58_33 : rowsJ2 58 59 53 340 ≤ 65665944317133 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_853 c22240R_58_34 (by norm_num)

theorem c22240R_58_32 : rowsJ2 58 59 52 340 ≤ 71668247866829 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_852 c22240R_58_33 (by norm_num)

theorem c22240R_58_31 : rowsJ2 58 59 51 340 ≤ 76260521149993 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_851 c22240R_58_32 (by norm_num)

theorem c22240R_58_30 : rowsJ2 58 59 50 340 ≤ 79750754845959 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_850 c22240R_58_31 (by norm_num)

theorem c22240R_58_29 : rowsJ2 58 59 49 340 ≤ 82308653700308 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_849 c22240R_58_30 (by norm_num)

theorem c22240R_58_28 : rowsJ2 58 59 48 340 ≤ 83967331500230 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_848 c22240R_58_29 (by norm_num)

theorem c22240R_58_27 : rowsJ2 58 59 47 340 ≤ 84835522033112 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_847 c22240R_58_28 (by norm_num)

theorem c22240R_58_26 : rowsJ2 58 59 46 340 ≤ 85242152810815 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_846 c22240R_58_27 (by norm_num)

theorem c22240R_58_25 : rowsJ2 58 59 45 340 ≤ 85450666430055 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_845 c22240R_58_26 (by norm_num)

theorem c22240R_58_24 : rowsJ2 58 59 44 340 ≤ 85521966736600 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_844 c22240R_58_25 (by norm_num)

theorem c22240R_58_23 : rowsJ2 58 59 43 340 ≤ 85521966736600 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_843 c22240R_58_24 (by norm_num)

theorem c22240R_58_22 : rowsJ2 58 59 42 340 ≤ 85521966736600 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_842 c22240R_58_23 (by norm_num)

theorem c22240R_58_21 : rowsJ2 58 59 41 340 ≤ 85521966736600 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_841 c22240R_58_22 (by norm_num)

theorem c22240R_58_20 : rowsJ2 58 59 40 340 ≤ 85521966736600 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_840 c22240R_58_21 (by norm_num)

theorem c22240R_58_19 : rowsJ2 58 59 39 340 ≤ 85521966736600 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_839 c22240R_58_20 (by norm_num)

theorem c22240R_58_18 : rowsJ2 58 59 38 340 ≤ 85521966736600 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_838 c22240R_58_19 (by norm_num)

theorem c22240R_58_17 : rowsJ2 58 59 37 340 ≤ 85521966736600 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_837 c22240R_58_18 (by norm_num)

theorem c22240R_58_16 : rowsJ2 58 59 36 340 ≤ 85521966736600 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_836 c22240R_58_17 (by norm_num)

theorem c22240R_58_15 : rowsJ2 58 59 35 340 ≤ 85521966736600 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_835 c22240R_58_16 (by norm_num)

theorem c22240R_58_14 : rowsJ2 58 59 34 340 ≤ 85521966736600 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_834 c22240R_58_15 (by norm_num)

theorem c22240R_58_13 : rowsJ2 58 59 33 340 ≤ 85521966736600 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_833 c22240R_58_14 (by norm_num)

theorem c22240R_58_12 : rowsJ2 58 59 32 340 ≤ 85526014865609 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_832 c22240R_58_13 (by norm_num)

theorem c22240R_58_11 : rowsJ2 58 59 31 340 ≤ 85534129326688 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_831 c22240R_58_12 (by norm_num)

theorem c22240R_58_10 : rowsJ2 58 59 30 340 ≤ 85550850881914 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_830 c22240R_58_11 (by norm_num)

theorem c22240R_58_9 : rowsJ2 58 59 29 340 ≤ 85575691110170 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_829 c22240R_58_10 (by norm_num)

theorem c22240R_58_8 : rowsJ2 58 59 28 340 ≤ 85613165627640 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_828 c22240R_58_9 (by norm_num)

theorem c22240R_58_7 : rowsJ2 58 59 27 340 ≤ 85662831138682 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_827 c22240R_58_8 (by norm_num)

theorem c22240R_58_6 : rowsJ2 58 59 26 340 ≤ 85728126381753 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_826 c22240R_58_7 (by norm_num)

theorem c22240R_58_5 : rowsJ2 58 59 25 340 ≤ 85809201566407 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_825 c22240R_58_6 (by norm_num)

theorem c22240R_58_4 : rowsJ2 58 59 24 340 ≤ 85910582933713 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_824 c22240R_58_5 (by norm_num)

theorem c22240R_58_3 : rowsJ2 58 59 23 340 ≤ 86032491123627 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_823 c22240R_58_4 (by norm_num)

theorem c22240R_58_2 : rowsJ2 58 59 21 340 ≤ 86350275261961 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_822 c22240R_58_3 (by norm_num)

theorem c22240R_58_1 : rowsJ2 58 59 16 340 ≤ 87724126932762 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_821 c22240R_58_2 (by norm_num)

theorem c22240R_58_0 : rowsJ2 58 59 0 340 ≤ 90589589742373 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22240R_820 c22240R_58_1 (by norm_num)

theorem hr22240R_58 : rows2 58 59 ≤ 90589589742373 := rows2_le_of_rowsJ2 58 59 c22240R_58_0

theorem c22240R_59_38 : rowsJ2 59 60 58 340 ≤ 28486048785592 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_897 rows22240R_898 (by norm_num)

theorem c22240R_59_37 : rowsJ2 59 60 57 340 ≤ 41210398074202 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_896 c22240R_59_38 (by norm_num)

theorem c22240R_59_36 : rowsJ2 59 60 56 340 ≤ 52704907884071 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_895 c22240R_59_37 (by norm_num)

theorem c22240R_59_35 : rowsJ2 59 60 55 340 ≤ 62789650360828 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_894 c22240R_59_36 (by norm_num)

theorem c22240R_59_34 : rowsJ2 59 60 54 340 ≤ 71528494779050 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_893 c22240R_59_35 (by norm_num)

theorem c22240R_59_33 : rowsJ2 59 60 53 340 ≤ 78887616670903 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_892 c22240R_59_34 (by norm_num)

theorem c22240R_59_32 : rowsJ2 59 60 52 340 ≤ 84833101467771 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_891 c22240R_59_33 (by norm_num)

theorem c22240R_59_31 : rowsJ2 59 60 51 340 ≤ 89381903567178 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_890 c22240R_59_32 (by norm_num)

theorem c22240R_59_30 : rowsJ2 59 60 50 340 ≤ 92839098160065 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_889 c22240R_59_31 (by norm_num)

theorem c22240R_59_29 : rowsJ2 59 60 49 340 ≤ 95372783540110 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_888 c22240R_59_30 (by norm_num)

theorem c22240R_59_28 : rowsJ2 59 60 48 340 ≤ 97015760034163 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_887 c22240R_59_29 (by norm_num)

theorem c22240R_59_27 : rowsJ2 59 60 47 340 ≤ 97875732138424 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_886 c22240R_59_28 (by norm_num)

theorem c22240R_59_26 : rowsJ2 59 60 46 340 ≤ 98278513685002 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_885 c22240R_59_27 (by norm_num)

theorem c22240R_59_25 : rowsJ2 59 60 45 340 ≤ 98485053481410 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_884 c22240R_59_26 (by norm_num)

theorem c22240R_59_24 : rowsJ2 59 60 44 340 ≤ 98555678847999 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_883 c22240R_59_25 (by norm_num)

theorem c22240R_59_23 : rowsJ2 59 60 43 340 ≤ 98555678847999 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_882 c22240R_59_24 (by norm_num)

theorem c22240R_59_22 : rowsJ2 59 60 42 340 ≤ 98555678847999 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_881 c22240R_59_23 (by norm_num)

theorem c22240R_59_21 : rowsJ2 59 60 41 340 ≤ 98555678847999 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_880 c22240R_59_22 (by norm_num)

theorem c22240R_59_20 : rowsJ2 59 60 40 340 ≤ 98555678847999 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_879 c22240R_59_21 (by norm_num)

theorem c22240R_59_19 : rowsJ2 59 60 39 340 ≤ 98555678847999 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_878 c22240R_59_20 (by norm_num)

theorem c22240R_59_18 : rowsJ2 59 60 38 340 ≤ 98555678847999 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_877 c22240R_59_19 (by norm_num)

theorem c22240R_59_17 : rowsJ2 59 60 37 340 ≤ 98555678847999 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_876 c22240R_59_18 (by norm_num)

theorem c22240R_59_16 : rowsJ2 59 60 36 340 ≤ 98555678847999 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_875 c22240R_59_17 (by norm_num)

theorem c22240R_59_15 : rowsJ2 59 60 35 340 ≤ 98555678847999 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_874 c22240R_59_16 (by norm_num)

theorem c22240R_59_14 : rowsJ2 59 60 34 340 ≤ 98555678847999 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_873 c22240R_59_15 (by norm_num)

theorem c22240R_59_13 : rowsJ2 59 60 33 340 ≤ 98555678847999 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_872 c22240R_59_14 (by norm_num)

theorem c22240R_59_12 : rowsJ2 59 60 32 340 ≤ 98555678847999 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_871 c22240R_59_13 (by norm_num)

theorem c22240R_59_11 : rowsJ2 59 60 31 340 ≤ 98559740304390 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_870 c22240R_59_12 (by norm_num)

theorem c22240R_59_10 : rowsJ2 59 60 30 340 ≤ 98567882831142 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_869 c22240R_59_11 (by norm_num)

theorem c22240R_59_9 : rowsJ2 59 60 29 340 ≤ 98584126067890 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_868 c22240R_59_10 (by norm_num)

theorem c22240R_59_8 : rowsJ2 59 60 28 340 ≤ 98608522207416 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_867 c22240R_59_9 (by norm_num)

theorem c22240R_59_7 : rowsJ2 59 60 27 340 ≤ 98645069364895 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_866 c22240R_59_8 (by norm_num)

theorem c22240R_59_6 : rowsJ2 59 60 26 340 ≤ 98693865401361 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_865 c22240R_59_7 (by norm_num)

theorem c22240R_59_5 : rowsJ2 59 60 25 340 ≤ 98758907191410 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_864 c22240R_59_6 (by norm_num)

theorem c22240R_59_4 : rowsJ2 59 60 24 340 ≤ 98840351809422 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_863 c22240R_59_5 (by norm_num)

theorem c22240R_59_3 : rowsJ2 59 60 23 340 ≤ 98942215556011 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_862 c22240R_59_4 (by norm_num)

theorem c22240R_59_2 : rowsJ2 59 60 21 340 ≤ 99211949502277 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_861 c22240R_59_3 (by norm_num)

theorem c22240R_59_1 : rowsJ2 59 60 16 340 ≤ 100408875644651 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_860 c22240R_59_2 (by norm_num)

theorem c22240R_59_0 : rowsJ2 59 60 0 340 ≤ 103201972362495 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22240R_859 c22240R_59_1 (by norm_num)

theorem hr22240R_59 : rows2 59 60 ≤ 103201972362495 := rows2_le_of_rowsJ2 59 60 c22240R_59_0

theorem c22240R_60_39 : rowsJ2 60 61 59 340 ≤ 29366102843071 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_938 rows22240R_939 (by norm_num)

theorem c22240R_60_38 : rowsJ2 60 61 58 340 ≤ 42615581492624 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_937 c22240R_60_39 (by norm_num)

theorem c22240R_60_37 : rowsJ2 60 61 57 340 ≤ 54927981860644 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_936 c22240R_60_38 (by norm_num)

theorem c22240R_60_36 : rowsJ2 60 61 56 340 ≤ 66121822907241 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_935 c22240R_60_37 (by norm_num)

theorem c22240R_60_35 : rowsJ2 60 61 55 340 ≤ 75969636800888 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_934 c22240R_60_36 (by norm_num)

theorem c22240R_60_34 : rowsJ2 60 61 54 340 ≤ 84579572383496 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_933 c22240R_60_35 (by norm_num)

theorem c22240R_60_33 : rowsJ2 60 61 53 340 ≤ 91869684948386 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_932 c22240R_60_34 (by norm_num)

theorem c22240R_60_32 : rowsJ2 60 61 52 340 ≤ 97759416639059 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_931 c22240R_60_33 (by norm_num)

theorem c22240R_60_31 : rowsJ2 60 61 51 340 ≤ 102265562865116 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_930 c22240R_60_32 (by norm_num)

theorem c22240R_60_30 : rowsJ2 60 61 50 340 ≤ 105690338009656 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_929 c22240R_60_31 (by norm_num)

theorem c22240R_60_29 : rowsJ2 60 61 49 340 ≤ 108200264043766 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_928 c22240R_60_30 (by norm_num)

theorem c22240R_60_28 : rowsJ2 60 61 48 340 ≤ 109827833712966 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_927 c22240R_60_29 (by norm_num)

theorem c22240R_60_27 : rowsJ2 60 61 47 340 ≤ 110679741526812 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_926 c22240R_60_28 (by norm_num)

theorem c22240R_60_26 : rowsJ2 60 61 46 340 ≤ 111078746035334 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_925 c22240R_60_27 (by norm_num)

theorem c22240R_60_25 : rowsJ2 60 61 45 340 ≤ 111283349028337 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_924 c22240R_60_26 (by norm_num)

theorem c22240R_60_24 : rowsJ2 60 61 44 340 ≤ 111353312113599 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_923 c22240R_60_25 (by norm_num)

theorem c22240R_60_23 : rowsJ2 60 61 43 340 ≤ 111353312113599 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_922 c22240R_60_24 (by norm_num)

theorem c22240R_60_22 : rowsJ2 60 61 42 340 ≤ 111353312113599 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_921 c22240R_60_23 (by norm_num)

theorem c22240R_60_21 : rowsJ2 60 61 41 340 ≤ 111353312113599 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_920 c22240R_60_22 (by norm_num)

theorem c22240R_60_20 : rowsJ2 60 61 40 340 ≤ 111353312113599 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_919 c22240R_60_21 (by norm_num)

theorem c22240R_60_19 : rowsJ2 60 61 39 340 ≤ 111353312113599 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_918 c22240R_60_20 (by norm_num)

theorem c22240R_60_18 : rowsJ2 60 61 38 340 ≤ 111353312113599 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_917 c22240R_60_19 (by norm_num)

theorem c22240R_60_17 : rowsJ2 60 61 37 340 ≤ 111353312113599 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_916 c22240R_60_18 (by norm_num)

theorem c22240R_60_16 : rowsJ2 60 61 36 340 ≤ 111353312113599 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_915 c22240R_60_17 (by norm_num)

theorem c22240R_60_15 : rowsJ2 60 61 35 340 ≤ 111353312113599 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_914 c22240R_60_16 (by norm_num)

theorem c22240R_60_14 : rowsJ2 60 61 34 340 ≤ 111353312113599 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_913 c22240R_60_15 (by norm_num)

theorem c22240R_60_13 : rowsJ2 60 61 33 340 ≤ 111353312113599 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_912 c22240R_60_14 (by norm_num)

theorem c22240R_60_12 : rowsJ2 60 61 32 340 ≤ 111353312113599 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_911 c22240R_60_13 (by norm_num)

theorem c22240R_60_11 : rowsJ2 60 61 31 340 ≤ 111353312113599 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_910 c22240R_60_12 (by norm_num)

theorem c22240R_60_10 : rowsJ2 60 61 30 340 ≤ 111357387982690 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_909 c22240R_60_11 (by norm_num)

theorem c22240R_60_9 : rowsJ2 60 61 29 340 ≤ 111365560796072 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_908 c22240R_60_10 (by norm_num)

theorem c22240R_60_8 : rowsJ2 60 61 28 340 ≤ 111381867301055 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_907 c22240R_60_9 (by norm_num)

theorem c22240R_60_7 : rowsJ2 60 61 27 340 ≤ 111406362862349 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_906 c22240R_60_8 (by norm_num)

theorem c22240R_60_6 : rowsJ2 60 61 26 340 ≤ 111443065730012 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_905 c22240R_60_7 (by norm_num)

theorem c22240R_60_5 : rowsJ2 60 61 25 340 ≤ 111492078953749 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_904 c22240R_60_6 (by norm_num)

theorem c22240R_60_4 : rowsJ2 60 61 24 340 ≤ 111557422973788 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_903 c22240R_60_5 (by norm_num)

theorem c22240R_60_3 : rowsJ2 60 61 23 340 ≤ 111639262444512 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_902 c22240R_60_4 (by norm_num)

theorem c22240R_60_2 : rowsJ2 60 61 21 340 ≤ 111864800155213 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_901 c22240R_60_3 (by norm_num)

theorem c22240R_60_1 : rowsJ2 60 61 16 340 ≤ 112902871305142 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_900 c22240R_60_2 (by norm_num)

theorem c22240R_60_0 : rowsJ2 60 61 0 340 ≤ 115609243718652 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22240R_899 c22240R_60_1 (by norm_num)

theorem hr22240R_60 : rows2 60 61 ≤ 115609243718652 := rows2_le_of_rowsJ2 60 61 c22240R_60_0

theorem c22240R_61_40 : rowsJ2 61 62 60 340 ≤ 29116275969620 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_980 rows22240R_981 (by norm_num)

theorem c22240R_61_39 : rowsJ2 61 62 59 340 ≤ 42697019000999 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_979 c22240R_61_40 (by norm_num)

theorem c22240R_61_38 : rowsJ2 61 62 58 340 ≤ 55423892836714 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_978 c22240R_61_39 (by norm_num)

theorem c22240R_61_37 : rowsJ2 61 62 57 340 ≤ 67325868207770 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_977 c22240R_61_38 (by norm_num)

theorem c22240R_61_36 : rowsJ2 61 62 56 340 ≤ 78173138310782 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_976 c22240R_61_37 (by norm_num)

theorem c22240R_61_35 : rowsJ2 61 62 55 340 ≤ 87785521834861 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_975 c22240R_61_36 (by norm_num)

theorem c22240R_61_34 : rowsJ2 61 62 54 340 ≤ 96221003744713 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_974 c22240R_61_35 (by norm_num)

theorem c22240R_61_33 : rowsJ2 61 62 53 340 ≤ 103443389240527 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_973 c22240R_61_34 (by norm_num)

theorem c22240R_61_32 : rowsJ2 61 62 52 340 ≤ 109278403769911 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_972 c22240R_61_33 (by norm_num)

theorem c22240R_61_31 : rowsJ2 61 62 51 340 ≤ 113742686708676 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_971 c22240R_61_32 (by norm_num)

theorem c22240R_61_30 : rowsJ2 61 62 50 340 ≤ 117135644788568 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_970 c22240R_61_31 (by norm_num)

theorem c22240R_61_29 : rowsJ2 61 62 49 340 ≤ 119622252947629 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_969 c22240R_61_30 (by norm_num)

theorem c22240R_61_28 : rowsJ2 61 62 48 340 ≤ 121234702065198 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_968 c22240R_61_29 (by norm_num)

theorem c22240R_61_27 : rowsJ2 61 62 47 340 ≤ 122078695430695 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_967 c22240R_61_28 (by norm_num)

theorem c22240R_61_26 : rowsJ2 61 62 46 340 ≤ 122473993082063 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_966 c22240R_61_27 (by norm_num)

theorem c22240R_61_25 : rowsJ2 61 62 45 340 ≤ 122676695259280 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_965 c22240R_61_26 (by norm_num)

theorem c22240R_61_24 : rowsJ2 61 62 44 340 ≤ 122746008369021 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_964 c22240R_61_25 (by norm_num)

theorem c22240R_61_23 : rowsJ2 61 62 43 340 ≤ 122746008369021 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_963 c22240R_61_24 (by norm_num)

theorem c22240R_61_22 : rowsJ2 61 62 42 340 ≤ 122746008369021 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_962 c22240R_61_23 (by norm_num)

theorem c22240R_61_21 : rowsJ2 61 62 41 340 ≤ 122746008369021 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_961 c22240R_61_22 (by norm_num)

theorem c22240R_61_20 : rowsJ2 61 62 40 340 ≤ 122746008369021 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_960 c22240R_61_21 (by norm_num)

theorem c22240R_61_19 : rowsJ2 61 62 39 340 ≤ 122746008369021 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_959 c22240R_61_20 (by norm_num)

theorem c22240R_61_18 : rowsJ2 61 62 38 340 ≤ 122746008369021 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_958 c22240R_61_19 (by norm_num)

theorem c22240R_61_17 : rowsJ2 61 62 37 340 ≤ 122746008369021 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_957 c22240R_61_18 (by norm_num)

theorem c22240R_61_16 : rowsJ2 61 62 36 340 ≤ 122746008369021 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_956 c22240R_61_17 (by norm_num)

theorem c22240R_61_15 : rowsJ2 61 62 35 340 ≤ 122746008369021 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_955 c22240R_61_16 (by norm_num)

theorem c22240R_61_14 : rowsJ2 61 62 34 340 ≤ 122746008369021 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_954 c22240R_61_15 (by norm_num)

theorem c22240R_61_13 : rowsJ2 61 62 33 340 ≤ 122746008369021 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_953 c22240R_61_14 (by norm_num)

theorem c22240R_61_12 : rowsJ2 61 62 32 340 ≤ 122746008369021 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_952 c22240R_61_13 (by norm_num)

theorem c22240R_61_11 : rowsJ2 61 62 31 340 ≤ 122746008369021 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_951 c22240R_61_12 (by norm_num)

theorem c22240R_61_10 : rowsJ2 61 62 30 340 ≤ 122746008369021 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_950 c22240R_61_11 (by norm_num)

theorem c22240R_61_9 : rowsJ2 61 62 29 340 ≤ 122750099758353 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_949 c22240R_61_10 (by norm_num)

theorem c22240R_61_8 : rowsJ2 61 62 28 340 ≤ 122758305126834 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_948 c22240R_61_9 (by norm_num)

theorem c22240R_61_7 : rowsJ2 61 62 27 340 ≤ 122774679525789 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_947 c22240R_61_8 (by norm_num)

theorem c22240R_61_6 : rowsJ2 61 62 26 340 ≤ 122799281614592 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_946 c22240R_61_7 (by norm_num)

theorem c22240R_61_5 : rowsJ2 61 62 25 340 ≤ 122836151086067 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_945 c22240R_61_6 (by norm_num)

theorem c22240R_61_4 : rowsJ2 61 62 24 340 ≤ 122885396390371 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_944 c22240R_61_5 (by norm_num)

theorem c22240R_61_3 : rowsJ2 61 62 23 340 ≤ 122951062980269 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_943 c22240R_61_4 (by norm_num)

theorem c22240R_61_2 : rowsJ2 61 62 21 340 ≤ 123136250587434 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_942 c22240R_61_3 (by norm_num)

theorem c22240R_61_1 : rowsJ2 61 62 17 340 ≤ 123789315246670 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_941 c22240R_61_2 (by norm_num)

theorem c22240R_61_0 : rowsJ2 61 62 0 340 ≤ 126634278895273 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22240R_940 c22240R_61_1 (by norm_num)

theorem hr22240R_61 : rows2 61 62 ≤ 126634278895273 := rows2_le_of_rowsJ2 61 62 c22240R_61_0

theorem c22240R_62_41 : rowsJ2 62 63 61 340 ≤ 25921751479986 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1023 rows22240R_1024 (by norm_num)

theorem c22240R_62_40 : rowsJ2 62 63 60 340 ≤ 39702566279046 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1022 c22240R_62_41 (by norm_num)

theorem c22240R_62_39 : rowsJ2 62 63 59 340 ≤ 52646291328165 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1021 c22240R_62_40 (by norm_num)

theorem c22240R_62_38 : rowsJ2 62 63 58 340 ≤ 64851625243112 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1020 c22240R_62_39 (by norm_num)

theorem c22240R_62_37 : rowsJ2 62 63 57 340 ≤ 76296415446194 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1019 c22240R_62_38 (by norm_num)

theorem c22240R_62_36 : rowsJ2 62 63 56 340 ≤ 86798440371061 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1018 c22240R_62_37 (by norm_num)

theorem c22240R_62_35 : rowsJ2 62 63 55 340 ≤ 96129242867512 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1017 c22240R_62_36 (by norm_num)

theorem c22240R_62_34 : rowsJ2 62 63 54 340 ≤ 104391565566307 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1016 c22240R_62_35 (by norm_num)

theorem c22240R_62_33 : rowsJ2 62 63 53 340 ≤ 111500444140323 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1015 c22240R_62_34 (by norm_num)

theorem c22240R_62_32 : rowsJ2 62 63 52 340 ≤ 117281748845253 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1014 c22240R_62_33 (by norm_num)

theorem c22240R_62_31 : rowsJ2 62 63 51 340 ≤ 121704939195167 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1013 c22240R_62_32 (by norm_num)

theorem c22240R_62_30 : rowsJ2 62 63 50 340 ≤ 125066665959024 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1012 c22240R_62_31 (by norm_num)

theorem c22240R_62_29 : rowsJ2 62 63 49 340 ≤ 127530385522513 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1011 c22240R_62_30 (by norm_num)

theorem c22240R_62_28 : rowsJ2 62 63 48 340 ≤ 129127992456126 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1010 c22240R_62_29 (by norm_num)

theorem c22240R_62_27 : rowsJ2 62 63 47 340 ≤ 129964217077387 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1009 c22240R_62_28 (by norm_num)

theorem c22240R_62_26 : rowsJ2 62 63 46 340 ≤ 130355876114429 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1008 c22240R_62_27 (by norm_num)

theorem c22240R_62_25 : rowsJ2 62 63 45 340 ≤ 130556712469668 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1007 c22240R_62_26 (by norm_num)

theorem c22240R_62_24 : rowsJ2 62 63 44 340 ≤ 130625387569865 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1006 c22240R_62_25 (by norm_num)

theorem c22240R_62_23 : rowsJ2 62 63 43 340 ≤ 130625387569865 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1005 c22240R_62_24 (by norm_num)

theorem c22240R_62_22 : rowsJ2 62 63 42 340 ≤ 130625387569865 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1004 c22240R_62_23 (by norm_num)

theorem c22240R_62_21 : rowsJ2 62 63 41 340 ≤ 130625387569865 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1003 c22240R_62_22 (by norm_num)

theorem c22240R_62_20 : rowsJ2 62 63 40 340 ≤ 130625387569865 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1002 c22240R_62_21 (by norm_num)

theorem c22240R_62_19 : rowsJ2 62 63 39 340 ≤ 130625387569865 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1001 c22240R_62_20 (by norm_num)

theorem c22240R_62_18 : rowsJ2 62 63 38 340 ≤ 130625387569865 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_1000 c22240R_62_19 (by norm_num)

theorem c22240R_62_17 : rowsJ2 62 63 37 340 ≤ 130625387569865 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_999 c22240R_62_18 (by norm_num)

theorem c22240R_62_16 : rowsJ2 62 63 36 340 ≤ 130625387569865 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_998 c22240R_62_17 (by norm_num)

theorem c22240R_62_15 : rowsJ2 62 63 35 340 ≤ 130625387569865 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_997 c22240R_62_16 (by norm_num)

theorem c22240R_62_14 : rowsJ2 62 63 34 340 ≤ 130625387569865 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_996 c22240R_62_15 (by norm_num)

theorem c22240R_62_13 : rowsJ2 62 63 33 340 ≤ 130625387569865 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_995 c22240R_62_14 (by norm_num)

theorem c22240R_62_12 : rowsJ2 62 63 32 340 ≤ 130625387569865 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_994 c22240R_62_13 (by norm_num)

theorem c22240R_62_11 : rowsJ2 62 63 31 340 ≤ 130625387569865 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_993 c22240R_62_12 (by norm_num)

theorem c22240R_62_10 : rowsJ2 62 63 30 340 ≤ 130625387569865 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_992 c22240R_62_11 (by norm_num)

theorem c22240R_62_9 : rowsJ2 62 63 29 340 ≤ 130625387569865 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_991 c22240R_62_10 (by norm_num)

theorem c22240R_62_8 : rowsJ2 62 63 28 340 ≤ 130629495611169 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_990 c22240R_62_9 (by norm_num)

theorem c22240R_62_7 : rowsJ2 62 63 27 340 ≤ 130637735854865 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_989 c22240R_62_8 (by norm_num)

theorem c22240R_62_6 : rowsJ2 62 63 26 340 ≤ 130654182883204 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_988 c22240R_62_7 (by norm_num)

theorem c22240R_62_5 : rowsJ2 62 63 25 340 ≤ 130678898780550 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_987 c22240R_62_6 (by norm_num)

theorem c22240R_62_4 : rowsJ2 62 63 24 340 ≤ 130715946028843 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_986 c22240R_62_5 (by norm_num)

theorem c22240R_62_3 : rowsJ2 62 63 23 340 ≤ 130765438703764 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_985 c22240R_62_4 (by norm_num)

theorem c22240R_62_2 : rowsJ2 62 63 21 340 ≤ 130914157026277 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_984 c22240R_62_3 (by norm_num)

theorem c22240R_62_1 : rowsJ2 62 63 17 340 ≤ 131467428439936 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_983 c22240R_62_2 (by norm_num)

theorem c22240R_62_0 : rowsJ2 62 63 0 340 ≤ 134167706864318 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22240R_982 c22240R_62_1 (by norm_num)

theorem hr22240R_62 : rows2 62 63 ≤ 134167706864318 := rows2_le_of_rowsJ2 62 63 c22240R_62_0

theorem c22240R_63_42 : rowsJ2 63 64 62 340 ≤ 22204207104129 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1067 rows22240R_1068 (by norm_num)

theorem c22240R_63_41 : rowsJ2 63 64 61 340 ≤ 34069783535704 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1066 c22240R_63_42 (by norm_num)

theorem c22240R_63_40 : rowsJ2 63 64 60 340 ≤ 46446698223454 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1065 c22240R_63_41 (by norm_num)

theorem c22240R_63_39 : rowsJ2 63 64 59 340 ≤ 58753808082820 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1064 c22240R_63_40 (by norm_num)

theorem c22240R_63_38 : rowsJ2 63 64 58 340 ≤ 70389726760770 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1063 c22240R_63_39 (by norm_num)

theorem c22240R_63_37 : rowsJ2 63 64 57 340 ≤ 81378268371731 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1062 c22240R_63_38 (by norm_num)

theorem c22240R_63_36 : rowsJ2 63 64 56 340 ≤ 91488105052914 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1061 c22240R_63_37 (by norm_num)

theorem c22240R_63_35 : rowsJ2 63 64 55 340 ≤ 100538460853195 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1060 c22240R_63_36 (by norm_num)

theorem c22240R_63_34 : rowsJ2 63 64 54 340 ≤ 108581272258746 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1059 c22240R_63_35 (by norm_num)

theorem c22240R_63_33 : rowsJ2 63 64 53 340 ≤ 115577764904168 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1058 c22240R_63_34 (by norm_num)

theorem c22240R_63_32 : rowsJ2 63 64 52 340 ≤ 121306339557189 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1057 c22240R_63_33 (by norm_num)

theorem c22240R_63_31 : rowsJ2 63 64 51 340 ≤ 125689186927686 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1056 c22240R_63_32 (by norm_num)

theorem c22240R_63_30 : rowsJ2 63 64 50 340 ≤ 129020252095964 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1055 c22240R_63_31 (by norm_num)

theorem c22240R_63_29 : rowsJ2 63 64 49 340 ≤ 131461500596762 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1054 c22240R_63_30 (by norm_num)

theorem c22240R_63_28 : rowsJ2 63 64 48 340 ≤ 133044536096963 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1053 c22240R_63_29 (by norm_num)

theorem c22240R_63_27 : rowsJ2 63 64 47 340 ≤ 133873133691117 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1052 c22240R_63_28 (by norm_num)

theorem c22240R_63_26 : rowsJ2 63 64 46 340 ≤ 134261220489295 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1051 c22240R_63_27 (by norm_num)

theorem c22240R_63_25 : rowsJ2 63 64 45 340 ≤ 134460225058807 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1050 c22240R_63_26 (by norm_num)

theorem c22240R_63_24 : rowsJ2 63 64 44 340 ≤ 134528273788006 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1049 c22240R_63_25 (by norm_num)

theorem c22240R_63_23 : rowsJ2 63 64 43 340 ≤ 134528273788006 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1048 c22240R_63_24 (by norm_num)

theorem c22240R_63_22 : rowsJ2 63 64 42 340 ≤ 134528273788006 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1047 c22240R_63_23 (by norm_num)

theorem c22240R_63_21 : rowsJ2 63 64 41 340 ≤ 134528273788006 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1046 c22240R_63_22 (by norm_num)

theorem c22240R_63_20 : rowsJ2 63 64 40 340 ≤ 134528273788006 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1045 c22240R_63_21 (by norm_num)

theorem c22240R_63_19 : rowsJ2 63 64 39 340 ≤ 134528273788006 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1044 c22240R_63_20 (by norm_num)

theorem c22240R_63_18 : rowsJ2 63 64 38 340 ≤ 134528273788006 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1043 c22240R_63_19 (by norm_num)

theorem c22240R_63_17 : rowsJ2 63 64 37 340 ≤ 134528273788006 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1042 c22240R_63_18 (by norm_num)

theorem c22240R_63_16 : rowsJ2 63 64 36 340 ≤ 134528273788006 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1041 c22240R_63_17 (by norm_num)

theorem c22240R_63_15 : rowsJ2 63 64 35 340 ≤ 134528273788006 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1040 c22240R_63_16 (by norm_num)

theorem c22240R_63_14 : rowsJ2 63 64 34 340 ≤ 134528273788006 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1039 c22240R_63_15 (by norm_num)

theorem c22240R_63_13 : rowsJ2 63 64 33 340 ≤ 134528273788006 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1038 c22240R_63_14 (by norm_num)

theorem c22240R_63_12 : rowsJ2 63 64 32 340 ≤ 134528273788006 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1037 c22240R_63_13 (by norm_num)

theorem c22240R_63_11 : rowsJ2 63 64 31 340 ≤ 134528273788006 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1036 c22240R_63_12 (by norm_num)

theorem c22240R_63_10 : rowsJ2 63 64 30 340 ≤ 134528273788006 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1035 c22240R_63_11 (by norm_num)

theorem c22240R_63_9 : rowsJ2 63 64 29 340 ≤ 134528273788006 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1034 c22240R_63_10 (by norm_num)

theorem c22240R_63_8 : rowsJ2 63 64 28 340 ≤ 134528273788006 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1033 c22240R_63_9 (by norm_num)

theorem c22240R_63_7 : rowsJ2 63 64 27 340 ≤ 134532399639274 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1032 c22240R_63_8 (by norm_num)

theorem c22240R_63_6 : rowsJ2 63 64 26 340 ≤ 134540677134301 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1031 c22240R_63_7 (by norm_num)

theorem c22240R_63_5 : rowsJ2 63 64 25 340 ≤ 134557201646249 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1030 c22240R_63_6 (by norm_num)

theorem c22240R_63_4 : rowsJ2 63 64 24 340 ≤ 134582038822916 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1029 c22240R_63_5 (by norm_num)

theorem c22240R_63_3 : rowsJ2 63 64 23 340 ≤ 134619275323236 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1028 c22240R_63_4 (by norm_num)

theorem c22240R_63_2 : rowsJ2 63 64 21 340 ≤ 134735406132195 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1027 c22240R_63_3 (by norm_num)

theorem c22240R_63_1 : rowsJ2 63 64 17 340 ≤ 135198833032193 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1026 c22240R_63_2 (by norm_num)

theorem c22240R_63_0 : rowsJ2 63 64 0 340 ≤ 137744907321407 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22240R_1025 c22240R_63_1 (by norm_num)

theorem hr22240R_63 : rows2 63 64 ≤ 137744907321407 := rows2_le_of_rowsJ2 63 64 c22240R_63_0

theorem c22240R_64_43 : rowsJ2 64 65 63 340 ≤ 18816503204547 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1112 rows22240R_1113 (by norm_num)

theorem c22240R_64_42 : rowsJ2 64 65 62 340 ≤ 28965902550092 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1111 c22240R_64_43 (by norm_num)

theorem c22240R_64_41 : rowsJ2 64 65 61 340 ≤ 39566608712242 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1110 c22240R_64_42 (by norm_num)

theorem c22240R_64_40 : rowsJ2 64 65 60 340 ≤ 50674512132895 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1109 c22240R_64_41 (by norm_num)

theorem c22240R_64_39 : rowsJ2 64 65 59 340 ≤ 62295775148638 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1108 c22240R_64_40 (by norm_num)

theorem c22240R_64_38 : rowsJ2 64 65 58 340 ≤ 73362594058767 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1107 c22240R_64_39 (by norm_num)

theorem c22240R_64_37 : rowsJ2 64 65 57 340 ≤ 83846900601819 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1106 c22240R_64_38 (by norm_num)

theorem c22240R_64_36 : rowsJ2 64 65 56 340 ≤ 93565361137783 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1105 c22240R_64_37 (by norm_num)

theorem c22240R_64_35 : rowsJ2 64 65 55 340 ≤ 102288141000365 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1104 c22240R_64_36 (by norm_num)

theorem c22240R_64_34 : rowsJ2 64 65 54 340 ≤ 110112437183279 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1103 c22240R_64_35 (by norm_num)

theorem c22240R_64_33 : rowsJ2 64 65 53 340 ≤ 116950010151659 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1102 c22240R_64_34 (by norm_num)

theorem c22240R_64_32 : rowsJ2 64 65 52 340 ≤ 122626807957635 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1101 c22240R_64_33 (by norm_num)

theorem c22240R_64_31 : rowsJ2 64 65 51 340 ≤ 126970041631590 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1100 c22240R_64_32 (by norm_num)

theorem c22240R_64_30 : rowsJ2 64 65 50 340 ≤ 130270999476117 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1099 c22240R_64_31 (by norm_num)

theorem c22240R_64_29 : rowsJ2 64 65 49 340 ≤ 132690183125206 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1098 c22240R_64_30 (by norm_num)

theorem c22240R_64_28 : rowsJ2 64 65 48 340 ≤ 134258910600825 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1097 c22240R_64_29 (by norm_num)

theorem c22240R_64_27 : rowsJ2 64 65 47 340 ≤ 135080019042182 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1096 c22240R_64_28 (by norm_num)

theorem c22240R_64_26 : rowsJ2 64 65 46 340 ≤ 135464598177109 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1095 c22240R_64_27 (by norm_num)

theorem c22240R_64_25 : rowsJ2 64 65 45 340 ≤ 135661804074215 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1094 c22240R_64_26 (by norm_num)

theorem c22240R_64_24 : rowsJ2 64 65 44 340 ≤ 135729237755369 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1093 c22240R_64_25 (by norm_num)

theorem c22240R_64_23 : rowsJ2 64 65 43 340 ≤ 135729237755369 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1092 c22240R_64_24 (by norm_num)

theorem c22240R_64_22 : rowsJ2 64 65 42 340 ≤ 135729237755369 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1091 c22240R_64_23 (by norm_num)

theorem c22240R_64_21 : rowsJ2 64 65 41 340 ≤ 135729237755369 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1090 c22240R_64_22 (by norm_num)

theorem c22240R_64_20 : rowsJ2 64 65 40 340 ≤ 135729237755369 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1089 c22240R_64_21 (by norm_num)

theorem c22240R_64_19 : rowsJ2 64 65 39 340 ≤ 135729237755369 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1088 c22240R_64_20 (by norm_num)

theorem c22240R_64_18 : rowsJ2 64 65 38 340 ≤ 135729237755369 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1087 c22240R_64_19 (by norm_num)

theorem c22240R_64_17 : rowsJ2 64 65 37 340 ≤ 135729237755369 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1086 c22240R_64_18 (by norm_num)

theorem c22240R_64_16 : rowsJ2 64 65 36 340 ≤ 135729237755369 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1085 c22240R_64_17 (by norm_num)

theorem c22240R_64_15 : rowsJ2 64 65 35 340 ≤ 135729237755369 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1084 c22240R_64_16 (by norm_num)

theorem c22240R_64_14 : rowsJ2 64 65 34 340 ≤ 135729237755369 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1083 c22240R_64_15 (by norm_num)

theorem c22240R_64_13 : rowsJ2 64 65 33 340 ≤ 135729237755369 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1082 c22240R_64_14 (by norm_num)

theorem c22240R_64_12 : rowsJ2 64 65 32 340 ≤ 135729237755369 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1081 c22240R_64_13 (by norm_num)

theorem c22240R_64_11 : rowsJ2 64 65 31 340 ≤ 135729237755369 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1080 c22240R_64_12 (by norm_num)

theorem c22240R_64_10 : rowsJ2 64 65 30 340 ≤ 135729237755369 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1079 c22240R_64_11 (by norm_num)

theorem c22240R_64_9 : rowsJ2 64 65 29 340 ≤ 135729237755369 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1078 c22240R_64_10 (by norm_num)

theorem c22240R_64_8 : rowsJ2 64 65 28 340 ≤ 135729237755369 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1077 c22240R_64_9 (by norm_num)

theorem c22240R_64_7 : rowsJ2 64 65 27 340 ≤ 135729237755369 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1076 c22240R_64_8 (by norm_num)

theorem c22240R_64_6 : rowsJ2 64 65 26 340 ≤ 135733382603022 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1075 c22240R_64_7 (by norm_num)

theorem c22240R_64_5 : rowsJ2 64 65 25 340 ≤ 135741699786087 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1074 c22240R_64_6 (by norm_num)

theorem c22240R_64_4 : rowsJ2 64 65 24 340 ≤ 135758306764325 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1073 c22240R_64_5 (by norm_num)

theorem c22240R_64_3 : rowsJ2 64 65 23 340 ≤ 135783272896121 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1072 c22240R_64_4 (by norm_num)

theorem c22240R_64_2 : rowsJ2 64 65 21 340 ≤ 135870745486329 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1071 c22240R_64_3 (by norm_num)

theorem c22240R_64_1 : rowsJ2 64 65 17 340 ≤ 136252147323356 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1070 c22240R_64_2 (by norm_num)

theorem c22240R_64_0 : rowsJ2 64 65 0 340 ≤ 138642662400066 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22240R_1069 c22240R_64_1 (by norm_num)

theorem hr22240R_64 : rows2 64 65 ≤ 138642662400066 := rows2_le_of_rowsJ2 64 65 c22240R_64_0

theorem c22240R_65_44 : rowsJ2 65 66 64 340 ≤ 15750786829620 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1158 rows22240R_1159 (by norm_num)

theorem c22240R_65_43 : rowsJ2 65 66 63 340 ≤ 24312114720538 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1157 c22240R_65_44 (by norm_num)

theorem c22240R_65_42 : rowsJ2 65 66 62 340 ≤ 33331930832693 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1156 c22240R_65_43 (by norm_num)

theorem c22240R_65_41 : rowsJ2 65 66 61 340 ≤ 42799711668355 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1155 c22240R_65_42 (by norm_num)

theorem c22240R_65_40 : rowsJ2 65 66 60 340 ≤ 52720755287079 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1154 c22240R_65_41 (by norm_num)

theorem c22240R_65_39 : rowsJ2 65 66 59 340 ≤ 63150932825636 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1153 c22240R_65_40 (by norm_num)

theorem c22240R_65_38 : rowsJ2 65 66 58 340 ≤ 73599353407500 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1152 c22240R_65_39 (by norm_num)

theorem c22240R_65_37 : rowsJ2 65 66 57 340 ≤ 83579689356275 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1151 c22240R_65_38 (by norm_num)

theorem c22240R_65_36 : rowsJ2 65 66 56 340 ≤ 92858669928317 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1150 c22240R_65_37 (by norm_num)

theorem c22240R_65_35 : rowsJ2 65 66 55 340 ≤ 101254565475995 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1149 c22240R_65_36 (by norm_num)

theorem c22240R_65_34 : rowsJ2 65 66 54 340 ≤ 108813072980662 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1148 c22240R_65_35 (by norm_num)

theorem c22240R_65_33 : rowsJ2 65 66 53 340 ≤ 115492610829456 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1147 c22240R_65_34 (by norm_num)

theorem c22240R_65_32 : rowsJ2 65 66 52 340 ≤ 121070912225588 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1146 c22240R_65_33 (by norm_num)

theorem c22240R_65_31 : rowsJ2 65 66 51 340 ≤ 125375241887679 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1145 c22240R_65_32 (by norm_num)

theorem c22240R_65_30 : rowsJ2 65 66 50 340 ≤ 128646631785191 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1144 c22240R_65_31 (by norm_num)

theorem c22240R_65_29 : rowsJ2 65 66 49 340 ≤ 131044145877342 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1143 c22240R_65_30 (by norm_num)

theorem c22240R_65_28 : rowsJ2 65 66 48 340 ≤ 132598821658552 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1142 c22240R_65_29 (by norm_num)

theorem c22240R_65_27 : rowsJ2 65 66 47 340 ≤ 133412575116285 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1141 c22240R_65_28 (by norm_num)

theorem c22240R_65_26 : rowsJ2 65 66 46 340 ≤ 133793709428217 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1140 c22240R_65_27 (by norm_num)

theorem c22240R_65_25 : rowsJ2 65 66 45 340 ≤ 133989148876373 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1139 c22240R_65_26 (by norm_num)

theorem c22240R_65_24 : rowsJ2 65 66 44 340 ≤ 134055978528149 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1138 c22240R_65_25 (by norm_num)

theorem c22240R_65_23 : rowsJ2 65 66 43 340 ≤ 134055978528149 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1137 c22240R_65_24 (by norm_num)

theorem c22240R_65_22 : rowsJ2 65 66 42 340 ≤ 134055978528149 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1136 c22240R_65_23 (by norm_num)

theorem c22240R_65_21 : rowsJ2 65 66 41 340 ≤ 134055978528149 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1135 c22240R_65_22 (by norm_num)

theorem c22240R_65_20 : rowsJ2 65 66 40 340 ≤ 134055978528149 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1134 c22240R_65_21 (by norm_num)

theorem c22240R_65_19 : rowsJ2 65 66 39 340 ≤ 134055978528149 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1133 c22240R_65_20 (by norm_num)

theorem c22240R_65_18 : rowsJ2 65 66 38 340 ≤ 134055978528149 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1132 c22240R_65_19 (by norm_num)

theorem c22240R_65_17 : rowsJ2 65 66 37 340 ≤ 134055978528149 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1131 c22240R_65_18 (by norm_num)

theorem c22240R_65_16 : rowsJ2 65 66 36 340 ≤ 134055978528149 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1130 c22240R_65_17 (by norm_num)

theorem c22240R_65_15 : rowsJ2 65 66 35 340 ≤ 134055978528149 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1129 c22240R_65_16 (by norm_num)

theorem c22240R_65_14 : rowsJ2 65 66 34 340 ≤ 134055978528149 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1128 c22240R_65_15 (by norm_num)

theorem c22240R_65_13 : rowsJ2 65 66 33 340 ≤ 134055978528149 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1127 c22240R_65_14 (by norm_num)

theorem c22240R_65_12 : rowsJ2 65 66 32 340 ≤ 134055978528149 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1126 c22240R_65_13 (by norm_num)

theorem c22240R_65_11 : rowsJ2 65 66 31 340 ≤ 134055978528149 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1125 c22240R_65_12 (by norm_num)

theorem c22240R_65_10 : rowsJ2 65 66 30 340 ≤ 134055978528149 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1124 c22240R_65_11 (by norm_num)

theorem c22240R_65_9 : rowsJ2 65 66 29 340 ≤ 134055978528149 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1123 c22240R_65_10 (by norm_num)

theorem c22240R_65_8 : rowsJ2 65 66 28 340 ≤ 134055978528149 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1122 c22240R_65_9 (by norm_num)

theorem c22240R_65_7 : rowsJ2 65 66 27 340 ≤ 134055978528149 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1121 c22240R_65_8 (by norm_num)

theorem c22240R_65_6 : rowsJ2 65 66 26 340 ≤ 134055978528149 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1120 c22240R_65_7 (by norm_num)

theorem c22240R_65_5 : rowsJ2 65 66 25 340 ≤ 134060143589335 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1119 c22240R_65_6 (by norm_num)

theorem c22240R_65_4 : rowsJ2 65 66 24 340 ≤ 134068502962580 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1118 c22240R_65_5 (by norm_num)

theorem c22240R_65_3 : rowsJ2 65 66 23 340 ≤ 134085197528451 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1117 c22240R_65_4 (by norm_num)

theorem c22240R_65_2 : rowsJ2 65 66 21 340 ≤ 134147951273676 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1116 c22240R_65_3 (by norm_num)

theorem c22240R_65_1 : rowsJ2 65 66 18 340 ≤ 134349675794655 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1115 c22240R_65_2 (by norm_num)

theorem c22240R_65_0 : rowsJ2 65 66 0 340 ≤ 136686330969338 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22240R_1114 c22240R_65_1 (by norm_num)

theorem hr22240R_65 : rows2 65 66 ≤ 136686330969338 := rows2_le_of_rowsJ2 65 66 c22240R_65_0

theorem c22240R_66_45 : rowsJ2 66 67 65 340 ≤ 13001311830263 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1205 rows22240R_1206 (by norm_num)

theorem c22240R_66_44 : rowsJ2 66 67 64 340 ≤ 20166382110592 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1204 c22240R_66_45 (by norm_num)

theorem c22240R_66_43 : rowsJ2 66 67 63 340 ≤ 27730611290702 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1203 c22240R_66_44 (by norm_num)

theorem c22240R_66_42 : rowsJ2 66 67 62 340 ≤ 35750121933676 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1202 c22240R_66_43 (by norm_num)

theorem c22240R_66_41 : rowsJ2 66 67 61 340 ≤ 44163727703321 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1201 c22240R_66_42 (by norm_num)

theorem c22240R_66_40 : rowsJ2 66 67 60 340 ≤ 53027158357412 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1200 c22240R_66_41 (by norm_num)

theorem c22240R_66_39 : rowsJ2 66 67 59 340 ≤ 62345682906762 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1199 c22240R_66_40 (by norm_num)

theorem c22240R_66_38 : rowsJ2 66 67 58 340 ≤ 72175178549088 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1198 c22240R_66_39 (by norm_num)

theorem c22240R_66_37 : rowsJ2 66 67 57 340 ≤ 81602203721416 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1197 c22240R_66_38 (by norm_num)

theorem c22240R_66_36 : rowsJ2 66 67 56 340 ≤ 90441918759295 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1196 c22240R_66_37 (by norm_num)

theorem c22240R_66_35 : rowsJ2 66 67 55 340 ≤ 98462702857237 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1195 c22240R_66_36 (by norm_num)

theorem c22240R_66_34 : rowsJ2 66 67 54 340 ≤ 105756040979611 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1194 c22240R_66_35 (by norm_num)

theorem c22240R_66_33 : rowsJ2 66 67 53 340 ≤ 112230142341644 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1193 c22240R_66_34 (by norm_num)

theorem c22240R_66_32 : rowsJ2 66 67 52 340 ≤ 117710723972372 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1192 c22240R_66_33 (by norm_num)

theorem c22240R_66_31 : rowsJ2 66 67 51 340 ≤ 121976840405067 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1191 c22240R_66_32 (by norm_num)

theorem c22240R_66_30 : rowsJ2 66 67 50 340 ≤ 125219187366188 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1190 c22240R_66_31 (by norm_num)

theorem c22240R_66_29 : rowsJ2 66 67 49 340 ≤ 127595416667636 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1189 c22240R_66_30 (by norm_num)

theorem c22240R_66_28 : rowsJ2 66 67 48 340 ≤ 129136290257353 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1188 c22240R_66_29 (by norm_num)

theorem c22240R_66_27 : rowsJ2 66 67 47 340 ≤ 129942819327090 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1187 c22240R_66_28 (by norm_num)

theorem c22240R_66_26 : rowsJ2 66 67 46 340 ≤ 130320569982557 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1186 c22240R_66_27 (by norm_num)

theorem c22240R_66_25 : rowsJ2 66 67 45 340 ≤ 130514274346960 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1185 c22240R_66_26 (by norm_num)

theorem c22240R_66_24 : rowsJ2 66 67 44 340 ≤ 130580510694549 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1184 c22240R_66_25 (by norm_num)

theorem c22240R_66_23 : rowsJ2 66 67 43 340 ≤ 130580510694549 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1183 c22240R_66_24 (by norm_num)

theorem c22240R_66_22 : rowsJ2 66 67 42 340 ≤ 130580510694549 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1182 c22240R_66_23 (by norm_num)

theorem c22240R_66_21 : rowsJ2 66 67 41 340 ≤ 130580510694549 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1181 c22240R_66_22 (by norm_num)

theorem c22240R_66_20 : rowsJ2 66 67 40 340 ≤ 130580510694549 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1180 c22240R_66_21 (by norm_num)

theorem c22240R_66_19 : rowsJ2 66 67 39 340 ≤ 130580510694549 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1179 c22240R_66_20 (by norm_num)

theorem c22240R_66_18 : rowsJ2 66 67 38 340 ≤ 130580510694549 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1178 c22240R_66_19 (by norm_num)

theorem c22240R_66_17 : rowsJ2 66 67 37 340 ≤ 130580510694549 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1177 c22240R_66_18 (by norm_num)

theorem c22240R_66_16 : rowsJ2 66 67 36 340 ≤ 130580510694549 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1176 c22240R_66_17 (by norm_num)

theorem c22240R_66_15 : rowsJ2 66 67 35 340 ≤ 130580510694549 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1175 c22240R_66_16 (by norm_num)

theorem c22240R_66_14 : rowsJ2 66 67 34 340 ≤ 130580510694549 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1174 c22240R_66_15 (by norm_num)

theorem c22240R_66_13 : rowsJ2 66 67 33 340 ≤ 130580510694549 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1173 c22240R_66_14 (by norm_num)

theorem c22240R_66_12 : rowsJ2 66 67 32 340 ≤ 130580510694549 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1172 c22240R_66_13 (by norm_num)

theorem c22240R_66_11 : rowsJ2 66 67 31 340 ≤ 130580510694549 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1171 c22240R_66_12 (by norm_num)

theorem c22240R_66_10 : rowsJ2 66 67 30 340 ≤ 130580510694549 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1170 c22240R_66_11 (by norm_num)

theorem c22240R_66_9 : rowsJ2 66 67 29 340 ≤ 130580510694549 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1169 c22240R_66_10 (by norm_num)

theorem c22240R_66_8 : rowsJ2 66 67 28 340 ≤ 130580510694549 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1168 c22240R_66_9 (by norm_num)

theorem c22240R_66_7 : rowsJ2 66 67 27 340 ≤ 130580510694549 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1167 c22240R_66_8 (by norm_num)

theorem c22240R_66_6 : rowsJ2 66 67 26 340 ≤ 130580510694549 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1166 c22240R_66_7 (by norm_num)

theorem c22240R_66_5 : rowsJ2 66 67 25 340 ≤ 130580510694549 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1165 c22240R_66_6 (by norm_num)

theorem c22240R_66_4 : rowsJ2 66 67 24 340 ≤ 130584697219561 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1164 c22240R_66_5 (by norm_num)

theorem c22240R_66_3 : rowsJ2 66 67 23 340 ≤ 130593101355695 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1163 c22240R_66_4 (by norm_num)

theorem c22240R_66_2 : rowsJ2 66 67 21 340 ≤ 130635136751620 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1162 c22240R_66_3 (by norm_num)

theorem c22240R_66_1 : rowsJ2 66 67 18 340 ≤ 130791263288587 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1161 c22240R_66_2 (by norm_num)

theorem c22240R_66_0 : rowsJ2 66 67 0 340 ≤ 132947936275762 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22240R_1160 c22240R_66_1 (by norm_num)

theorem hr22240R_66 : rows2 66 67 ≤ 132947936275762 := rows2_le_of_rowsJ2 66 67 c22240R_66_0

theorem c22240R_67_46 : rowsJ2 67 68 66 340 ≤ 10562050238709 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1253 rows22240R_1254 (by norm_num)

theorem c22240R_67_45 : rowsJ2 67 68 65 340 ≤ 16452722488965 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1252 c22240R_67_46 (by norm_num)

theorem c22240R_67_44 : rowsJ2 67 68 64 340 ≤ 22750103746123 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1251 c22240R_67_45 (by norm_num)

theorem c22240R_67_43 : rowsJ2 67 68 63 340 ≤ 29444101276970 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1250 c22240R_67_44 (by norm_num)

theorem c22240R_67_42 : rowsJ2 67 68 62 340 ≤ 36538887618401 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1249 c22240R_67_43 (by norm_num)

theorem c22240R_67_41 : rowsJ2 67 68 61 340 ≤ 44025044044434 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1248 c22240R_67_42 (by norm_num)

theorem c22240R_67_40 : rowsJ2 67 68 60 340 ≤ 51907039520596 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1247 c22240R_67_41 (by norm_num)

theorem c22240R_67_39 : rowsJ2 67 68 59 340 ≤ 60240606867793 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1246 c22240R_67_40 (by norm_num)

theorem c22240R_67_38 : rowsJ2 67 68 58 340 ≤ 69031002503460 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1245 c22240R_67_39 (by norm_num)

theorem c22240R_67_37 : rowsJ2 67 68 57 340 ≤ 77904217998273 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1244 c22240R_67_38 (by norm_num)

theorem c22240R_67_36 : rowsJ2 67 68 56 340 ≤ 86255276631434 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1243 c22240R_67_37 (by norm_num)

theorem c22240R_67_35 : rowsJ2 67 68 55 340 ≤ 93901114939590 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1242 c22240R_67_36 (by norm_num)

theorem c22240R_67_34 : rowsJ2 67 68 54 340 ≤ 100880970275495 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1241 c22240R_67_35 (by norm_num)

theorem c22240R_67_33 : rowsJ2 67 68 53 340 ≤ 107150205432092 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1240 c22240R_67_34 (by norm_num)

theorem c22240R_67_32 : rowsJ2 67 68 52 340 ≤ 112485531813648 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1239 c22240R_67_33 (by norm_num)

theorem c22240R_67_31 : rowsJ2 67 68 51 340 ≤ 116714107562599 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1238 c22240R_67_32 (by norm_num)

theorem c22240R_67_30 : rowsJ2 67 68 50 340 ≤ 119927922737548 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1237 c22240R_67_31 (by norm_num)

theorem c22240R_67_29 : rowsJ2 67 68 49 340 ≤ 122283241856605 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1236 c22240R_67_30 (by norm_num)

theorem c22240R_67_28 : rowsJ2 67 68 48 340 ≤ 123810556170802 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1235 c22240R_67_29 (by norm_num)

theorem c22240R_67_27 : rowsJ2 67 68 47 340 ≤ 124609988000409 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1234 c22240R_67_28 (by norm_num)

theorem c22240R_67_26 : rowsJ2 67 68 46 340 ≤ 124984414551129 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1233 c22240R_67_27 (by norm_num)

theorem c22240R_67_25 : rowsJ2 67 68 45 340 ≤ 125176414368927 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1232 c22240R_67_26 (by norm_num)

theorem c22240R_67_24 : rowsJ2 67 68 44 340 ≤ 125242067854370 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1231 c22240R_67_25 (by norm_num)

theorem c22240R_67_23 : rowsJ2 67 68 43 340 ≤ 125242067854370 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1230 c22240R_67_24 (by norm_num)

theorem c22240R_67_22 : rowsJ2 67 68 42 340 ≤ 125242067854370 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1229 c22240R_67_23 (by norm_num)

theorem c22240R_67_21 : rowsJ2 67 68 41 340 ≤ 125242067854370 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1228 c22240R_67_22 (by norm_num)

theorem c22240R_67_20 : rowsJ2 67 68 40 340 ≤ 125242067854370 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1227 c22240R_67_21 (by norm_num)

theorem c22240R_67_19 : rowsJ2 67 68 39 340 ≤ 125242067854370 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1226 c22240R_67_20 (by norm_num)

theorem c22240R_67_18 : rowsJ2 67 68 38 340 ≤ 125242067854370 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1225 c22240R_67_19 (by norm_num)

theorem c22240R_67_17 : rowsJ2 67 68 37 340 ≤ 125242067854370 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1224 c22240R_67_18 (by norm_num)

theorem c22240R_67_16 : rowsJ2 67 68 36 340 ≤ 125242067854370 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1223 c22240R_67_17 (by norm_num)

theorem c22240R_67_15 : rowsJ2 67 68 35 340 ≤ 125242067854370 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1222 c22240R_67_16 (by norm_num)

theorem c22240R_67_14 : rowsJ2 67 68 34 340 ≤ 125242067854370 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1221 c22240R_67_15 (by norm_num)

theorem c22240R_67_13 : rowsJ2 67 68 33 340 ≤ 125242067854370 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1220 c22240R_67_14 (by norm_num)

theorem c22240R_67_12 : rowsJ2 67 68 32 340 ≤ 125242067854370 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1219 c22240R_67_13 (by norm_num)

theorem c22240R_67_11 : rowsJ2 67 68 31 340 ≤ 125242067854370 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1218 c22240R_67_12 (by norm_num)

theorem c22240R_67_10 : rowsJ2 67 68 30 340 ≤ 125242067854370 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1217 c22240R_67_11 (by norm_num)

theorem c22240R_67_9 : rowsJ2 67 68 29 340 ≤ 125242067854370 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1216 c22240R_67_10 (by norm_num)

theorem c22240R_67_8 : rowsJ2 67 68 28 340 ≤ 125242067854370 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1215 c22240R_67_9 (by norm_num)

theorem c22240R_67_7 : rowsJ2 67 68 27 340 ≤ 125242067854370 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1214 c22240R_67_8 (by norm_num)

theorem c22240R_67_6 : rowsJ2 67 68 26 340 ≤ 125242067854370 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1213 c22240R_67_7 (by norm_num)

theorem c22240R_67_5 : rowsJ2 67 68 25 340 ≤ 125242067854370 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1212 c22240R_67_6 (by norm_num)

theorem c22240R_67_4 : rowsJ2 67 68 24 340 ≤ 125242067854370 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1211 c22240R_67_5 (by norm_num)

theorem c22240R_67_3 : rowsJ2 67 68 23 340 ≤ 125246277129217 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1210 c22240R_67_4 (by norm_num)

theorem c22240R_67_2 : rowsJ2 67 68 21 340 ≤ 125271614391557 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1209 c22240R_67_3 (by norm_num)

theorem c22240R_67_1 : rowsJ2 67 68 18 340 ≤ 125386106061113 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1208 c22240R_67_2 (by norm_num)

theorem c22240R_67_0 : rowsJ2 67 68 0 340 ≤ 127367671831250 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22240R_1207 c22240R_67_1 (by norm_num)

theorem hr22240R_67 : rows2 67 68 ≤ 127367671831250 := rows2_le_of_rowsJ2 67 68 c22240R_67_0

theorem c22240R_68_47 : rowsJ2 68 69 67 340 ≤ 8296886171508 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1302 rows22240R_1303 (by norm_num)

theorem c22240R_68_46 : rowsJ2 68 69 66 340 ≤ 13033661588451 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1301 c22240R_68_47 (by norm_num)

theorem c22240R_68_45 : rowsJ2 68 69 65 340 ≤ 18118053042166 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1300 c22240R_68_46 (by norm_num)

theorem c22240R_68_44 : rowsJ2 68 69 64 340 ≤ 23606709475153 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1299 c22240R_68_45 (by norm_num)

theorem c22240R_68_43 : rowsJ2 68 69 63 340 ≤ 29437421067531 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1298 c22240R_68_44 (by norm_num)

theorem c22240R_68_42 : rowsJ2 68 69 62 340 ≤ 35666328690164 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1297 c22240R_68_43 (by norm_num)

theorem c22240R_68_41 : rowsJ2 68 69 61 340 ≤ 42232613513104 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1296 c22240R_68_42 (by norm_num)

theorem c22240R_68_40 : rowsJ2 68 69 60 340 ≤ 49191954042536 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1295 c22240R_68_41 (by norm_num)

theorem c22240R_68_39 : rowsJ2 68 69 59 340 ≤ 56548791752924 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1294 c22240R_68_40 (by norm_num)

theorem c22240R_68_38 : rowsJ2 68 69 58 340 ≤ 64358874875057 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1293 c22240R_68_39 (by norm_num)

theorem c22240R_68_37 : rowsJ2 68 69 57 340 ≤ 72627451242094 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1292 c22240R_68_38 (by norm_num)

theorem c22240R_68_36 : rowsJ2 68 69 56 340 ≤ 80489380295779 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1291 c22240R_68_37 (by norm_num)

theorem c22240R_68_35 : rowsJ2 68 69 55 340 ≤ 87710822552539 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1290 c22240R_68_36 (by norm_num)

theorem c22240R_68_34 : rowsJ2 68 69 54 340 ≤ 94377355281897 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1289 c22240R_68_35 (by norm_num)

theorem c22240R_68_33 : rowsJ2 68 69 53 340 ≤ 100393337474406 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1288 c22240R_68_34 (by norm_num)

theorem c22240R_68_32 : rowsJ2 68 69 52 340 ≤ 105583931398807 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1287 c22240R_68_33 (by norm_num)

theorem c22240R_68_31 : rowsJ2 68 69 51 340 ≤ 109727290866214 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1286 c22240R_68_32 (by norm_num)

theorem c22240R_68_30 : rowsJ2 68 69 50 340 ≤ 112913072028443 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1285 c22240R_68_31 (by norm_num)

theorem c22240R_68_29 : rowsJ2 68 69 49 340 ≤ 115247845769953 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1284 c22240R_68_30 (by norm_num)

theorem c22240R_68_28 : rowsJ2 68 69 48 340 ≤ 116761837367507 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1283 c22240R_68_29 (by norm_num)

theorem c22240R_68_27 : rowsJ2 68 69 47 340 ≤ 117554295777407 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1282 c22240R_68_28 (by norm_num)

theorem c22240R_68_26 : rowsJ2 68 69 46 340 ≤ 117925456216631 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1281 c22240R_68_27 (by norm_num)

theorem c22240R_68_25 : rowsJ2 68 69 45 340 ≤ 118115781225817 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1280 c22240R_68_26 (by norm_num)

theorem c22240R_68_24 : rowsJ2 68 69 44 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1279 c22240R_68_25 (by norm_num)

theorem c22240R_68_23 : rowsJ2 68 69 43 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1278 c22240R_68_24 (by norm_num)

theorem c22240R_68_22 : rowsJ2 68 69 42 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1277 c22240R_68_23 (by norm_num)

theorem c22240R_68_21 : rowsJ2 68 69 41 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1276 c22240R_68_22 (by norm_num)

theorem c22240R_68_20 : rowsJ2 68 69 40 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1275 c22240R_68_21 (by norm_num)

theorem c22240R_68_19 : rowsJ2 68 69 39 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1274 c22240R_68_20 (by norm_num)

theorem c22240R_68_18 : rowsJ2 68 69 38 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1273 c22240R_68_19 (by norm_num)

theorem c22240R_68_17 : rowsJ2 68 69 37 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1272 c22240R_68_18 (by norm_num)

theorem c22240R_68_16 : rowsJ2 68 69 36 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1271 c22240R_68_17 (by norm_num)

theorem c22240R_68_15 : rowsJ2 68 69 35 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1270 c22240R_68_16 (by norm_num)

theorem c22240R_68_14 : rowsJ2 68 69 34 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1269 c22240R_68_15 (by norm_num)

theorem c22240R_68_13 : rowsJ2 68 69 33 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1268 c22240R_68_14 (by norm_num)

theorem c22240R_68_12 : rowsJ2 68 69 32 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1267 c22240R_68_13 (by norm_num)

theorem c22240R_68_11 : rowsJ2 68 69 31 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1266 c22240R_68_12 (by norm_num)

theorem c22240R_68_10 : rowsJ2 68 69 30 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1265 c22240R_68_11 (by norm_num)

theorem c22240R_68_9 : rowsJ2 68 69 29 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1264 c22240R_68_10 (by norm_num)

theorem c22240R_68_8 : rowsJ2 68 69 28 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1263 c22240R_68_9 (by norm_num)

theorem c22240R_68_7 : rowsJ2 68 69 27 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1262 c22240R_68_8 (by norm_num)

theorem c22240R_68_6 : rowsJ2 68 69 26 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1261 c22240R_68_7 (by norm_num)

theorem c22240R_68_5 : rowsJ2 68 69 25 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1260 c22240R_68_6 (by norm_num)

theorem c22240R_68_4 : rowsJ2 68 69 24 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1259 c22240R_68_5 (by norm_num)

theorem c22240R_68_3 : rowsJ2 68 69 23 340 ≤ 118180862017890 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1258 c22240R_68_4 (by norm_num)

theorem c22240R_68_2 : rowsJ2 68 69 21 340 ≤ 118193597056876 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1257 c22240R_68_3 (by norm_num)

theorem c22240R_68_1 : rowsJ2 68 69 18 340 ≤ 118274517313395 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1256 c22240R_68_2 (by norm_num)

theorem c22240R_68_0 : rowsJ2 68 69 0 340 ≤ 120084804318445 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22240R_1255 c22240R_68_1 (by norm_num)

theorem hr22240R_68 : rows2 68 69 ≤ 120084804318445 := rows2_le_of_rowsJ2 68 69 c22240R_68_0

theorem c22240R_69_47 : rowsJ2 69 70 68 340 ≤ 6204682293906 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1351 rows22240R_1352 (by norm_num)

theorem c22240R_69_46 : rowsJ2 69 70 67 340 ≤ 9840639782242 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1350 c22240R_69_47 (by norm_num)

theorem c22240R_69_45 : rowsJ2 69 70 66 340 ≤ 13831882225603 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1349 c22240R_69_46 (by norm_num)

theorem c22240R_69_44 : rowsJ2 69 70 65 340 ≤ 18168950354825 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1348 c22240R_69_45 (by norm_num)

theorem c22240R_69_43 : rowsJ2 69 70 64 340 ≤ 22855010781930 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1347 c22240R_69_44 (by norm_num)

theorem c22240R_69_42 : rowsJ2 69 70 63 340 ≤ 27881210856951 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1346 c22240R_69_43 (by norm_num)

theorem c22240R_69_41 : rowsJ2 69 70 62 340 ≤ 33250974959549 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1345 c22240R_69_42 (by norm_num)

theorem c22240R_69_40 : rowsJ2 69 70 61 340 ≤ 38956034339983 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1344 c22240R_69_41 (by norm_num)

theorem c22240R_69_39 : rowsJ2 69 70 60 340 ≤ 45000069236070 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1343 c22240R_69_40 (by norm_num)

theorem c22240R_69_38 : rowsJ2 69 70 59 340 ≤ 51438758778573 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1342 c22240R_69_39 (by norm_num)

theorem c22240R_69_37 : rowsJ2 69 70 58 340 ≤ 58276520617603 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1341 c22240R_69_38 (by norm_num)

theorem c22240R_69_36 : rowsJ2 69 70 57 340 ≤ 65569130612582 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1340 c22240R_69_37 (by norm_num)

theorem c22240R_69_35 : rowsJ2 69 70 56 340 ≤ 72891118282204 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1339 c22240R_69_36 (by norm_num)

theorem c22240R_69_34 : rowsJ2 69 70 55 340 ≤ 79687715542118 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1338 c22240R_69_35 (by norm_num)

theorem c22240R_69_33 : rowsJ2 69 70 54 340 ≤ 85991448270919 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1337 c22240R_69_34 (by norm_num)

theorem c22240R_69_32 : rowsJ2 69 70 53 340 ≤ 91754352138278 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1336 c22240R_69_33 (by norm_num)

theorem c22240R_69_31 : rowsJ2 69 70 52 340 ≤ 96751745208850 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1335 c22240R_69_32 (by norm_num)

theorem c22240R_69_30 : rowsJ2 69 70 51 340 ≤ 100810365546593 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1334 c22240R_69_31 (by norm_num)

theorem c22240R_69_29 : rowsJ2 69 70 50 340 ≤ 103968597555520 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1333 c22240R_69_30 (by norm_num)

theorem c22240R_69_28 : rowsJ2 69 70 49 340 ≤ 106283181259973 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1332 c22240R_69_29 (by norm_num)

theorem c22240R_69_27 : rowsJ2 69 70 48 340 ≤ 107784080562582 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1331 c22240R_69_28 (by norm_num)

theorem c22240R_69_26 : rowsJ2 69 70 47 340 ≤ 108569686160845 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1330 c22240R_69_27 (by norm_num)

theorem c22240R_69_25 : rowsJ2 69 70 46 340 ≤ 108937636977275 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1329 c22240R_69_26 (by norm_num)

theorem c22240R_69_24 : rowsJ2 69 70 45 340 ≤ 109126316144330 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1328 c22240R_69_25 (by norm_num)

theorem c22240R_69_23 : rowsJ2 69 70 44 340 ≤ 109190834147992 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1327 c22240R_69_24 (by norm_num)

theorem c22240R_69_22 : rowsJ2 69 70 43 340 ≤ 109190834147992 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1326 c22240R_69_23 (by norm_num)

theorem c22240R_69_21 : rowsJ2 69 70 42 340 ≤ 109190834147992 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1325 c22240R_69_22 (by norm_num)

theorem c22240R_69_20 : rowsJ2 69 70 41 340 ≤ 109190834147992 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1324 c22240R_69_21 (by norm_num)

theorem c22240R_69_19 : rowsJ2 69 70 40 340 ≤ 109190834147992 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1323 c22240R_69_20 (by norm_num)

theorem c22240R_69_18 : rowsJ2 69 70 38 340 ≤ 109190834147992 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1322 c22240R_69_19 (by norm_num)

theorem c22240R_69_17 : rowsJ2 69 70 37 340 ≤ 109190834147992 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1321 c22240R_69_18 (by norm_num)

theorem c22240R_69_16 : rowsJ2 69 70 36 340 ≤ 109190834147992 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1320 c22240R_69_17 (by norm_num)

theorem c22240R_69_15 : rowsJ2 69 70 35 340 ≤ 109190834147992 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1319 c22240R_69_16 (by norm_num)

theorem c22240R_69_14 : rowsJ2 69 70 34 340 ≤ 109190834147992 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1318 c22240R_69_15 (by norm_num)

theorem c22240R_69_13 : rowsJ2 69 70 33 340 ≤ 109190834147992 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1317 c22240R_69_14 (by norm_num)

theorem c22240R_69_12 : rowsJ2 69 70 32 340 ≤ 109190834147992 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1316 c22240R_69_13 (by norm_num)

theorem c22240R_69_11 : rowsJ2 69 70 31 340 ≤ 109190834147992 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1315 c22240R_69_12 (by norm_num)

theorem c22240R_69_10 : rowsJ2 69 70 30 340 ≤ 109190834147992 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1314 c22240R_69_11 (by norm_num)

theorem c22240R_69_9 : rowsJ2 69 70 29 340 ≤ 109190834147992 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1313 c22240R_69_10 (by norm_num)

theorem c22240R_69_8 : rowsJ2 69 70 28 340 ≤ 109190834147992 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1312 c22240R_69_9 (by norm_num)

theorem c22240R_69_7 : rowsJ2 69 70 27 340 ≤ 109190834147992 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1311 c22240R_69_8 (by norm_num)

theorem c22240R_69_6 : rowsJ2 69 70 26 340 ≤ 109190834147992 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1310 c22240R_69_7 (by norm_num)

theorem c22240R_69_5 : rowsJ2 69 70 25 340 ≤ 109190834147992 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1309 c22240R_69_6 (by norm_num)

theorem c22240R_69_4 : rowsJ2 69 70 24 340 ≤ 109190834147992 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1308 c22240R_69_5 (by norm_num)

theorem c22240R_69_3 : rowsJ2 69 70 23 340 ≤ 109190834147992 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1307 c22240R_69_4 (by norm_num)

theorem c22240R_69_2 : rowsJ2 69 70 21 340 ≤ 109195092937188 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1306 c22240R_69_3 (by norm_num)

theorem c22240R_69_1 : rowsJ2 69 70 18 340 ≤ 109246481297971 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1305 c22240R_69_2 (by norm_num)

theorem c22240R_69_0 : rowsJ2 69 70 0 340 ≤ 110886972786040 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22240R_1304 c22240R_69_1 (by norm_num)

theorem hr22240R_69 : rows2 69 70 ≤ 110886972786040 := rows2_le_of_rowsJ2 69 70 c22240R_69_0

theorem c22240R_70_47 : rowsJ2 70 71 69 340 ≤ 4285978043123 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1400 rows22240R_1401 (by norm_num)

theorem c22240R_70_46 : rowsJ2 70 71 68 340 ≤ 6941081447535 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1399 c22240R_70_47 (by norm_num)

theorem c22240R_70_45 : rowsJ2 70 71 67 340 ≤ 9892288291861 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1398 c22240R_70_46 (by norm_num)

theorem c22240R_70_44 : rowsJ2 70 71 66 340 ≤ 13197039073443 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1397 c22240R_70_45 (by norm_num)

theorem c22240R_70_43 : rowsJ2 70 71 65 340 ≤ 16792135829418 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1396 c22240R_70_44 (by norm_num)

theorem c22240R_70_42 : rowsJ2 70 71 64 340 ≤ 20734392421670 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1395 c22240R_70_43 (by norm_num)

theorem c22240R_70_41 : rowsJ2 70 71 63 340 ≤ 24962013943906 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1394 c22240R_70_42 (by norm_num)

theorem c22240R_70_40 : rowsJ2 70 71 62 340 ≤ 29531234126632 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1393 c22240R_70_41 (by norm_num)

theorem c22240R_70_39 : rowsJ2 70 71 61 340 ≤ 34381589826497 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1392 c22240R_70_40 (by norm_num)

theorem c22240R_70_38 : rowsJ2 70 71 60 340 ≤ 39568781478730 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1391 c22240R_70_39 (by norm_num)

theorem c22240R_70_37 : rowsJ2 70 71 59 340 ≤ 45096451087379 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1390 c22240R_70_38 (by norm_num)

theorem c22240R_70_36 : rowsJ2 70 71 58 340 ≤ 51020290262503 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1389 c22240R_70_37 (by norm_num)

theorem c22240R_70_35 : rowsJ2 70 71 57 340 ≤ 57344696329421 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1388 c22240R_70_36 (by norm_num)

theorem c22240R_70_34 : rowsJ2 70 71 56 340 ≤ 64125484884273 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1387 c22240R_70_35 (by norm_num)

theorem c22240R_70_33 : rowsJ2 70 71 55 340 ≤ 70446431480137 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1386 c22240R_70_34 (by norm_num)

theorem c22240R_70_32 : rowsJ2 70 71 54 340 ≤ 76386978038467 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1385 c22240R_70_33 (by norm_num)

theorem c22240R_70_31 : rowsJ2 70 71 53 340 ≤ 81847308611941 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1384 c22240R_70_32 (by norm_num)

theorem c22240R_70_30 : rowsJ2 70 71 52 340 ≤ 86651689354994 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1383 c22240R_70_31 (by norm_num)

theorem c22240R_70_29 : rowsJ2 70 71 51 340 ≤ 90577012554869 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1382 c22240R_70_30 (by norm_num)

theorem c22240R_70_28 : rowsJ2 70 71 50 340 ≤ 93708167798779 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1381 c22240R_70_29 (by norm_num)

theorem c22240R_70_27 : rowsJ2 70 71 49 340 ≤ 96002907666901 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1380 c22240R_70_28 (by norm_num)

theorem c22240R_70_26 : rowsJ2 70 71 48 340 ≤ 97490939169546 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1379 c22240R_70_27 (by norm_num)

theorem c22240R_70_25 : rowsJ2 70 71 47 340 ≤ 98269809462069 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1378 c22240R_70_26 (by norm_num)

theorem c22240R_70_24 : rowsJ2 70 71 46 340 ≤ 98634605691449 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1377 c22240R_70_25 (by norm_num)

theorem c22240R_70_23 : rowsJ2 70 71 45 340 ≤ 98821667237806 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1376 c22240R_70_24 (by norm_num)

theorem c22240R_70_22 : rowsJ2 70 71 44 340 ≤ 98885632103250 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1375 c22240R_70_23 (by norm_num)

theorem c22240R_70_21 : rowsJ2 70 71 43 340 ≤ 98885632103250 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1374 c22240R_70_22 (by norm_num)

theorem c22240R_70_20 : rowsJ2 70 71 42 340 ≤ 98885632103250 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1373 c22240R_70_21 (by norm_num)

theorem c22240R_70_19 : rowsJ2 70 71 40 340 ≤ 98885632103250 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1372 c22240R_70_20 (by norm_num)

theorem c22240R_70_18 : rowsJ2 70 71 38 340 ≤ 98885632103250 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1371 c22240R_70_19 (by norm_num)

theorem c22240R_70_17 : rowsJ2 70 71 36 340 ≤ 98885632103250 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1370 c22240R_70_18 (by norm_num)

theorem c22240R_70_16 : rowsJ2 70 71 35 340 ≤ 98885632103250 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1369 c22240R_70_17 (by norm_num)

theorem c22240R_70_15 : rowsJ2 70 71 34 340 ≤ 98885632103250 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1368 c22240R_70_16 (by norm_num)

theorem c22240R_70_14 : rowsJ2 70 71 33 340 ≤ 98885632103250 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1367 c22240R_70_15 (by norm_num)

theorem c22240R_70_13 : rowsJ2 70 71 32 340 ≤ 98885632103250 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1366 c22240R_70_14 (by norm_num)

theorem c22240R_70_12 : rowsJ2 70 71 31 340 ≤ 98885632103250 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1365 c22240R_70_13 (by norm_num)

theorem c22240R_70_11 : rowsJ2 70 71 30 340 ≤ 98885632103250 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1364 c22240R_70_12 (by norm_num)

theorem c22240R_70_10 : rowsJ2 70 71 29 340 ≤ 98885632103250 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1363 c22240R_70_11 (by norm_num)

theorem c22240R_70_9 : rowsJ2 70 71 28 340 ≤ 98885632103250 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1362 c22240R_70_10 (by norm_num)

theorem c22240R_70_8 : rowsJ2 70 71 27 340 ≤ 98885632103250 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1361 c22240R_70_9 (by norm_num)

theorem c22240R_70_7 : rowsJ2 70 71 26 340 ≤ 98885632103250 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1360 c22240R_70_8 (by norm_num)

theorem c22240R_70_6 : rowsJ2 70 71 25 340 ≤ 98885632103250 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1359 c22240R_70_7 (by norm_num)

theorem c22240R_70_5 : rowsJ2 70 71 24 340 ≤ 98885632103250 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1358 c22240R_70_6 (by norm_num)

theorem c22240R_70_4 : rowsJ2 70 71 23 340 ≤ 98885632103250 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1357 c22240R_70_5 (by norm_num)

theorem c22240R_70_3 : rowsJ2 70 71 22 340 ≤ 98885632103250 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1356 c22240R_70_4 (by norm_num)

theorem c22240R_70_2 : rowsJ2 70 71 21 340 ≤ 98885632103250 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1355 c22240R_70_3 (by norm_num)

theorem c22240R_70_1 : rowsJ2 70 71 18 340 ≤ 98915743241554 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1354 c22240R_70_2 (by norm_num)

theorem c22240R_70_0 : rowsJ2 70 71 0 340 ≤ 100395270455026 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22240R_1353 c22240R_70_1 (by norm_num)

theorem hr22240R_70 : rows2 70 71 ≤ 100395270455026 := rows2_le_of_rowsJ2 70 71 c22240R_70_0

theorem c22240R_71_48 : rowsJ2 71 72 70 340 ≤ 2608124166162 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1450 rows22240R_1451 (by norm_num)

theorem c22240R_71_47 : rowsJ2 71 72 69 340 ≤ 4335248553928 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1449 c22240R_71_48 (by norm_num)

theorem c22240R_71_46 : rowsJ2 71 72 68 340 ≤ 6365954417868 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1448 c22240R_71_47 (by norm_num)

theorem c22240R_71_45 : rowsJ2 71 72 67 340 ≤ 8691617306730 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1447 c22240R_71_46 (by norm_num)

theorem c22240R_71_44 : rowsJ2 71 72 66 340 ≤ 11314500562923 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1446 c22240R_71_45 (by norm_num)

theorem c22240R_71_43 : rowsJ2 71 72 65 340 ≤ 14226515646383 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1445 c22240R_71_44 (by norm_num)

theorem c22240R_71_42 : rowsJ2 71 72 64 340 ≤ 17430148147232 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1444 c22240R_71_43 (by norm_num)

theorem c22240R_71_41 : rowsJ2 71 72 63 340 ≤ 20917822436994 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1443 c22240R_71_42 (by norm_num)

theorem c22240R_71_40 : rowsJ2 71 72 62 340 ≤ 24692242020942 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1442 c22240R_71_41 (by norm_num)

theorem c22240R_71_39 : rowsJ2 71 72 61 340 ≤ 28746324106597 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1441 c22240R_71_40 (by norm_num)

theorem c22240R_71_38 : rowsJ2 71 72 60 340 ≤ 33082987666284 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1440 c22240R_71_39 (by norm_num)

theorem c22240R_71_37 : rowsJ2 71 72 59 340 ≤ 37757931307591 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1439 c22240R_71_38 (by norm_num)

theorem c22240R_71_36 : rowsJ2 71 72 58 340 ≤ 42774761983278 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1438 c22240R_71_37 (by norm_num)

theorem c22240R_71_35 : rowsJ2 71 72 57 340 ≤ 48189195505673 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1437 c22240R_71_36 (by norm_num)

theorem c22240R_71_34 : rowsJ2 71 72 56 340 ≤ 54005612216060 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1436 c22240R_71_35 (by norm_num)

theorem c22240R_71_33 : rowsJ2 71 72 55 340 ≤ 59849749519739 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1435 c22240R_71_34 (by norm_num)

theorem c22240R_71_32 : rowsJ2 71 72 54 340 ≤ 65376337925958 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1434 c22240R_71_33 (by norm_num)

theorem c22240R_71_31 : rowsJ2 71 72 53 340 ≤ 70533788401231 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1433 c22240R_71_32 (by norm_num)

theorem c22240R_71_30 : rowsJ2 71 72 52 340 ≤ 75095633862238 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1432 c22240R_71_31 (by norm_num)

theorem c22240R_71_29 : rowsJ2 71 72 51 340 ≤ 78887862201950 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1431 c22240R_71_30 (by norm_num)

theorem c22240R_71_28 : rowsJ2 71 72 50 340 ≤ 81943323100974 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1430 c22240R_71_29 (by norm_num)

theorem c22240R_71_27 : rowsJ2 71 72 49 340 ≤ 84218556504521 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1429 c22240R_71_28 (by norm_num)

theorem c22240R_71_26 : rowsJ2 71 72 48 340 ≤ 85693938977005 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1428 c22240R_71_27 (by norm_num)

theorem c22240R_71_25 : rowsJ2 71 72 47 340 ≤ 86466188472990 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1427 c22240R_71_26 (by norm_num)

theorem c22240R_71_24 : rowsJ2 71 72 46 340 ≤ 86827883747519 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1426 c22240R_71_25 (by norm_num)

theorem c22240R_71_23 : rowsJ2 71 72 45 340 ≤ 87013355174892 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1425 c22240R_71_24 (by norm_num)

theorem c22240R_71_22 : rowsJ2 71 72 44 340 ≤ 87076776306208 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1424 c22240R_71_23 (by norm_num)

theorem c22240R_71_21 : rowsJ2 71 72 43 340 ≤ 87076776306208 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1423 c22240R_71_22 (by norm_num)

theorem c22240R_71_20 : rowsJ2 71 72 42 340 ≤ 87076776306208 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1422 c22240R_71_21 (by norm_num)

theorem c22240R_71_19 : rowsJ2 71 72 41 340 ≤ 87076776306208 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1421 c22240R_71_20 (by norm_num)

theorem c22240R_71_18 : rowsJ2 71 72 39 340 ≤ 87076776306208 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1420 c22240R_71_19 (by norm_num)

theorem c22240R_71_17 : rowsJ2 71 72 37 340 ≤ 87076776306208 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1419 c22240R_71_18 (by norm_num)

theorem c22240R_71_16 : rowsJ2 71 72 35 340 ≤ 87076776306208 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1418 c22240R_71_17 (by norm_num)

theorem c22240R_71_15 : rowsJ2 71 72 34 340 ≤ 87076776306208 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1417 c22240R_71_16 (by norm_num)

theorem c22240R_71_14 : rowsJ2 71 72 33 340 ≤ 87076776306208 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1416 c22240R_71_15 (by norm_num)

theorem c22240R_71_13 : rowsJ2 71 72 32 340 ≤ 87076776306208 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1415 c22240R_71_14 (by norm_num)

theorem c22240R_71_12 : rowsJ2 71 72 31 340 ≤ 87076776306208 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1414 c22240R_71_13 (by norm_num)

theorem c22240R_71_11 : rowsJ2 71 72 30 340 ≤ 87076776306208 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1413 c22240R_71_12 (by norm_num)

theorem c22240R_71_10 : rowsJ2 71 72 29 340 ≤ 87076776306208 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1412 c22240R_71_11 (by norm_num)

theorem c22240R_71_9 : rowsJ2 71 72 28 340 ≤ 87076776306208 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1411 c22240R_71_10 (by norm_num)

theorem c22240R_71_8 : rowsJ2 71 72 27 340 ≤ 87076776306208 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1410 c22240R_71_9 (by norm_num)

theorem c22240R_71_7 : rowsJ2 71 72 26 340 ≤ 87076776306208 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1409 c22240R_71_8 (by norm_num)

theorem c22240R_71_6 : rowsJ2 71 72 25 340 ≤ 87076776306208 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1408 c22240R_71_7 (by norm_num)

theorem c22240R_71_5 : rowsJ2 71 72 24 340 ≤ 87076776306208 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1407 c22240R_71_6 (by norm_num)

theorem c22240R_71_4 : rowsJ2 71 72 23 340 ≤ 87076776306208 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1406 c22240R_71_5 (by norm_num)

theorem c22240R_71_3 : rowsJ2 71 72 22 340 ≤ 87076776306208 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1405 c22240R_71_4 (by norm_num)

theorem c22240R_71_2 : rowsJ2 71 72 21 340 ≤ 87076776306208 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1404 c22240R_71_3 (by norm_num)

theorem c22240R_71_1 : rowsJ2 71 72 18 340 ≤ 87089759666135 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1403 c22240R_71_2 (by norm_num)

theorem c22240R_71_0 : rowsJ2 71 72 0 340 ≤ 88413796280685 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22240R_1402 c22240R_71_1 (by norm_num)

theorem hr22240R_71 : rows2 71 72 ≤ 88413796280685 := rows2_le_of_rowsJ2 71 72 c22240R_71_0

theorem c22240R_72_48 : rowsJ2 72 73 71 340 ≤ 1305401392351 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1500 rows22240R_1501 (by norm_num)

theorem c22240R_72_47 : rowsJ2 72 73 70 340 ≤ 2291958931741 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1499 c22240R_72_48 (by norm_num)

theorem c22240R_72_46 : rowsJ2 72 73 69 340 ≤ 3522257201772 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1498 c22240R_72_47 (by norm_num)

theorem c22240R_72_45 : rowsJ2 72 73 68 340 ≤ 5054820107228 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1497 c22240R_72_46 (by norm_num)

theorem c22240R_72_44 : rowsJ2 72 73 67 340 ≤ 6825508081846 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1496 c22240R_72_45 (by norm_num)

theorem c22240R_72_43 : rowsJ2 72 73 66 340 ≤ 8892093675224 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1495 c22240R_72_44 (by norm_num)

theorem c22240R_72_42 : rowsJ2 72 73 65 340 ≤ 11191855684833 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1494 c22240R_72_43 (by norm_num)

theorem c22240R_72_41 : rowsJ2 72 73 64 340 ≤ 13781863928027 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1493 c22240R_72_42 (by norm_num)

theorem c22240R_72_40 : rowsJ2 72 73 63 340 ≤ 16600740583340 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1492 c22240R_72_41 (by norm_num)

theorem c22240R_72_39 : rowsJ2 72 73 62 340 ≤ 19704901141843 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1491 c22240R_72_40 (by norm_num)

theorem c22240R_72_38 : rowsJ2 72 73 61 340 ≤ 23034240776576 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1490 c22240R_72_39 (by norm_num)

theorem c22240R_72_37 : rowsJ2 72 73 60 340 ≤ 26644568945817 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1489 c22240R_72_38 (by norm_num)

theorem c22240R_72_36 : rowsJ2 72 73 59 340 ≤ 30538768402425 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1488 c22240R_72_37 (by norm_num)

theorem c22240R_72_35 : rowsJ2 72 73 58 340 ≤ 34772560018570 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1487 c22240R_72_36 (by norm_num)

theorem c22240R_72_34 : rowsJ2 72 73 57 340 ≤ 39349531359560 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1486 c22240R_72_35 (by norm_num)

theorem c22240R_72_33 : rowsJ2 72 73 56 340 ≤ 44325446677917 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1485 c22240R_72_34 (by norm_num)

theorem c22240R_72_32 : rowsJ2 72 73 55 340 ≤ 49640473070778 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1484 c22240R_72_33 (by norm_num)

theorem c22240R_72_31 : rowsJ2 72 73 54 340 ≤ 54752077667226 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1483 c22240R_72_32 (by norm_num)

theorem c22240R_72_30 : rowsJ2 72 73 53 340 ≤ 59555915940906 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1482 c22240R_72_31 (by norm_num)

theorem c22240R_72_29 : rowsJ2 72 73 52 340 ≤ 63874995961883 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1481 c22240R_72_30 (by norm_num)

theorem c22240R_72_28 : rowsJ2 72 73 51 340 ≤ 67484568505878 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1480 c22240R_72_29 (by norm_num)

theorem c22240R_72_27 : rowsJ2 72 73 50 340 ≤ 70464588144811 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1479 c22240R_72_28 (by norm_num)

theorem c22240R_72_26 : rowsJ2 72 73 49 340 ≤ 72720643924237 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1478 c22240R_72_27 (by norm_num)

theorem c22240R_72_25 : rowsJ2 72 73 48 340 ≤ 74183590604225 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1477 c22240R_72_26 (by norm_num)

theorem c22240R_72_24 : rowsJ2 72 73 47 340 ≤ 74949330917227 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1476 c22240R_72_25 (by norm_num)

theorem c22240R_72_23 : rowsJ2 72 73 46 340 ≤ 75307977512878 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1475 c22240R_72_24 (by norm_num)

theorem c22240R_72_22 : rowsJ2 72 73 45 340 ≤ 75491885627532 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1474 c22240R_72_23 (by norm_num)

theorem c22240R_72_21 : rowsJ2 72 73 44 340 ≤ 75554772191002 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1473 c22240R_72_22 (by norm_num)

theorem c22240R_72_20 : rowsJ2 72 73 43 340 ≤ 75554772191002 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1472 c22240R_72_21 (by norm_num)

theorem c22240R_72_19 : rowsJ2 72 73 42 340 ≤ 75554772191002 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1471 c22240R_72_20 (by norm_num)

theorem c22240R_72_18 : rowsJ2 72 73 40 340 ≤ 75554772191002 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1470 c22240R_72_19 (by norm_num)

theorem c22240R_72_17 : rowsJ2 72 73 38 340 ≤ 75554772191002 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1469 c22240R_72_18 (by norm_num)

theorem c22240R_72_16 : rowsJ2 72 73 36 340 ≤ 75554772191002 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1468 c22240R_72_17 (by norm_num)

theorem c22240R_72_15 : rowsJ2 72 73 34 340 ≤ 75554772191002 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1467 c22240R_72_16 (by norm_num)

theorem c22240R_72_14 : rowsJ2 72 73 33 340 ≤ 75554772191002 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1466 c22240R_72_15 (by norm_num)

theorem c22240R_72_13 : rowsJ2 72 73 32 340 ≤ 75554772191002 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1465 c22240R_72_14 (by norm_num)

theorem c22240R_72_12 : rowsJ2 72 73 31 340 ≤ 75554772191002 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1464 c22240R_72_13 (by norm_num)

theorem c22240R_72_11 : rowsJ2 72 73 30 340 ≤ 75554772191002 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1463 c22240R_72_12 (by norm_num)

theorem c22240R_72_10 : rowsJ2 72 73 29 340 ≤ 75554772191002 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1462 c22240R_72_11 (by norm_num)

theorem c22240R_72_9 : rowsJ2 72 73 28 340 ≤ 75554772191002 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1461 c22240R_72_10 (by norm_num)

theorem c22240R_72_8 : rowsJ2 72 73 27 340 ≤ 75554772191002 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1460 c22240R_72_9 (by norm_num)

theorem c22240R_72_7 : rowsJ2 72 73 26 340 ≤ 75554772191002 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1459 c22240R_72_8 (by norm_num)

theorem c22240R_72_6 : rowsJ2 72 73 25 340 ≤ 75554772191002 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1458 c22240R_72_7 (by norm_num)

theorem c22240R_72_5 : rowsJ2 72 73 24 340 ≤ 75554772191002 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1457 c22240R_72_6 (by norm_num)

theorem c22240R_72_4 : rowsJ2 72 73 23 340 ≤ 75554772191002 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1456 c22240R_72_5 (by norm_num)

theorem c22240R_72_3 : rowsJ2 72 73 22 340 ≤ 75554772191002 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1455 c22240R_72_4 (by norm_num)

theorem c22240R_72_2 : rowsJ2 72 73 21 340 ≤ 75554772191002 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1454 c22240R_72_3 (by norm_num)

theorem c22240R_72_1 : rowsJ2 72 73 18 340 ≤ 75559115956066 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1453 c22240R_72_2 (by norm_num)

theorem c22240R_72_0 : rowsJ2 72 73 0 340 ≤ 76733109506435 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22240R_1452 c22240R_72_1 (by norm_num)

theorem hr22240R_72 : rows2 72 73 ≤ 76733109506435 := rows2_le_of_rowsJ2 72 73 c22240R_72_0

theorem c22240R_73_49 : rowsJ2 73 74 72 340 ≤ 375457977132 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1551 rows22240R_1552 (by norm_num)

theorem c22240R_73_48 : rowsJ2 73 74 71 340 ≤ 807399901453 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1550 c22240R_73_49 (by norm_num)

theorem c22240R_73_47 : rowsJ2 73 74 70 340 ≤ 1423050446720 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1549 c22240R_73_48 (by norm_num)

theorem c22240R_73_46 : rowsJ2 73 74 69 340 ≤ 2281449880497 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1548 c22240R_73_47 (by norm_num)

theorem c22240R_73_45 : rowsJ2 73 74 68 340 ≤ 3384101185962 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1547 c22240R_73_46 (by norm_num)

theorem c22240R_73_44 : rowsJ2 73 74 67 340 ≤ 4723932679162 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1546 c22240R_73_45 (by norm_num)

theorem c22240R_73_43 : rowsJ2 73 74 66 340 ≤ 6302634520684 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1545 c22240R_73_44 (by norm_num)

theorem c22240R_73_42 : rowsJ2 73 74 65 340 ≤ 8113571244426 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1544 c22240R_73_43 (by norm_num)

theorem c22240R_73_41 : rowsJ2 73 74 64 340 ≤ 10158614360201 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1543 c22240R_73_42 (by norm_num)

theorem c22240R_73_40 : rowsJ2 73 74 63 340 ≤ 12431545214856 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1542 c22240R_73_41 (by norm_num)

theorem c22240R_73_39 : rowsJ2 73 74 62 340 ≤ 14934412469108 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1541 c22240R_73_40 (by norm_num)

theorem c22240R_73_38 : rowsJ2 73 74 61 340 ≤ 17661397287745 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1540 c22240R_73_39 (by norm_num)

theorem c22240R_73_37 : rowsJ2 73 74 60 340 ≤ 20614722837088 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1539 c22240R_73_38 (by norm_num)

theorem c22240R_73_36 : rowsJ2 73 74 59 340 ≤ 23850219692755 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1538 c22240R_73_37 (by norm_num)

theorem c22240R_73_35 : rowsJ2 73 74 58 340 ≤ 27370749603424 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1537 c22240R_73_36 (by norm_num)

theorem c22240R_73_34 : rowsJ2 73 74 57 340 ≤ 31232079433411 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1536 c22240R_73_35 (by norm_num)

theorem c22240R_73_33 : rowsJ2 73 74 56 340 ≤ 35437792652917 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1535 c22240R_73_34 (by norm_num)

theorem c22240R_73_32 : rowsJ2 73 74 55 340 ≤ 39980050566022 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1534 c22240R_73_33 (by norm_num)

theorem c22240R_73_31 : rowsJ2 73 74 54 340 ≤ 44624466447410 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1533 c22240R_73_32 (by norm_num)

theorem c22240R_73_30 : rowsJ2 73 74 53 340 ≤ 49073813058346 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1532 c22240R_73_31 (by norm_num)

theorem c22240R_73_29 : rowsJ2 73 74 52 340 ≤ 53099422797656 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1531 c22240R_73_30 (by norm_num)

theorem c22240R_73_28 : rowsJ2 73 74 51 340 ≤ 56526183866591 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1530 c22240R_73_29 (by norm_num)

theorem c22240R_73_27 : rowsJ2 73 74 50 340 ≤ 59381189570402 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1529 c22240R_73_28 (by norm_num)

theorem c22240R_73_26 : rowsJ2 73 74 49 340 ≤ 61618388320135 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1528 c22240R_73_27 (by norm_num)

theorem c22240R_73_25 : rowsJ2 73 74 48 340 ≤ 63069107098120 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1527 c22240R_73_26 (by norm_num)

theorem c22240R_73_24 : rowsJ2 73 74 47 340 ≤ 63828447042855 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1526 c22240R_73_25 (by norm_num)

theorem c22240R_73_23 : rowsJ2 73 74 46 340 ≤ 64184095924722 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1525 c22240R_73_24 (by norm_num)

theorem c22240R_73_22 : rowsJ2 73 74 45 340 ≤ 64366466860725 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1524 c22240R_73_23 (by norm_num)

theorem c22240R_73_21 : rowsJ2 73 74 44 340 ≤ 64428827792779 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1523 c22240R_73_22 (by norm_num)

theorem c22240R_73_20 : rowsJ2 73 74 43 340 ≤ 64428827792779 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1522 c22240R_73_21 (by norm_num)

theorem c22240R_73_19 : rowsJ2 73 74 42 340 ≤ 64428827792779 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1521 c22240R_73_20 (by norm_num)

theorem c22240R_73_18 : rowsJ2 73 74 41 340 ≤ 64428827792779 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1520 c22240R_73_19 (by norm_num)

theorem c22240R_73_17 : rowsJ2 73 74 39 340 ≤ 64428827792779 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1519 c22240R_73_18 (by norm_num)

theorem c22240R_73_16 : rowsJ2 73 74 37 340 ≤ 64428827792779 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1518 c22240R_73_17 (by norm_num)

theorem c22240R_73_15 : rowsJ2 73 74 35 340 ≤ 64428827792779 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1517 c22240R_73_16 (by norm_num)

theorem c22240R_73_14 : rowsJ2 73 74 33 340 ≤ 64428827792779 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1516 c22240R_73_15 (by norm_num)

theorem c22240R_73_13 : rowsJ2 73 74 32 340 ≤ 64428827792779 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1515 c22240R_73_14 (by norm_num)

theorem c22240R_73_12 : rowsJ2 73 74 31 340 ≤ 64428827792779 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1514 c22240R_73_13 (by norm_num)

theorem c22240R_73_11 : rowsJ2 73 74 30 340 ≤ 64429795052376 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1513 c22240R_73_12 (by norm_num)

theorem c22240R_73_10 : rowsJ2 73 74 29 340 ≤ 64430759699280 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1512 c22240R_73_11 (by norm_num)

theorem c22240R_73_9 : rowsJ2 73 74 28 340 ≤ 64432684355914 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1511 c22240R_73_10 (by norm_num)

theorem c22240R_73_8 : rowsJ2 73 74 27 340 ≤ 64434605198409 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1510 c22240R_73_9 (by norm_num)

theorem c22240R_73_7 : rowsJ2 73 74 26 340 ≤ 64438378481395 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1509 c22240R_73_8 (by norm_num)

theorem c22240R_73_6 : rowsJ2 73 74 25 340 ≤ 64442146371304 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1508 c22240R_73_7 (by norm_num)

theorem c22240R_73_5 : rowsJ2 73 74 24 340 ≤ 64447759888198 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1507 c22240R_73_6 (by norm_num)

theorem c22240R_73_4 : rowsJ2 73 74 23 340 ≤ 64453369204982 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1506 c22240R_73_5 (by norm_num)

theorem c22240R_73_3 : rowsJ2 73 74 22 340 ≤ 64459939457609 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1505 c22240R_73_4 (by norm_num)

theorem c22240R_73_2 : rowsJ2 73 74 21 340 ≤ 64464598544993 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1504 c22240R_73_3 (by norm_num)

theorem c22240R_73_1 : rowsJ2 73 74 18 340 ≤ 64466379795862 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1503 c22240R_73_2 (by norm_num)

theorem c22240R_73_0 : rowsJ2 73 74 0 340 ≤ 65501103101660 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22240R_1502 c22240R_73_1 (by norm_num)

theorem hr22240R_73 : rows2 73 74 ≤ 65501103101660 := rows2_le_of_rowsJ2 73 74 c22240R_73_0

theorem c22240R_74_49 : rowsJ2 74 75 73 340 ≤ 0 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1602 rows22240R_1603 (by norm_num)

theorem c22240R_74_48 : rowsJ2 74 75 72 340 ≤ 62341027845 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1601 c22240R_74_49 (by norm_num)

theorem c22240R_74_47 : rowsJ2 74 75 71 340 ≤ 247974005729 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1600 c22240R_74_48 (by norm_num)

theorem c22240R_74_46 : rowsJ2 74 75 70 340 ≤ 616570458663 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1599 c22240R_74_47 (by norm_num)

theorem c22240R_74_45 : rowsJ2 74 75 69 340 ≤ 1169158555440 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1598 c22240R_74_46 (by norm_num)

theorem c22240R_74_44 : rowsJ2 74 75 68 340 ≤ 1964814015011 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1597 c22240R_74_45 (by norm_num)

theorem c22240R_74_43 : rowsJ2 74 75 67 340 ≤ 2939980599600 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1596 c22240R_74_44 (by norm_num)

theorem c22240R_74_42 : rowsJ2 74 75 66 340 ≤ 4152899713242 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1595 c22240R_74_43 (by norm_num)

theorem c22240R_74_41 : rowsJ2 74 75 65 340 ≤ 5541371203300 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1594 c22240R_74_42 (by norm_num)

theorem c22240R_74_40 : rowsJ2 74 75 64 340 ≤ 7162853751901 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1593 c22240R_74_41 (by norm_num)

theorem c22240R_74_39 : rowsJ2 74 75 63 340 ≤ 8956429996354 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1592 c22240R_74_40 (by norm_num)

theorem c22240R_74_38 : rowsJ2 74 75 62 340 ≤ 10978826778188 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1591 c22240R_74_39 (by norm_num)

theorem c22240R_74_37 : rowsJ2 74 75 61 340 ≤ 13170340432166 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1590 c22240R_74_38 (by norm_num)

theorem c22240R_74_36 : rowsJ2 74 75 60 340 ≤ 15587016253265 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1589 c22240R_74_37 (by norm_num)

theorem c22240R_74_35 : rowsJ2 74 75 59 340 ≤ 18231055554928 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1588 c22240R_74_36 (by norm_num)

theorem c22240R_74_34 : rowsJ2 74 75 58 340 ≤ 21158333294618 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1587 c22240R_74_35 (by norm_num)

theorem c22240R_74_33 : rowsJ2 74 75 57 340 ≤ 24371705040034 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1586 c22240R_74_34 (by norm_num)

theorem c22240R_74_32 : rowsJ2 74 75 56 340 ≤ 27927007080808 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1585 c22240R_74_33 (by norm_num)

theorem c22240R_74_31 : rowsJ2 74 75 55 340 ≤ 31764686232245 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1584 c22240R_74_32 (by norm_num)

theorem c22240R_74_30 : rowsJ2 74 75 54 340 ≤ 35940148101880 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1583 c22240R_74_31 (by norm_num)

theorem c22240R_74_29 : rowsJ2 74 75 53 340 ≤ 39982897638123 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1582 c22240R_74_30 (by norm_num)

theorem c22240R_74_28 : rowsJ2 74 75 52 340 ≤ 43714298883255 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1581 c22240R_74_29 (by norm_num)

theorem c22240R_74_27 : rowsJ2 74 75 51 340 ≤ 46907558807747 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1580 c22240R_74_28 (by norm_num)

theorem c22240R_74_26 : rowsJ2 74 75 50 340 ≤ 49637502695433 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1579 c22240R_74_27 (by norm_num)

theorem c22240R_74_25 : rowsJ2 74 75 49 340 ≤ 51806266382816 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1578 c22240R_74_26 (by norm_num)

theorem c22240R_74_24 : rowsJ2 74 75 48 340 ≤ 53244959979422 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1577 c22240R_74_25 (by norm_num)

theorem c22240R_74_23 : rowsJ2 74 75 47 340 ≤ 53998005664576 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1576 c22240R_74_24 (by norm_num)

theorem c22240R_74_22 : rowsJ2 74 75 46 340 ≤ 54350706530347 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1575 c22240R_74_23 (by norm_num)

theorem c22240R_74_21 : rowsJ2 74 75 45 340 ≤ 54531565771859 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1574 c22240R_74_22 (by norm_num)

theorem c22240R_74_20 : rowsJ2 74 75 44 340 ≤ 54593409786692 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1573 c22240R_74_21 (by norm_num)

theorem c22240R_74_19 : rowsJ2 74 75 43 340 ≤ 54593409786692 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1572 c22240R_74_20 (by norm_num)

theorem c22240R_74_18 : rowsJ2 74 75 42 340 ≤ 54593409786692 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1571 c22240R_74_19 (by norm_num)

theorem c22240R_74_17 : rowsJ2 74 75 41 340 ≤ 54593409786692 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1570 c22240R_74_18 (by norm_num)

theorem c22240R_74_16 : rowsJ2 74 75 39 340 ≤ 54593409786692 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1569 c22240R_74_17 (by norm_num)

theorem c22240R_74_15 : rowsJ2 74 75 37 340 ≤ 54593409786692 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1568 c22240R_74_16 (by norm_num)

theorem c22240R_74_14 : rowsJ2 74 75 35 340 ≤ 54593409786692 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1567 c22240R_74_15 (by norm_num)

theorem c22240R_74_13 : rowsJ2 74 75 33 340 ≤ 54593409786692 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1566 c22240R_74_14 (by norm_num)

theorem c22240R_74_12 : rowsJ2 74 75 31 340 ≤ 54593409786692 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1565 c22240R_74_13 (by norm_num)

theorem c22240R_74_11 : rowsJ2 74 75 30 340 ≤ 54594369028558 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1564 c22240R_74_12 (by norm_num)

theorem c22240R_74_10 : rowsJ2 74 75 29 340 ≤ 54596297603319 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1563 c22240R_74_11 (by norm_num)

theorem c22240R_74_9 : rowsJ2 74 75 28 340 ≤ 54599175774354 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1562 c22240R_74_10 (by norm_num)

theorem c22240R_74_8 : rowsJ2 74 75 27 340 ≤ 54603015317939 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1561 c22240R_74_9 (by norm_num)

theorem c22240R_74_7 : rowsJ2 74 75 26 340 ≤ 54608688469196 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1560 c22240R_74_8 (by norm_num)

theorem c22240R_74_6 : rowsJ2 74 75 25 340 ≤ 54616219367843 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1559 c22240R_74_7 (by norm_num)

theorem c22240R_74_5 : rowsJ2 74 75 24 340 ≤ 54625575910325 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1558 c22240R_74_6 (by norm_num)

theorem c22240R_74_4 : rowsJ2 74 75 23 340 ≤ 54636785659396 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1557 c22240R_74_5 (by norm_num)

theorem c22240R_74_3 : rowsJ2 74 75 22 340 ≤ 54647981935336 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1556 c22240R_74_4 (by norm_num)

theorem c22240R_74_2 : rowsJ2 74 75 21 340 ≤ 54658253350215 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1555 c22240R_74_3 (by norm_num)

theorem c22240R_74_1 : rowsJ2 74 75 18 340 ≤ 54662710461634 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1554 c22240R_74_2 (by norm_num)

theorem c22240R_74_0 : rowsJ2 74 75 0 340 ≤ 55567869353099 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22240R_1553 c22240R_74_1 (by norm_num)

theorem hr22240R_74 : rows2 74 75 ≤ 55567869353099 := rows2_le_of_rowsJ2 74 75 c22240R_74_0

theorem c22240R_75_48 : rowsJ2 75 76 73 340 ≤ 0 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1652 rows22240R_1653 (by norm_num)

theorem c22240R_75_47 : rowsJ2 75 76 72 340 ≤ 0 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1651 c22240R_75_48 (by norm_num)

theorem c22240R_75_46 : rowsJ2 75 76 71 340 ≤ 62354097934 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1650 c22240R_75_47 (by norm_num)

theorem c22240R_75_45 : rowsJ2 75 76 70 340 ≤ 248039412506 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1649 c22240R_75_46 (by norm_num)

theorem c22240R_75_44 : rowsJ2 75 76 69 340 ≤ 616766889775 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1648 c22240R_75_45 (by norm_num)

theorem c22240R_75_43 : rowsJ2 75 76 68 340 ≤ 1169592755844 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1647 c22240R_75_44 (by norm_num)

theorem c22240R_75_42 : rowsJ2 75 76 67 340 ≤ 1901102253346 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1646 c22240R_75_43 (by norm_num)

theorem c22240R_75_41 : rowsJ2 75 76 66 340 ≤ 2812494901190 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1645 c22240R_75_42 (by norm_num)

theorem c22240R_75_40 : rowsJ2 75 76 65 340 ≤ 3898688618209 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1644 c22240R_75_41 (by norm_num)

theorem c22240R_75_39 : rowsJ2 75 76 64 340 ≤ 5161021343318 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1643 c22240R_75_40 (by norm_num)

theorem c22240R_75_38 : rowsJ2 75 76 63 340 ≤ 6594728438541 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1642 c22240R_75_39 (by norm_num)

theorem c22240R_75_37 : rowsJ2 75 76 62 340 ≤ 8201282652484 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1641 c22240R_75_38 (by norm_num)

theorem c22240R_75_36 : rowsJ2 75 76 61 340 ≤ 9976223417265 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1640 c22240R_75_37 (by norm_num)

theorem c22240R_75_35 : rowsJ2 75 76 60 340 ≤ 11921155878560 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1639 c22240R_75_36 (by norm_num)

theorem c22240R_75_34 : rowsJ2 75 76 59 340 ≤ 14092168923522 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1638 c22240R_75_35 (by norm_num)

theorem c22240R_75_33 : rowsJ2 75 76 58 340 ≤ 16491456406704 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1637 c22240R_75_34 (by norm_num)

theorem c22240R_75_32 : rowsJ2 75 76 57 340 ≤ 19174960615707 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1636 c22240R_75_33 (by norm_num)

theorem c22240R_75_31 : rowsJ2 75 76 56 340 ≤ 22145545429111 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1635 c22240R_75_32 (by norm_num)

theorem c22240R_75_30 : rowsJ2 75 76 55 340 ≤ 25396511361494 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1634 c22240R_75_31 (by norm_num)

theorem c22240R_75_29 : rowsJ2 75 76 54 340 ≤ 28930955502357 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1633 c22240R_75_30 (by norm_num)

theorem c22240R_75_28 : rowsJ2 75 76 53 340 ≤ 32565558152636 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1632 c22240R_75_29 (by norm_num)

theorem c22240R_75_27 : rowsJ2 75 76 52 340 ≤ 35950730054053 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1631 c22240R_75_28 (by norm_num)

theorem c22240R_75_26 : rowsJ2 75 76 51 340 ≤ 38909887596115 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1630 c22240R_75_27 (by norm_num)

theorem c22240R_75_25 : rowsJ2 75 76 50 340 ≤ 41464117668495 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1629 c22240R_75_26 (by norm_num)

theorem c22240R_75_24 : rowsJ2 75 76 49 340 ≤ 43564520340539 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1628 c22240R_75_25 (by norm_num)

theorem c22240R_75_23 : rowsJ2 75 76 48 340 ≤ 44991386476532 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1627 c22240R_75_24 (by norm_num)

theorem c22240R_75_22 : rowsJ2 75 76 47 340 ≤ 45738241393755 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1626 c22240R_75_23 (by norm_num)

theorem c22240R_75_21 : rowsJ2 75 76 46 340 ≤ 46088042715377 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1625 c22240R_75_22 (by norm_num)

theorem c22240R_75_20 : rowsJ2 75 76 45 340 ≤ 46267415118024 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1624 c22240R_75_21 (by norm_num)

theorem c22240R_75_19 : rowsJ2 75 76 44 340 ≤ 46328750714907 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1623 c22240R_75_20 (by norm_num)

theorem c22240R_75_18 : rowsJ2 75 76 43 340 ≤ 46328750714907 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1622 c22240R_75_19 (by norm_num)

theorem c22240R_75_17 : rowsJ2 75 76 42 340 ≤ 46328750714907 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1621 c22240R_75_18 (by norm_num)

theorem c22240R_75_16 : rowsJ2 75 76 40 340 ≤ 46328750714907 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1620 c22240R_75_17 (by norm_num)

theorem c22240R_75_15 : rowsJ2 75 76 38 340 ≤ 46328750714907 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1619 c22240R_75_16 (by norm_num)

theorem c22240R_75_14 : rowsJ2 75 76 36 340 ≤ 46328750714907 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1618 c22240R_75_15 (by norm_num)

theorem c22240R_75_13 : rowsJ2 75 76 34 340 ≤ 46328750714907 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1617 c22240R_75_14 (by norm_num)

theorem c22240R_75_12 : rowsJ2 75 76 32 340 ≤ 46328750714907 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1616 c22240R_75_13 (by norm_num)

theorem c22240R_75_11 : rowsJ2 75 76 30 340 ≤ 46328750714907 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1615 c22240R_75_12 (by norm_num)

theorem c22240R_75_10 : rowsJ2 75 76 29 340 ≤ 46329714648678 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1614 c22240R_75_11 (by norm_num)

theorem c22240R_75_9 : rowsJ2 75 76 28 340 ≤ 46331652995447 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1613 c22240R_75_10 (by norm_num)

theorem c22240R_75_8 : rowsJ2 75 76 27 340 ≤ 46334546269468 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1612 c22240R_75_9 (by norm_num)

theorem c22240R_75_7 : rowsJ2 75 76 26 340 ≤ 46339289017175 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1611 c22240R_75_8 (by norm_num)

theorem c22240R_75_6 : rowsJ2 75 76 25 340 ≤ 46345874673532 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1610 c22240R_75_7 (by norm_num)

theorem c22240R_75_5 : rowsJ2 75 76 24 340 ≤ 46355207685049 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1609 c22240R_75_6 (by norm_num)

theorem c22240R_75_4 : rowsJ2 75 76 23 340 ≤ 46366376717578 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1608 c22240R_75_5 (by norm_num)

theorem c22240R_75_3 : rowsJ2 75 76 22 340 ≤ 46379332496583 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1607 c22240R_75_4 (by norm_num)

theorem c22240R_75_2 : rowsJ2 75 76 21 340 ≤ 46391309865851 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1606 c22240R_75_3 (by norm_num)

theorem c22240R_75_1 : rowsJ2 75 76 18 340 ≤ 46401354984818 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1605 c22240R_75_2 (by norm_num)

theorem c22240R_75_0 : rowsJ2 75 76 0 340 ≤ 47184364529886 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22240R_1604 c22240R_75_1 (by norm_num)

theorem hr22240R_75 : rows2 75 76 ≤ 47184364529886 := rows2_le_of_rowsJ2 75 76 c22240R_75_0

theorem c22240R_76_48 : rowsJ2 76 77 74 340 ≤ 72433683073 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1702 rows22240R_1703 (by norm_num)

theorem c22240R_76_47 : rowsJ2 76 77 72 340 ≤ 72433683073 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1701 c22240R_76_48 (by norm_num)

theorem c22240R_76_46 : rowsJ2 76 77 71 340 ≤ 72433683073 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1700 c22240R_76_47 (by norm_num)

theorem c22240R_76_45 : rowsJ2 76 77 70 340 ≤ 134809576673 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1699 c22240R_76_46 (by norm_num)

theorem c22240R_76_44 : rowsJ2 76 77 69 340 ≤ 320573451636 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1698 c22240R_76_45 (by norm_num)

theorem c22240R_76_43 : rowsJ2 76 77 68 340 ≤ 689484519555 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1697 c22240R_76_44 (by norm_num)

theorem c22240R_76_42 : rowsJ2 76 77 67 340 ≤ 1178605163802 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1696 c22240R_76_43 (by norm_num)

theorem c22240R_76_41 : rowsJ2 76 77 66 340 ≤ 1846772577631 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1695 c22240R_76_42 (by norm_num)

theorem c22240R_76_40 : rowsJ2 76 77 65 340 ≤ 2632341494922 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1694 c22240R_76_41 (by norm_num)

theorem c22240R_76_39 : rowsJ2 76 77 64 340 ≤ 3593282246147 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1693 c22240R_76_40 (by norm_num)

theorem c22240R_76_38 : rowsJ2 76 77 63 340 ≤ 4669170688082 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1692 c22240R_76_39 (by norm_num)

theorem c22240R_76_37 : rowsJ2 76 77 62 340 ≤ 5917164197053 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1691 c22240R_76_38 (by norm_num)

theorem c22240R_76_36 : rowsJ2 76 77 61 340 ≤ 7277992309830 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1690 c22240R_76_37 (by norm_num)

theorem c22240R_76_35 : rowsJ2 76 77 60 340 ≤ 8808052261404 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1689 c22240R_76_36 (by norm_num)

theorem c22240R_76_34 : rowsJ2 76 77 59 340 ≤ 10508928988072 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1688 c22240R_76_35 (by norm_num)

theorem c22240R_76_33 : rowsJ2 76 77 58 340 ≤ 12436765299050 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1687 c22240R_76_34 (by norm_num)

theorem c22240R_76_32 : rowsJ2 76 77 57 340 ≤ 14593749526417 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1686 c22240R_76_33 (by norm_num)

theorem c22240R_76_31 : rowsJ2 76 77 56 340 ≤ 17035901940129 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1685 c22240R_76_32 (by norm_num)

theorem c22240R_76_30 : rowsJ2 76 77 55 340 ≤ 19703979204786 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1684 c22240R_76_31 (by norm_num)

theorem c22240R_76_29 : rowsJ2 76 77 54 340 ≤ 22653495325383 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1683 c22240R_76_30 (by norm_num)

theorem c22240R_76_28 : rowsJ2 76 77 53 340 ≤ 25826327698348 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1682 c22240R_76_29 (by norm_num)

theorem c22240R_76_27 : rowsJ2 76 77 52 340 ≤ 28863928639990 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1681 c22240R_76_28 (by norm_num)

theorem c22240R_76_26 : rowsJ2 76 77 51 340 ≤ 31537033227297 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1680 c22240R_76_27 (by norm_num)

theorem c22240R_76_25 : rowsJ2 76 77 50 340 ≤ 33915114853012 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1679 c22240R_76_26 (by norm_num)

theorem c22240R_76_24 : rowsJ2 76 77 49 340 ≤ 35896545940739 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1678 c22240R_76_25 (by norm_num)

theorem c22240R_76_23 : rowsJ2 76 77 48 340 ≤ 37311777500119 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1677 c22240R_76_24 (by norm_num)

theorem c22240R_76_22 : rowsJ2 76 77 47 340 ≤ 38052542609384 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1676 c22240R_76_23 (by norm_num)

theorem c22240R_76_21 : rowsJ2 76 77 46 340 ≤ 38399491673059 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1675 c22240R_76_22 (by norm_num)

theorem c22240R_76_20 : rowsJ2 76 77 45 340 ≤ 38577401484430 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1674 c22240R_76_21 (by norm_num)

theorem c22240R_76_19 : rowsJ2 76 77 44 340 ≤ 38638236954719 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1673 c22240R_76_20 (by norm_num)

theorem c22240R_76_18 : rowsJ2 76 77 43 340 ≤ 38638236954719 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1672 c22240R_76_19 (by norm_num)

theorem c22240R_76_17 : rowsJ2 76 77 42 340 ≤ 38638236954719 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1671 c22240R_76_18 (by norm_num)

theorem c22240R_76_16 : rowsJ2 76 77 41 340 ≤ 38638236954719 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1670 c22240R_76_17 (by norm_num)

theorem c22240R_76_15 : rowsJ2 76 77 39 340 ≤ 38638236954719 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1669 c22240R_76_16 (by norm_num)

theorem c22240R_76_14 : rowsJ2 76 77 37 340 ≤ 38638236954719 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1668 c22240R_76_15 (by norm_num)

theorem c22240R_76_13 : rowsJ2 76 77 35 340 ≤ 38638236954719 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1667 c22240R_76_14 (by norm_num)

theorem c22240R_76_12 : rowsJ2 76 77 33 340 ≤ 38638236954719 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1666 c22240R_76_13 (by norm_num)

theorem c22240R_76_11 : rowsJ2 76 77 31 340 ≤ 38638236954719 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1665 c22240R_76_12 (by norm_num)

theorem c22240R_76_10 : rowsJ2 76 77 29 340 ≤ 38638236954719 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1664 c22240R_76_11 (by norm_num)

theorem c22240R_76_9 : rowsJ2 76 77 28 340 ≤ 38639205838186 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1663 c22240R_76_10 (by norm_num)

theorem c22240R_76_8 : rowsJ2 76 77 27 340 ≤ 38641154487987 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1662 c22240R_76_9 (by norm_num)

theorem c22240R_76_7 : rowsJ2 76 77 26 340 ≤ 38644938827220 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1661 c22240R_76_8 (by norm_num)

theorem c22240R_76_6 : rowsJ2 76 77 25 340 ≤ 38650581989922 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1660 c22240R_76_7 (by norm_num)

theorem c22240R_76_5 : rowsJ2 76 77 24 340 ≤ 38658950369084 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1659 c22240R_76_6 (by norm_num)

theorem c22240R_76_4 : rowsJ2 76 77 23 340 ≤ 38670082044033 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1658 c22240R_76_5 (by norm_num)

theorem c22240R_76_3 : rowsJ2 76 77 22 340 ≤ 38683931616621 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1657 c22240R_76_4 (by norm_num)

theorem c22240R_76_2 : rowsJ2 76 77 20 340 ≤ 38708624040736 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1656 c22240R_76_3 (by norm_num)

theorem c22240R_76_1 : rowsJ2 76 77 18 340 ≤ 38712220801602 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1655 c22240R_76_2 (by norm_num)

theorem c22240R_76_0 : rowsJ2 76 77 0 340 ≤ 39388454088310 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22240R_1654 c22240R_76_1 (by norm_num)

theorem hr22240R_76 : rows2 76 77 ≤ 39388454088310 := rows2_le_of_rowsJ2 76 77 c22240R_76_0

theorem c22240R_77_47 : rowsJ2 77 78 75 340 ≤ 1788223341922 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1751 rows22240R_1752 (by norm_num)

theorem c22240R_77_46 : rowsJ2 77 78 73 340 ≤ 1788223341922 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1750 c22240R_77_47 (by norm_num)

theorem c22240R_77_45 : rowsJ2 77 78 71 340 ≤ 1788223341922 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1749 c22240R_77_46 (by norm_num)

theorem c22240R_77_44 : rowsJ2 77 78 70 340 ≤ 1788223341922 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1748 c22240R_77_45 (by norm_num)

theorem c22240R_77_43 : rowsJ2 77 78 69 340 ≤ 1850629775067 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1747 c22240R_77_44 (by norm_num)

theorem c22240R_77_42 : rowsJ2 77 78 68 340 ≤ 2036498500692 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1746 c22240R_77_43 (by norm_num)

theorem c22240R_77_41 : rowsJ2 77 78 67 340 ≤ 2342141130125 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1745 c22240R_77_42 (by norm_num)

theorem c22240R_77_40 : rowsJ2 77 78 66 340 ≤ 2768310476417 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1744 c22240R_77_41 (by norm_num)

theorem c22240R_77_39 : rowsJ2 77 78 65 340 ≤ 3311544012291 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1743 c22240R_77_40 (by norm_num)

theorem c22240R_77_38 : rowsJ2 77 78 64 340 ≤ 3972688688429 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1742 c22240R_77_39 (by norm_num)

theorem c22240R_77_37 : rowsJ2 77 78 63 340 ≤ 4748497194979 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1741 c22240R_77_38 (by norm_num)

theorem c22240R_77_36 : rowsJ2 77 78 62 340 ≤ 5639907881718 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1740 c22240R_77_37 (by norm_num)

theorem c22240R_77_35 : rowsJ2 77 78 61 340 ≤ 6643879291768 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1739 c22240R_77_36 (by norm_num)

theorem c22240R_77_34 : rowsJ2 77 78 60 340 ≤ 7761439259375 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1738 c22240R_77_35 (by norm_num)

theorem c22240R_77_33 : rowsJ2 77 78 59 340 ≤ 9049026307646 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1737 c22240R_77_34 (by norm_num)

theorem c22240R_77_32 : rowsJ2 77 78 58 340 ≤ 10508206800340 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1736 c22240R_77_33 (by norm_num)

theorem c22240R_77_31 : rowsJ2 77 78 57 340 ≤ 12195187772582 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1735 c22240R_77_32 (by norm_num)

theorem c22240R_77_30 : rowsJ2 77 78 56 340 ≤ 14112153892329 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1734 c22240R_77_31 (by norm_num)

theorem c22240R_77_29 : rowsJ2 77 78 55 340 ≤ 16253598736848 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1733 c22240R_77_30 (by norm_num)

theorem c22240R_77_28 : rowsJ2 77 78 54 340 ≤ 18621894966222 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1732 c22240R_77_29 (by norm_num)

theorem c22240R_77_27 : rowsJ2 77 78 53 340 ≤ 21211918849484 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1731 c22240R_77_28 (by norm_num)

theorem c22240R_77_26 : rowsJ2 77 78 52 340 ≤ 23848469858614 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1730 c22240R_77_27 (by norm_num)

theorem c22240R_77_25 : rowsJ2 77 78 51 340 ≤ 26234381584636 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1729 c22240R_77_26 (by norm_num)

theorem c22240R_77_24 : rowsJ2 77 78 50 340 ≤ 28384453240922 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1728 c22240R_77_25 (by norm_num)

theorem c22240R_77_23 : rowsJ2 77 78 49 340 ≤ 30246656259263 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1727 c22240R_77_24 (by norm_num)

theorem c22240R_77_22 : rowsJ2 77 78 48 340 ≤ 31599671016835 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1726 c22240R_77_23 (by norm_num)

theorem c22240R_77_21 : rowsJ2 77 78 47 340 ≤ 32334444828337 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1725 c22240R_77_22 (by norm_num)

theorem c22240R_77_20 : rowsJ2 77 78 46 340 ≤ 32678587772876 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1724 c22240R_77_21 (by norm_num)

theorem c22240R_77_19 : rowsJ2 77 78 45 340 ≤ 32855058652200 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1723 c22240R_77_20 (by norm_num)

theorem c22240R_77_18 : rowsJ2 77 78 44 340 ≤ 32915402086062 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1722 c22240R_77_19 (by norm_num)

theorem c22240R_77_17 : rowsJ2 77 78 43 340 ≤ 32915402086062 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1721 c22240R_77_18 (by norm_num)

theorem c22240R_77_16 : rowsJ2 77 78 42 340 ≤ 32915402086062 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1720 c22240R_77_17 (by norm_num)

theorem c22240R_77_15 : rowsJ2 77 78 41 340 ≤ 32915402086062 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1719 c22240R_77_16 (by norm_num)

theorem c22240R_77_14 : rowsJ2 77 78 39 340 ≤ 32915402086062 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1718 c22240R_77_15 (by norm_num)

theorem c22240R_77_13 : rowsJ2 77 78 37 340 ≤ 33285004652741 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1717 c22240R_77_14 (by norm_num)

theorem c22240R_77_12 : rowsJ2 77 78 34 340 ≤ 33751909858505 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1716 c22240R_77_13 (by norm_num)

theorem c22240R_77_11 : rowsJ2 77 78 32 340 ≤ 33751909858505 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1715 c22240R_77_12 (by norm_num)

theorem c22240R_77_10 : rowsJ2 77 78 30 340 ≤ 33751909858505 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1714 c22240R_77_11 (by norm_num)

theorem c22240R_77_9 : rowsJ2 77 78 28 340 ≤ 33751909858505 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1713 c22240R_77_10 (by norm_num)

theorem c22240R_77_8 : rowsJ2 77 78 27 340 ≤ 33752883956714 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1712 c22240R_77_9 (by norm_num)

theorem c22240R_77_7 : rowsJ2 77 78 26 340 ≤ 33755711527604 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1711 c22240R_77_8 (by norm_num)

theorem c22240R_77_6 : rowsJ2 77 78 25 340 ≤ 33760384015941 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1710 c22240R_77_7 (by norm_num)

theorem c22240R_77_5 : rowsJ2 77 78 24 340 ≤ 33767790624940 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1709 c22240R_77_6 (by norm_num)

theorem c22240R_77_4 : rowsJ2 77 78 23 340 ≤ 33777938265665 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1708 c22240R_77_5 (by norm_num)

theorem c22240R_77_3 : rowsJ2 77 78 22 340 ≤ 33791729878925 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1707 c22240R_77_4 (by norm_num)

theorem c22240R_77_2 : rowsJ2 77 78 20 340 ≤ 33819997169288 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1706 c22240R_77_3 (by norm_num)

theorem c22240R_77_1 : rowsJ2 77 78 18 340 ≤ 33826313952536 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1705 c22240R_77_2 (by norm_num)

theorem c22240R_77_0 : rowsJ2 77 78 0 340 ≤ 34403236049386 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22240R_1704 c22240R_77_1 (by norm_num)

theorem hr22240R_77 : rows2 77 78 ≤ 34403236049386 := rows2_le_of_rowsJ2 77 78 c22240R_77_0

theorem c22240R_78_46 : rowsJ2 78 79 76 340 ≤ 4605035937124 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1799 rows22240R_1800 (by norm_num)

theorem c22240R_78_45 : rowsJ2 78 79 74 340 ≤ 4605035937124 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1798 c22240R_78_46 (by norm_num)

theorem c22240R_78_44 : rowsJ2 78 79 72 340 ≤ 4605035937124 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1797 c22240R_78_45 (by norm_num)

theorem c22240R_78_43 : rowsJ2 78 79 70 340 ≤ 4605035937124 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1796 c22240R_78_44 (by norm_num)

theorem c22240R_78_42 : rowsJ2 78 79 69 340 ≤ 4605035937124 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1795 c22240R_78_43 (by norm_num)

theorem c22240R_78_41 : rowsJ2 78 79 68 340 ≤ 4667481679370 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1794 c22240R_78_42 (by norm_num)

theorem c22240R_78_40 : rowsJ2 78 79 67 340 ≤ 4790486387005 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1793 c22240R_78_41 (by norm_num)

theorem c22240R_78_39 : rowsJ2 78 79 66 340 ≤ 5033573861348 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1792 c22240R_78_40 (by norm_num)

theorem c22240R_78_38 : rowsJ2 78 79 65 340 ≤ 5335651001303 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1791 c22240R_78_39 (by norm_num)

theorem c22240R_78_37 : rowsJ2 78 79 64 340 ≤ 5755287072752 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1790 c22240R_78_38 (by norm_num)

theorem c22240R_78_36 : rowsJ2 78 79 63 340 ≤ 6232548012878 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1789 c22240R_78_37 (by norm_num)

theorem c22240R_78_35 : rowsJ2 78 79 62 340 ≤ 6825105875571 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1788 c22240R_78_36 (by norm_num)

theorem c22240R_78_34 : rowsJ2 78 79 61 340 ≤ 7474120027805 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1787 c22240R_78_35 (by norm_num)

theorem c22240R_78_33 : rowsJ2 78 79 60 340 ≤ 8236421002518 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1786 c22240R_78_34 (by norm_num)

theorem c22240R_78_32 : rowsJ2 78 79 59 340 ≤ 9113005723483 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1785 c22240R_78_33 (by norm_num)

theorem c22240R_78_31 : rowsJ2 78 79 58 340 ≤ 10160364001924 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1784 c22240R_78_32 (by norm_num)

theorem c22240R_78_30 : rowsJ2 78 79 57 340 ≤ 11380045171457 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1783 c22240R_78_31 (by norm_num)

theorem c22240R_78_29 : rowsJ2 78 79 56 340 ≤ 12828330783546 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1782 c22240R_78_30 (by norm_num)

theorem c22240R_78_28 : rowsJ2 78 79 55 340 ≤ 14446282639556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1781 c22240R_78_29 (by norm_num)

theorem c22240R_78_27 : rowsJ2 78 79 54 340 ≤ 16289598662119 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1780 c22240R_78_28 (by norm_num)

theorem c22240R_78_26 : rowsJ2 78 79 53 340 ≤ 18300401138633 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1779 c22240R_78_27 (by norm_num)

theorem c22240R_78_25 : rowsJ2 78 79 52 340 ≤ 20533854739417 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1778 c22240R_78_26 (by norm_num)

theorem c22240R_78_24 : rowsJ2 78 79 51 340 ≤ 22579222435974 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1777 c22240R_78_25 (by norm_num)

theorem c22240R_78_23 : rowsJ2 78 79 50 340 ≤ 24500371881107 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1776 c22240R_78_24 (by norm_num)

theorem c22240R_78_22 : rowsJ2 78 79 49 340 ≤ 26191575451503 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1775 c22240R_78_23 (by norm_num)

theorem c22240R_78_21 : rowsJ2 78 79 48 340 ≤ 27482290352560 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1774 c22240R_78_22 (by norm_num)

theorem c22240R_78_20 : rowsJ2 78 79 47 340 ≤ 28211169005352 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1773 c22240R_78_21 (by norm_num)

theorem c22240R_78_19 : rowsJ2 78 79 46 340 ≤ 28552550859001 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1772 c22240R_78_20 (by norm_num)

theorem c22240R_78_18 : rowsJ2 78 79 45 340 ≤ 28727605896028 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1771 c22240R_78_19 (by norm_num)

theorem c22240R_78_17 : rowsJ2 78 79 44 340 ≤ 28787465188902 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1770 c22240R_78_18 (by norm_num)

theorem c22240R_78_16 : rowsJ2 78 79 43 340 ≤ 28787465188902 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1769 c22240R_78_17 (by norm_num)

theorem c22240R_78_15 : rowsJ2 78 79 42 340 ≤ 28787465188902 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1768 c22240R_78_16 (by norm_num)

theorem c22240R_78_14 : rowsJ2 78 79 40 340 ≤ 28787465188902 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1767 c22240R_78_15 (by norm_num)

theorem c22240R_78_13 : rowsJ2 78 79 38 340 ≤ 29499578984442 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1766 c22240R_78_14 (by norm_num)

theorem c22240R_78_12 : rowsJ2 78 79 36 340 ≤ 31062115791318 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1765 c22240R_78_13 (by norm_num)

theorem c22240R_78_11 : rowsJ2 78 79 33 340 ≤ 31345284364413 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1764 c22240R_78_12 (by norm_num)

theorem c22240R_78_10 : rowsJ2 78 79 31 340 ≤ 31345284364413 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1763 c22240R_78_11 (by norm_num)

theorem c22240R_78_9 : rowsJ2 78 79 29 340 ≤ 31345284364413 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1762 c22240R_78_10 (by norm_num)

theorem c22240R_78_8 : rowsJ2 78 79 27 340 ≤ 31345284364413 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1761 c22240R_78_9 (by norm_num)

theorem c22240R_78_7 : rowsJ2 78 79 26 340 ≤ 31347125057183 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1760 c22240R_78_8 (by norm_num)

theorem c22240R_78_6 : rowsJ2 78 79 25 340 ≤ 31350828502981 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1759 c22240R_78_7 (by norm_num)

theorem c22240R_78_5 : rowsJ2 78 79 24 340 ≤ 31357245086669 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1758 c22240R_78_6 (by norm_num)

theorem c22240R_78_4 : rowsJ2 78 79 23 340 ≤ 31366411662219 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1757 c22240R_78_5 (by norm_num)

theorem c22240R_78_3 : rowsJ2 78 79 22 340 ≤ 31379192874782 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1756 c22240R_78_4 (by norm_num)

theorem c22240R_78_2 : rowsJ2 78 79 20 340 ≤ 31410189273964 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1755 c22240R_78_3 (by norm_num)

theorem c22240R_78_1 : rowsJ2 78 79 18 340 ≤ 31420212290280 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1754 c22240R_78_2 (by norm_num)

theorem c22240R_78_0 : rowsJ2 78 79 0 340 ≤ 31905329196229 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22240R_1753 c22240R_78_1 (by norm_num)

theorem hr22240R_78 : rows2 78 79 ≤ 31905329196229 := rows2_le_of_rowsJ2 78 79 c22240R_78_0

theorem c22240R_79_45 : rowsJ2 79 80 77 340 ≤ 7054463935505 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1846 rows22240R_1847 (by norm_num)

theorem c22240R_79_44 : rowsJ2 79 80 75 340 ≤ 7124905789879 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1845 c22240R_79_45 (by norm_num)

theorem c22240R_79_43 : rowsJ2 79 80 73 340 ≤ 7124905789879 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1844 c22240R_79_44 (by norm_num)

theorem c22240R_79_42 : rowsJ2 79 80 71 340 ≤ 7124905789879 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1843 c22240R_79_43 (by norm_num)

theorem c22240R_79_41 : rowsJ2 79 80 69 340 ≤ 7124905789879 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1842 c22240R_79_42 (by norm_num)

theorem c22240R_79_40 : rowsJ2 79 80 68 340 ≤ 7124905789879 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1841 c22240R_79_41 (by norm_num)

theorem c22240R_79_39 : rowsJ2 79 80 67 340 ≤ 7124905789879 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1840 c22240R_79_40 (by norm_num)

theorem c22240R_79_38 : rowsJ2 79 80 66 340 ≤ 7185719961289 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1839 c22240R_79_39 (by norm_num)

theorem c22240R_79_37 : rowsJ2 79 80 65 340 ≤ 7305563602200 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1838 c22240R_79_38 (by norm_num)

theorem c22240R_79_36 : rowsJ2 79 80 64 340 ≤ 7484823213184 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1837 c22240R_79_37 (by norm_num)

theorem c22240R_79_35 : rowsJ2 79 80 63 340 ≤ 7721824126701 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1836 c22240R_79_36 (by norm_num)

theorem c22240R_79_34 : rowsJ2 79 80 62 340 ≤ 8016999825865 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1835 c22240R_79_35 (by norm_num)

theorem c22240R_79_33 : rowsJ2 79 80 61 340 ≤ 8368780677468 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1834 c22240R_79_34 (by norm_num)

theorem c22240R_79_32 : rowsJ2 79 80 60 340 ≤ 8777645951690 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1833 c22240R_79_33 (by norm_num)

theorem c22240R_79_31 : rowsJ2 79 80 59 340 ≤ 9300465280356 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1832 c22240R_79_32 (by norm_num)

theorem c22240R_79_30 : rowsJ2 79 80 58 340 ≤ 9938205940895 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1831 c22240R_79_31 (by norm_num)

theorem c22240R_79_29 : rowsJ2 79 80 57 340 ≤ 10747419002015 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1830 c22240R_79_30 (by norm_num)

theorem c22240R_79_28 : rowsJ2 79 80 56 340 ≤ 11729638219051 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1829 c22240R_79_29 (by norm_num)

theorem c22240R_79_27 : rowsJ2 79 80 55 340 ≤ 12880595438270 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1828 c22240R_79_28 (by norm_num)

theorem c22240R_79_26 : rowsJ2 79 80 54 340 ≤ 14201967041812 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1827 c22240R_79_27 (by norm_num)

theorem c22240R_79_25 : rowsJ2 79 80 53 340 ≤ 15689775439384 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1826 c22240R_79_26 (by norm_num)

theorem c22240R_79_24 : rowsJ2 79 80 52 340 ≤ 17345839428534 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1825 c22240R_79_25 (by norm_num)

theorem c22240R_79_23 : rowsJ2 79 80 51 340 ≤ 19048884819934 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1824 c22240R_79_24 (by norm_num)

theorem c22240R_79_22 : rowsJ2 79 80 50 340 ≤ 20687903716758 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1823 c22240R_79_23 (by norm_num)

theorem c22240R_79_21 : rowsJ2 79 80 49 340 ≤ 22207432164945 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1822 c22240R_79_22 (by norm_num)

theorem c22240R_79_20 : rowsJ2 79 80 48 340 ≤ 23384151156027 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1821 c22240R_79_21 (by norm_num)

theorem c22240R_79_19 : rowsJ2 79 80 47 340 ≤ 24107228493508 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1820 c22240R_79_20 (by norm_num)

theorem c22240R_79_18 : rowsJ2 79 80 46 340 ≤ 24445893209308 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1819 c22240R_79_19 (by norm_num)

theorem c22240R_79_17 : rowsJ2 79 80 45 340 ≤ 24619554942440 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1818 c22240R_79_18 (by norm_num)

theorem c22240R_79_16 : rowsJ2 79 80 44 340 ≤ 24678937801231 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1817 c22240R_79_17 (by norm_num)

theorem c22240R_79_15 : rowsJ2 79 80 43 340 ≤ 24678937801231 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1816 c22240R_79_16 (by norm_num)

theorem c22240R_79_14 : rowsJ2 79 80 42 340 ≤ 24678937801231 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1815 c22240R_79_15 (by norm_num)

theorem c22240R_79_13 : rowsJ2 79 80 41 340 ≤ 24678937801231 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1814 c22240R_79_14 (by norm_num)

theorem c22240R_79_12 : rowsJ2 79 80 39 340 ≤ 25551889595561 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1813 c22240R_79_13 (by norm_num)

theorem c22240R_79_11 : rowsJ2 79 80 37 340 ≤ 28244930857398 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1812 c22240R_79_12 (by norm_num)

theorem c22240R_79_10 : rowsJ2 79 80 34 340 ≤ 29832463741527 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1811 c22240R_79_11 (by norm_num)

theorem c22240R_79_9 : rowsJ2 79 80 31 340 ≤ 29832463741527 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1810 c22240R_79_10 (by norm_num)

theorem c22240R_79_8 : rowsJ2 79 80 29 340 ≤ 29832463741527 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1809 c22240R_79_9 (by norm_num)

theorem c22240R_79_7 : rowsJ2 79 80 27 340 ≤ 29832463741527 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1808 c22240R_79_8 (by norm_num)

theorem c22240R_79_6 : rowsJ2 79 80 25 340 ≤ 29834315273895 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1807 c22240R_79_7 (by norm_num)

theorem c22240R_79_5 : rowsJ2 79 80 24 340 ≤ 29838041254914 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1806 c22240R_79_6 (by norm_num)

theorem c22240R_79_4 : rowsJ2 79 80 23 340 ≤ 29844498177293 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1805 c22240R_79_5 (by norm_num)

theorem c22240R_79_3 : rowsJ2 79 80 22 340 ≤ 29853724282472 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1804 c22240R_79_4 (by norm_num)

theorem c22240R_79_2 : rowsJ2 79 80 20 340 ≤ 29881312299806 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1803 c22240R_79_3 (by norm_num)

theorem c22240R_79_1 : rowsJ2 79 80 18 340 ≤ 29895040887832 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1802 c22240R_79_2 (by norm_num)

theorem c22240R_79_0 : rowsJ2 79 80 0 340 ≤ 30297120399270 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22240R_1801 c22240R_79_1 (by norm_num)

theorem hr22240R_79 : rows2 79 80 ≤ 30297120399270 := rows2_le_of_rowsJ2 79 80 c22240R_79_0

theorem c22240R_80_44 : rowsJ2 80 81 78 340 ≤ 8292569002590 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1892 rows22240R_1893 (by norm_num)

theorem c22240R_80_43 : rowsJ2 80 81 76 340 ≤ 9722979309256 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1891 c22240R_80_44 (by norm_num)

theorem c22240R_80_42 : rowsJ2 80 81 74 340 ≤ 9722979309256 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1890 c22240R_80_43 (by norm_num)

theorem c22240R_80_41 : rowsJ2 80 81 72 340 ≤ 9722979309256 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1889 c22240R_80_42 (by norm_num)

theorem c22240R_80_40 : rowsJ2 80 81 70 340 ≤ 9722979309256 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1888 c22240R_80_41 (by norm_num)

theorem c22240R_80_39 : rowsJ2 80 81 68 340 ≤ 9722979309256 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1887 c22240R_80_40 (by norm_num)

theorem c22240R_80_38 : rowsJ2 80 81 67 340 ≤ 9722979309256 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1886 c22240R_80_39 (by norm_num)

theorem c22240R_80_37 : rowsJ2 80 81 66 340 ≤ 9722979309256 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1885 c22240R_80_38 (by norm_num)

theorem c22240R_80_36 : rowsJ2 80 81 65 340 ≤ 9722979309256 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1884 c22240R_80_37 (by norm_num)

theorem c22240R_80_35 : rowsJ2 80 81 64 340 ≤ 9782252386893 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1883 c22240R_80_36 (by norm_num)

theorem c22240R_80_34 : rowsJ2 80 81 63 340 ≤ 9841367636385 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1882 c22240R_80_35 (by norm_num)

theorem c22240R_80_33 : rowsJ2 80 81 62 340 ≤ 9958612710070 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1881 c22240R_80_34 (by norm_num)

theorem c22240R_80_32 : rowsJ2 80 81 61 340 ≤ 10075589019404 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1880 c22240R_80_33 (by norm_num)

theorem c22240R_80_31 : rowsJ2 80 81 60 340 ≤ 10249657828495 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1879 c22240R_80_32 (by norm_num)

theorem c22240R_80_30 : rowsJ2 80 81 59 340 ≤ 10481269957348 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1878 c22240R_80_31 (by norm_num)

theorem c22240R_80_29 : rowsJ2 80 81 58 340 ≤ 10827356830122 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1877 c22240R_80_30 (by norm_num)

theorem c22240R_80_28 : rowsJ2 80 81 57 340 ≤ 11288870125927 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1876 c22240R_80_29 (by norm_num)

theorem c22240R_80_27 : rowsJ2 80 81 56 340 ≤ 11922444915582 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1875 c22240R_80_28 (by norm_num)

theorem c22240R_80_26 : rowsJ2 80 81 55 340 ≤ 12669457738096 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1874 c22240R_80_27 (by norm_num)

theorem c22240R_80_25 : rowsJ2 80 81 54 340 ≤ 13585880464264 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1873 c22240R_80_26 (by norm_num)

theorem c22240R_80_24 : rowsJ2 80 81 53 340 ≤ 14614090085769 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1872 c22240R_80_25 (by norm_num)

theorem c22240R_80_23 : rowsJ2 80 81 52 340 ≤ 15809446938961 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1871 c22240R_80_24 (by norm_num)

theorem c22240R_80_22 : rowsJ2 80 81 51 340 ≤ 17115269773713 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1870 c22240R_80_23 (by norm_num)

theorem c22240R_80_21 : rowsJ2 80 81 50 340 ≤ 18470671296338 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1869 c22240R_80_22 (by norm_num)

theorem c22240R_80_20 : rowsJ2 80 81 49 340 ≤ 19765457471305 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1868 c22240R_80_21 (by norm_num)

theorem c22240R_80_19 : rowsJ2 80 81 48 340 ≤ 20827735009452 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1867 c22240R_80_20 (by norm_num)

theorem c22240R_80_18 : rowsJ2 80 81 47 340 ≤ 21493383403628 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1866 c22240R_80_19 (by norm_num)

theorem c22240R_80_17 : rowsJ2 80 81 46 340 ≤ 21829373893377 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1865 c22240R_80_18 (by norm_num)

theorem c22240R_80_16 : rowsJ2 80 81 45 340 ≤ 22001664327081 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1864 c22240R_80_17 (by norm_num)

theorem c22240R_80_15 : rowsJ2 80 81 44 340 ≤ 22060578276120 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1863 c22240R_80_16 (by norm_num)

theorem c22240R_80_14 : rowsJ2 80 81 43 340 ≤ 22060578276120 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1862 c22240R_80_15 (by norm_num)

theorem c22240R_80_13 : rowsJ2 80 81 42 340 ≤ 22060578276120 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1861 c22240R_80_14 (by norm_num)

theorem c22240R_80_12 : rowsJ2 80 81 41 340 ≤ 22060578276120 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1860 c22240R_80_13 (by norm_num)

theorem c22240R_80_11 : rowsJ2 80 81 39 340 ≤ 25511004049399 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1859 c22240R_80_12 (by norm_num)

theorem c22240R_80_10 : rowsJ2 80 81 37 340 ≤ 29706758510424 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1858 c22240R_80_11 (by norm_num)

theorem c22240R_80_9 : rowsJ2 80 81 34 340 ≤ 31941915788549 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1857 c22240R_80_10 (by norm_num)

theorem c22240R_80_8 : rowsJ2 80 81 31 340 ≤ 31941915788549 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1856 c22240R_80_9 (by norm_num)

theorem c22240R_80_7 : rowsJ2 80 81 29 340 ≤ 31941915788549 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1855 c22240R_80_8 (by norm_num)

theorem c22240R_80_6 : rowsJ2 80 81 27 340 ≤ 31941915788549 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1854 c22240R_80_7 (by norm_num)

theorem c22240R_80_5 : rowsJ2 80 81 25 340 ≤ 31941915788549 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1853 c22240R_80_6 (by norm_num)

theorem c22240R_80_4 : rowsJ2 80 81 23 340 ≤ 31947528347818 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1852 c22240R_80_5 (by norm_num)

theorem c22240R_80_3 : rowsJ2 80 81 22 340 ≤ 31954027614518 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1851 c22240R_80_4 (by norm_num)

theorem c22240R_80_2 : rowsJ2 80 81 20 340 ≤ 31976273107726 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1850 c22240R_80_3 (by norm_num)

theorem c22240R_80_1 : rowsJ2 80 81 18 340 ≤ 31991946968547 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1849 c22240R_80_2 (by norm_num)

theorem c22240R_80_0 : rowsJ2 80 81 0 340 ≤ 32319520047870 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22240R_1848 c22240R_80_1 (by norm_num)

theorem hr22240R_80 : rows2 80 81 ≤ 32319520047870 := rows2_le_of_rowsJ2 80 81 c22240R_80_0

theorem c22240R_81_43 : rowsJ2 81 82 80 340 ≤ 5591700869472 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1937 rows22240R_1938 (by norm_num)

theorem c22240R_81_42 : rowsJ2 81 82 78 340 ≤ 9910807999829 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1936 c22240R_81_43 (by norm_num)

theorem c22240R_81_41 : rowsJ2 81 82 76 340 ≤ 11044887445195 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1935 c22240R_81_42 (by norm_num)

theorem c22240R_81_40 : rowsJ2 81 82 73 340 ≤ 11044887445195 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1934 c22240R_81_41 (by norm_num)

theorem c22240R_81_39 : rowsJ2 81 82 71 340 ≤ 11044887445195 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1933 c22240R_81_40 (by norm_num)

theorem c22240R_81_38 : rowsJ2 81 82 69 340 ≤ 11044887445195 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1932 c22240R_81_39 (by norm_num)

theorem c22240R_81_37 : rowsJ2 81 82 67 340 ≤ 11044887445195 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1931 c22240R_81_38 (by norm_num)

theorem c22240R_81_36 : rowsJ2 81 82 66 340 ≤ 11044887445195 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1930 c22240R_81_37 (by norm_num)

theorem c22240R_81_35 : rowsJ2 81 82 65 340 ≤ 11044887445195 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1929 c22240R_81_36 (by norm_num)

theorem c22240R_81_34 : rowsJ2 81 82 64 340 ≤ 11044887445195 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1928 c22240R_81_35 (by norm_num)

theorem c22240R_81_33 : rowsJ2 81 82 63 340 ≤ 11044887445195 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1927 c22240R_81_34 (by norm_num)

theorem c22240R_81_32 : rowsJ2 81 82 62 340 ≤ 11044887445195 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1926 c22240R_81_33 (by norm_num)

theorem c22240R_81_31 : rowsJ2 81 82 61 340 ≤ 11044887445195 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1925 c22240R_81_32 (by norm_num)

theorem c22240R_81_30 : rowsJ2 81 82 60 340 ≤ 11044887445195 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1924 c22240R_81_31 (by norm_num)

theorem c22240R_81_29 : rowsJ2 81 82 59 340 ≤ 11102311941498 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1923 c22240R_81_30 (by norm_num)

theorem c22240R_81_28 : rowsJ2 81 82 58 340 ≤ 11217596997832 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1922 c22240R_81_29 (by norm_num)

theorem c22240R_81_27 : rowsJ2 81 82 57 340 ≤ 11447758182989 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1921 c22240R_81_28 (by norm_num)

theorem c22240R_81_26 : rowsJ2 81 82 56 340 ≤ 11793745248837 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1920 c22240R_81_27 (by norm_num)

theorem c22240R_81_25 : rowsJ2 81 82 55 340 ≤ 12252615336316 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1919 c22240R_81_26 (by norm_num)

theorem c22240R_81_24 : rowsJ2 81 82 54 340 ≤ 12825414678242 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1918 c22240R_81_25 (by norm_num)

theorem c22240R_81_23 : rowsJ2 81 82 53 340 ≤ 13509396880335 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1917 c22240R_81_24 (by norm_num)

theorem c22240R_81_22 : rowsJ2 81 82 52 340 ≤ 14305704072842 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1916 c22240R_81_23 (by norm_num)

theorem c22240R_81_21 : rowsJ2 81 82 51 340 ≤ 15211780217674 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1915 c22240R_81_22 (by norm_num)

theorem c22240R_81_20 : rowsJ2 81 82 50 340 ≤ 16228863610154 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1914 c22240R_81_21 (by norm_num)

theorem c22240R_81_19 : rowsJ2 81 82 49 340 ≤ 17297718322405 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1913 c22240R_81_20 (by norm_num)

theorem c22240R_81_18 : rowsJ2 81 82 48 340 ≤ 18192611771635 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1912 c22240R_81_19 (by norm_num)

theorem c22240R_81_17 : rowsJ2 81 82 47 340 ≤ 18800617303129 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1911 c22240R_81_18 (by norm_num)

theorem c22240R_81_16 : rowsJ2 81 82 46 340 ≤ 19133975470013 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1910 c22240R_81_17 (by norm_num)

theorem c22240R_81_15 : rowsJ2 81 82 45 340 ≤ 19304916091560 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1909 c22240R_81_16 (by norm_num)

theorem c22240R_81_14 : rowsJ2 81 82 44 340 ≤ 19363368478323 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1908 c22240R_81_15 (by norm_num)

theorem c22240R_81_13 : rowsJ2 81 82 43 340 ≤ 19363368478323 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1907 c22240R_81_14 (by norm_num)

theorem c22240R_81_12 : rowsJ2 81 82 42 340 ≤ 19363368478323 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1906 c22240R_81_13 (by norm_num)

theorem c22240R_81_11 : rowsJ2 81 82 41 340 ≤ 20869358449371 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1905 c22240R_81_12 (by norm_num)

theorem c22240R_81_10 : rowsJ2 81 82 39 340 ≤ 26632203940629 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1904 c22240R_81_11 (by norm_num)

theorem c22240R_81_9 : rowsJ2 81 82 36 340 ≤ 33168595154315 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1903 c22240R_81_10 (by norm_num)

theorem c22240R_81_8 : rowsJ2 81 82 33 340 ≤ 34398740444258 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1902 c22240R_81_9 (by norm_num)

theorem c22240R_81_7 : rowsJ2 81 82 30 340 ≤ 34398740444258 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1901 c22240R_81_8 (by norm_num)

theorem c22240R_81_6 : rowsJ2 81 82 28 340 ≤ 34398740444258 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1900 c22240R_81_7 (by norm_num)

theorem c22240R_81_5 : rowsJ2 81 82 26 340 ≤ 34398740444258 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1899 c22240R_81_6 (by norm_num)

theorem c22240R_81_4 : rowsJ2 81 82 24 340 ≤ 34398740444258 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1898 c22240R_81_5 (by norm_num)

theorem c22240R_81_3 : rowsJ2 81 82 22 340 ≤ 34404389776079 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1897 c22240R_81_4 (by norm_num)

theorem c22240R_81_2 : rowsJ2 81 82 20 340 ≤ 34420287571081 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1896 c22240R_81_3 (by norm_num)

theorem c22240R_81_1 : rowsJ2 81 82 18 340 ≤ 34437973459805 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1895 c22240R_81_2 (by norm_num)

theorem c22240R_81_0 : rowsJ2 81 82 0 340 ≤ 34699966760828 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22240R_1894 c22240R_81_1 (by norm_num)

theorem hr22240R_81 : rows2 81 82 ≤ 34699966760828 := rows2_le_of_rowsJ2 81 82 c22240R_81_0

theorem c22240R_82_43 : rowsJ2 82 83 81 340 ≤ 5291338364124 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1982 rows22240R_1983 (by norm_num)

theorem c22240R_82_42 : rowsJ2 82 83 80 340 ≤ 7619353400527 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1981 c22240R_82_43 (by norm_num)

theorem c22240R_82_41 : rowsJ2 82 83 78 340 ≤ 11426200738259 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1980 c22240R_82_42 (by norm_num)

theorem c22240R_82_40 : rowsJ2 82 83 75 340 ≤ 12563616111674 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1979 c22240R_82_41 (by norm_num)

theorem c22240R_82_39 : rowsJ2 82 83 72 340 ≤ 12563616111674 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1978 c22240R_82_40 (by norm_num)

theorem c22240R_82_38 : rowsJ2 82 83 70 340 ≤ 12563616111674 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1977 c22240R_82_39 (by norm_num)

theorem c22240R_82_37 : rowsJ2 82 83 68 340 ≤ 12563616111674 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1976 c22240R_82_38 (by norm_num)

theorem c22240R_82_36 : rowsJ2 82 83 66 340 ≤ 12563616111674 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1975 c22240R_82_37 (by norm_num)

theorem c22240R_82_35 : rowsJ2 82 83 65 340 ≤ 12563616111674 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1974 c22240R_82_36 (by norm_num)

theorem c22240R_82_34 : rowsJ2 82 83 64 340 ≤ 12563616111674 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1973 c22240R_82_35 (by norm_num)

theorem c22240R_82_33 : rowsJ2 82 83 63 340 ≤ 12563616111674 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1972 c22240R_82_34 (by norm_num)

theorem c22240R_82_32 : rowsJ2 82 83 62 340 ≤ 12563616111674 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1971 c22240R_82_33 (by norm_num)

theorem c22240R_82_31 : rowsJ2 82 83 61 340 ≤ 12563616111674 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1970 c22240R_82_32 (by norm_num)

theorem c22240R_82_30 : rowsJ2 82 83 60 340 ≤ 12563616111674 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1969 c22240R_82_31 (by norm_num)

theorem c22240R_82_29 : rowsJ2 82 83 59 340 ≤ 12563616111674 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1968 c22240R_82_30 (by norm_num)

theorem c22240R_82_28 : rowsJ2 82 83 58 340 ≤ 12621138730433 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1967 c22240R_82_29 (by norm_num)

theorem c22240R_82_27 : rowsJ2 82 83 57 340 ≤ 12736631325103 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1966 c22240R_82_28 (by norm_num)

theorem c22240R_82_26 : rowsJ2 82 83 56 340 ≤ 12967228320375 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1965 c22240R_82_27 (by norm_num)

theorem c22240R_82_25 : rowsJ2 82 83 55 340 ≤ 13254682958576 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1964 c22240R_82_26 (by norm_num)

theorem c22240R_82_24 : rowsJ2 82 83 54 340 ≤ 13655383620319 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1963 c22240R_82_25 (by norm_num)

theorem c22240R_82_23 : rowsJ2 82 83 53 340 ≤ 14112023358960 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1962 c22240R_82_24 (by norm_num)

theorem c22240R_82_22 : rowsJ2 82 83 52 340 ≤ 14680298118347 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1961 c22240R_82_23 (by norm_num)

theorem c22240R_82_21 : rowsJ2 82 83 51 340 ≤ 15303782703742 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1960 c22240R_82_22 (by norm_num)

theorem c22240R_82_20 : rowsJ2 82 83 50 340 ≤ 16037533347471 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1959 c22240R_82_21 (by norm_num)

theorem c22240R_82_19 : rowsJ2 82 83 49 340 ≤ 16825950844579 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1958 c22240R_82_20 (by norm_num)

theorem c22240R_82_18 : rowsJ2 82 83 48 340 ≤ 17552560374338 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1957 c22240R_82_19 (by norm_num)

theorem c22240R_82_17 : rowsJ2 82 83 47 340 ≤ 18050095922906 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1956 c22240R_82_18 (by norm_num)

theorem c22240R_82_16 : rowsJ2 82 83 46 340 ≤ 18380862692865 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1955 c22240R_82_17 (by norm_num)

theorem c22240R_82_15 : rowsJ2 82 83 45 340 ≤ 18550474488406 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1954 c22240R_82_16 (by norm_num)

theorem c22240R_82_14 : rowsJ2 82 83 44 340 ≤ 18608472489015 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1953 c22240R_82_15 (by norm_num)

theorem c22240R_82_13 : rowsJ2 82 83 43 340 ≤ 18608472489015 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1952 c22240R_82_14 (by norm_num)

theorem c22240R_82_12 : rowsJ2 82 83 42 340 ≤ 20718020742653 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1951 c22240R_82_13 (by norm_num)

theorem c22240R_82_11 : rowsJ2 82 83 41 340 ≤ 24033069788249 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1950 c22240R_82_12 (by norm_num)

theorem c22240R_82_10 : rowsJ2 82 83 39 340 ≤ 32583517699189 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1949 c22240R_82_11 (by norm_num)

theorem c22240R_82_9 : rowsJ2 82 83 37 340 ≤ 38374393283126 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1948 c22240R_82_10 (by norm_num)

theorem c22240R_82_8 : rowsJ2 82 83 34 340 ≤ 41255262015976 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1947 c22240R_82_9 (by norm_num)

theorem c22240R_82_7 : rowsJ2 82 83 31 340 ≤ 41352574396749 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1946 c22240R_82_8 (by norm_num)

theorem c22240R_82_6 : rowsJ2 82 83 28 340 ≤ 41352574396749 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1945 c22240R_82_7 (by norm_num)

theorem c22240R_82_5 : rowsJ2 82 83 26 340 ≤ 41352574396749 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1944 c22240R_82_6 (by norm_num)

theorem c22240R_82_4 : rowsJ2 82 83 24 340 ≤ 41352574396749 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1943 c22240R_82_5 (by norm_num)

theorem c22240R_82_3 : rowsJ2 82 83 22 340 ≤ 41354461789571 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1942 c22240R_82_4 (by norm_num)

theorem c22240R_82_2 : rowsJ2 82 83 20 340 ≤ 41364852540896 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1941 c22240R_82_3 (by norm_num)

theorem c22240R_82_1 : rowsJ2 82 83 18 340 ≤ 41381746481485 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1940 c22240R_82_2 (by norm_num)

theorem c22240R_82_0 : rowsJ2 82 83 0 340 ≤ 41587199985148 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22240R_1939 c22240R_82_1 (by norm_num)

theorem hr22240R_82 : rows2 82 83 ≤ 41587199985148 := rows2_le_of_rowsJ2 82 83 c22240R_82_0

theorem c22240R_83_43 : rowsJ2 83 84 82 340 ≤ 5628607442994 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2027 rows22240R_2028 (by norm_num)

theorem c22240R_83_42 : rowsJ2 83 84 81 340 ≤ 7776701698116 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2026 c22240R_83_43 (by norm_num)

theorem c22240R_83_41 : rowsJ2 83 84 80 340 ≤ 9773552773385 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2025 c22240R_83_42 (by norm_num)

theorem c22240R_83_40 : rowsJ2 83 84 79 340 ≤ 11505209560554 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2024 c22240R_83_41 (by norm_num)

theorem c22240R_83_39 : rowsJ2 83 84 77 340 ≤ 13703653353053 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2023 c22240R_83_40 (by norm_num)

theorem c22240R_83_38 : rowsJ2 83 84 74 340 ≤ 13771544919164 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2022 c22240R_83_39 (by norm_num)

theorem c22240R_83_37 : rowsJ2 83 84 71 340 ≤ 13771544919164 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2021 c22240R_83_38 (by norm_num)

theorem c22240R_83_36 : rowsJ2 83 84 69 340 ≤ 13771544919164 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2020 c22240R_83_37 (by norm_num)

theorem c22240R_83_35 : rowsJ2 83 84 67 340 ≤ 13771544919164 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2019 c22240R_83_36 (by norm_num)

theorem c22240R_83_34 : rowsJ2 83 84 65 340 ≤ 13771544919164 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2018 c22240R_83_35 (by norm_num)

theorem c22240R_83_33 : rowsJ2 83 84 64 340 ≤ 13771544919164 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2017 c22240R_83_34 (by norm_num)

theorem c22240R_83_32 : rowsJ2 83 84 63 340 ≤ 13771544919164 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2016 c22240R_83_33 (by norm_num)

theorem c22240R_83_31 : rowsJ2 83 84 62 340 ≤ 13771544919164 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2015 c22240R_83_32 (by norm_num)

theorem c22240R_83_30 : rowsJ2 83 84 61 340 ≤ 13771544919164 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2014 c22240R_83_31 (by norm_num)

theorem c22240R_83_29 : rowsJ2 83 84 60 340 ≤ 13771544919164 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2013 c22240R_83_30 (by norm_num)

theorem c22240R_83_28 : rowsJ2 83 84 59 340 ≤ 13771544919164 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2012 c22240R_83_29 (by norm_num)

theorem c22240R_83_27 : rowsJ2 83 84 58 340 ≤ 13771544919164 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2011 c22240R_83_28 (by norm_num)

theorem c22240R_83_26 : rowsJ2 83 84 57 340 ≤ 13829174573837 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2010 c22240R_83_27 (by norm_num)

theorem c22240R_83_25 : rowsJ2 83 84 56 340 ≤ 13944892846644 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2009 c22240R_83_26 (by norm_num)

theorem c22240R_83_24 : rowsJ2 83 84 55 340 ≤ 14117198717197 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2008 c22240R_83_25 (by norm_num)

theorem c22240R_83_23 : rowsJ2 83 84 54 340 ≤ 14346599910694 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2007 c22240R_83_24 (by norm_num)

theorem c22240R_83_22 : rowsJ2 83 84 53 340 ≤ 14631694941806 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2006 c22240R_83_23 (by norm_num)

theorem c22240R_83_21 : rowsJ2 83 84 52 340 ≤ 14973039882655 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2005 c22240R_83_22 (by norm_num)

theorem c22240R_83_20 : rowsJ2 83 84 51 340 ≤ 15369329553832 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2004 c22240R_83_21 (by norm_num)

theorem c22240R_83_19 : rowsJ2 83 84 50 340 ≤ 15821168392593 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2003 c22240R_83_20 (by norm_num)

theorem c22240R_83_18 : rowsJ2 83 84 49 340 ≤ 16327344881004 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2002 c22240R_83_19 (by norm_num)

theorem c22240R_83_17 : rowsJ2 83 84 48 340 ≤ 16831341072820 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2001 c22240R_83_18 (by norm_num)

theorem c22240R_83_16 : rowsJ2 83 84 47 340 ≤ 17217795592839 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_2000 c22240R_83_17 (by norm_num)

theorem c22240R_83_15 : rowsJ2 83 84 46 340 ≤ 17493271506164 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_1999 c22240R_83_16 (by norm_num)

theorem c22240R_83_14 : rowsJ2 83 84 45 340 ≤ 17661574976199 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_1998 c22240R_83_15 (by norm_num)

theorem c22240R_83_13 : rowsJ2 83 84 44 340 ≤ 17719125600709 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_1997 c22240R_83_14 (by norm_num)

theorem c22240R_83_12 : rowsJ2 83 84 43 340 ≤ 20124823024157 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_1996 c22240R_83_13 (by norm_num)

theorem c22240R_83_11 : rowsJ2 83 84 42 340 ≤ 24269415077960 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_1995 c22240R_83_12 (by norm_num)

theorem c22240R_83_10 : rowsJ2 83 84 41 340 ≤ 29315255985178 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_1994 c22240R_83_11 (by norm_num)

theorem c22240R_83_9 : rowsJ2 83 84 39 340 ≤ 39639948301287 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_1993 c22240R_83_10 (by norm_num)

theorem c22240R_83_8 : rowsJ2 83 84 36 340 ≤ 47806302838961 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_1992 c22240R_83_9 (by norm_num)

theorem c22240R_83_7 : rowsJ2 83 84 32 340 ≤ 49507754390838 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_1991 c22240R_83_8 (by norm_num)

theorem c22240R_83_6 : rowsJ2 83 84 29 340 ≤ 49507754390838 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_1990 c22240R_83_7 (by norm_num)

theorem c22240R_83_5 : rowsJ2 83 84 26 340 ≤ 49507754390838 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_1989 c22240R_83_6 (by norm_num)

theorem c22240R_83_4 : rowsJ2 83 84 24 340 ≤ 49507754390838 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_1988 c22240R_83_5 (by norm_num)

theorem c22240R_83_3 : rowsJ2 83 84 22 340 ≤ 49507754390838 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_1987 c22240R_83_4 (by norm_num)

theorem c22240R_83_2 : rowsJ2 83 84 20 340 ≤ 49513482689555 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_1986 c22240R_83_3 (by norm_num)

theorem c22240R_83_1 : rowsJ2 83 84 17 340 ≤ 49530509308049 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_1985 c22240R_83_2 (by norm_num)

theorem c22240R_83_0 : rowsJ2 83 84 0 340 ≤ 49685778889596 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22240R_1984 c22240R_83_1 (by norm_num)

theorem hr22240R_83 : rows2 83 84 ≤ 49685778889596 := rows2_le_of_rowsJ2 83 84 c22240R_83_0

theorem c22240R_84_44 : rowsJ2 84 85 83 340 ≤ 6804132209364 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2073 rows22240R_2074 (by norm_num)

theorem c22240R_84_43 : rowsJ2 84 85 82 340 ≤ 9102927526730 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2072 c22240R_84_44 (by norm_num)

theorem c22240R_84_42 : rowsJ2 84 85 81 340 ≤ 11010760926724 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2071 c22240R_84_43 (by norm_num)

theorem c22240R_84_41 : rowsJ2 84 85 80 340 ≤ 12661342652930 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2070 c22240R_84_42 (by norm_num)

theorem c22240R_84_40 : rowsJ2 84 85 78 340 ≤ 15390636864342 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2069 c22240R_84_41 (by norm_num)

theorem c22240R_84_39 : rowsJ2 84 85 76 340 ≤ 16223102830853 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2068 c22240R_84_40 (by norm_num)

theorem c22240R_84_38 : rowsJ2 84 85 73 340 ≤ 16223102830853 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2067 c22240R_84_39 (by norm_num)

theorem c22240R_84_37 : rowsJ2 84 85 70 340 ≤ 16223102830853 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2066 c22240R_84_38 (by norm_num)

theorem c22240R_84_36 : rowsJ2 84 85 68 340 ≤ 16223102830853 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2065 c22240R_84_37 (by norm_num)

theorem c22240R_84_35 : rowsJ2 84 85 66 340 ≤ 16223102830853 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2064 c22240R_84_36 (by norm_num)

theorem c22240R_84_34 : rowsJ2 84 85 64 340 ≤ 16223102830853 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2063 c22240R_84_35 (by norm_num)

theorem c22240R_84_33 : rowsJ2 84 85 63 340 ≤ 16223102830853 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2062 c22240R_84_34 (by norm_num)

theorem c22240R_84_32 : rowsJ2 84 85 62 340 ≤ 16223102830853 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2061 c22240R_84_33 (by norm_num)

theorem c22240R_84_31 : rowsJ2 84 85 61 340 ≤ 16223102830853 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2060 c22240R_84_32 (by norm_num)

theorem c22240R_84_30 : rowsJ2 84 85 60 340 ≤ 16223102830853 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2059 c22240R_84_31 (by norm_num)

theorem c22240R_84_29 : rowsJ2 84 85 59 340 ≤ 16223102830853 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2058 c22240R_84_30 (by norm_num)

theorem c22240R_84_28 : rowsJ2 84 85 58 340 ≤ 16223102830853 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2057 c22240R_84_29 (by norm_num)

theorem c22240R_84_27 : rowsJ2 84 85 57 340 ≤ 16223102830853 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2056 c22240R_84_28 (by norm_num)

theorem c22240R_84_26 : rowsJ2 84 85 56 340 ≤ 16280848532660 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2055 c22240R_84_27 (by norm_num)

theorem c22240R_84_25 : rowsJ2 84 85 55 340 ≤ 16338496986944 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2054 c22240R_84_26 (by norm_num)

theorem c22240R_84_24 : rowsJ2 84 85 54 340 ≤ 16452961655864 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2053 c22240R_84_25 (by norm_num)

theorem c22240R_84_23 : rowsJ2 84 85 53 340 ≤ 16567278109348 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2052 c22240R_84_24 (by norm_num)

theorem c22240R_84_22 : rowsJ2 84 85 52 340 ≤ 16737583620574 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2051 c22240R_84_23 (by norm_num)

theorem c22240R_84_21 : rowsJ2 84 85 51 340 ≤ 16907735181397 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2050 c22240R_84_22 (by norm_num)

theorem c22240R_84_20 : rowsJ2 84 85 50 340 ≤ 17133148490698 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2049 c22240R_84_21 (by norm_num)

theorem c22240R_84_19 : rowsJ2 84 85 49 340 ≤ 17358446712095 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2048 c22240R_84_20 (by norm_num)

theorem c22240R_84_18 : rowsJ2 84 85 48 340 ≤ 17638377351714 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2047 c22240R_84_19 (by norm_num)

theorem c22240R_84_17 : rowsJ2 84 85 47 340 ≤ 17859586543674 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2046 c22240R_84_18 (by norm_num)

theorem c22240R_84_16 : rowsJ2 84 85 46 340 ≤ 18079469643985 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2045 c22240R_84_17 (by norm_num)

theorem c22240R_84_15 : rowsJ2 84 85 45 340 ≤ 18246484818230 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2044 c22240R_84_16 (by norm_num)

theorem c22240R_84_14 : rowsJ2 84 85 44 340 ≤ 21457475531101 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2043 c22240R_84_15 (by norm_num)

theorem c22240R_84_13 : rowsJ2 84 85 43 340 ≤ 26644203998926 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2042 c22240R_84_14 (by norm_num)

theorem c22240R_84_12 : rowsJ2 84 85 42 340 ≤ 33199783642881 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2041 c22240R_84_13 (by norm_num)

theorem c22240R_84_11 : rowsJ2 84 85 41 340 ≤ 40290344533611 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2040 c22240R_84_12 (by norm_num)

theorem c22240R_84_10 : rowsJ2 84 85 40 340 ≤ 46281564179020 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2039 c22240R_84_11 (by norm_num)

theorem c22240R_84_9 : rowsJ2 84 85 38 340 ≤ 55373342252541 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2038 c22240R_84_10 (by norm_num)

theorem c22240R_84_8 : rowsJ2 84 85 35 340 ≤ 61492472597126 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2037 c22240R_84_9 (by norm_num)

theorem c22240R_84_7 : rowsJ2 84 85 31 340 ≤ 62356546868309 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2036 c22240R_84_8 (by norm_num)

theorem c22240R_84_6 : rowsJ2 84 85 28 340 ≤ 62356546868309 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2035 c22240R_84_7 (by norm_num)

theorem c22240R_84_5 : rowsJ2 84 85 25 340 ≤ 62356546868309 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2034 c22240R_84_6 (by norm_num)

theorem c22240R_84_4 : rowsJ2 84 85 23 340 ≤ 62356546868309 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2033 c22240R_84_5 (by norm_num)

theorem c22240R_84_3 : rowsJ2 84 85 21 340 ≤ 62356546868309 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2032 c22240R_84_4 (by norm_num)

theorem c22240R_84_2 : rowsJ2 84 85 19 340 ≤ 62362317492736 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2031 c22240R_84_3 (by norm_num)

theorem c22240R_84_1 : rowsJ2 84 85 17 340 ≤ 62372810430871 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2030 c22240R_84_2 (by norm_num)

theorem c22240R_84_0 : rowsJ2 84 85 0 340 ≤ 62489021416256 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22240R_2029 c22240R_84_1 (by norm_num)

theorem hr22240R_84 : rows2 84 85 ≤ 62489021416256 := rows2_le_of_rowsJ2 84 85 c22240R_84_0

theorem c22240R_85_43 : rowsJ2 85 86 84 340 ≤ 8781337898803 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2118 rows22240R_2119 (by norm_num)

theorem c22240R_85_42 : rowsJ2 85 86 83 340 ≤ 11708540009757 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2117 c22240R_85_43 (by norm_num)

theorem c22240R_85_41 : rowsJ2 85 86 82 340 ≤ 13871793499919 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2116 c22240R_85_42 (by norm_num)

theorem c22240R_85_40 : rowsJ2 85 86 81 340 ≤ 15528406531491 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2115 c22240R_85_41 (by norm_num)

theorem c22240R_85_39 : rowsJ2 85 86 80 340 ≤ 16941394984682 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2114 c22240R_85_40 (by norm_num)

theorem c22240R_85_38 : rowsJ2 85 86 78 340 ≤ 19108580949918 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2113 c22240R_85_39 (by norm_num)

theorem c22240R_85_37 : rowsJ2 85 86 75 340 ≤ 19720404508703 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2112 c22240R_85_38 (by norm_num)

theorem c22240R_85_36 : rowsJ2 85 86 72 340 ≤ 19720404508703 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2111 c22240R_85_37 (by norm_num)

theorem c22240R_85_35 : rowsJ2 85 86 69 340 ≤ 19720404508703 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2110 c22240R_85_36 (by norm_num)

theorem c22240R_85_34 : rowsJ2 85 86 67 340 ≤ 19720404508703 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2109 c22240R_85_35 (by norm_num)

theorem c22240R_85_33 : rowsJ2 85 86 65 340 ≤ 19720404508703 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2108 c22240R_85_34 (by norm_num)

theorem c22240R_85_32 : rowsJ2 85 86 63 340 ≤ 19720404508703 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2107 c22240R_85_33 (by norm_num)

theorem c22240R_85_31 : rowsJ2 85 86 62 340 ≤ 19720404508703 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2106 c22240R_85_32 (by norm_num)

theorem c22240R_85_30 : rowsJ2 85 86 61 340 ≤ 19720404508703 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2105 c22240R_85_31 (by norm_num)

theorem c22240R_85_29 : rowsJ2 85 86 60 340 ≤ 19720404508703 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2104 c22240R_85_30 (by norm_num)

theorem c22240R_85_28 : rowsJ2 85 86 59 340 ≤ 19720404508703 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2103 c22240R_85_29 (by norm_num)

theorem c22240R_85_27 : rowsJ2 85 86 58 340 ≤ 19720404508703 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2102 c22240R_85_28 (by norm_num)

theorem c22240R_85_26 : rowsJ2 85 86 57 340 ≤ 19720404508703 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2101 c22240R_85_27 (by norm_num)

theorem c22240R_85_25 : rowsJ2 85 86 56 340 ≤ 19720404508703 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2100 c22240R_85_26 (by norm_num)

theorem c22240R_85_24 : rowsJ2 85 86 55 340 ≤ 19720404508703 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2099 c22240R_85_25 (by norm_num)

theorem c22240R_85_23 : rowsJ2 85 86 54 340 ≤ 19720404508703 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2098 c22240R_85_24 (by norm_num)

theorem c22240R_85_22 : rowsJ2 85 86 53 340 ≤ 19720404508703 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2097 c22240R_85_23 (by norm_num)

theorem c22240R_85_21 : rowsJ2 85 86 52 340 ≤ 19720404508703 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2096 c22240R_85_22 (by norm_num)

theorem c22240R_85_20 : rowsJ2 85 86 51 340 ≤ 19720404508703 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2095 c22240R_85_21 (by norm_num)

theorem c22240R_85_19 : rowsJ2 85 86 50 340 ≤ 19720404508703 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2094 c22240R_85_20 (by norm_num)

theorem c22240R_85_18 : rowsJ2 85 86 49 340 ≤ 19720404508703 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2093 c22240R_85_19 (by norm_num)

theorem c22240R_85_17 : rowsJ2 85 86 48 340 ≤ 19720404508703 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2092 c22240R_85_18 (by norm_num)

theorem c22240R_85_16 : rowsJ2 85 86 47 340 ≤ 19775264978104 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2091 c22240R_85_17 (by norm_num)

theorem c22240R_85_15 : rowsJ2 85 86 46 340 ≤ 19885565188648 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2090 c22240R_85_16 (by norm_num)

theorem c22240R_85_14 : rowsJ2 85 86 45 340 ≤ 23451901639790 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2089 c22240R_85_15 (by norm_num)

theorem c22240R_85_13 : rowsJ2 85 86 44 340 ≤ 29717192706009 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2088 c22240R_85_14 (by norm_num)

theorem c22240R_85_12 : rowsJ2 85 86 43 340 ≤ 37619200345858 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2087 c22240R_85_13 (by norm_num)

theorem c22240R_85_11 : rowsJ2 85 86 42 340 ≤ 46515354434429 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2086 c22240R_85_12 (by norm_num)

theorem c22240R_85_10 : rowsJ2 85 86 41 340 ≤ 54115311728301 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2085 c22240R_85_11 (by norm_num)

theorem c22240R_85_9 : rowsJ2 85 86 39 340 ≤ 65897797044559 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2084 c22240R_85_10 (by norm_num)

theorem c22240R_85_8 : rowsJ2 85 86 36 340 ≤ 76180376155550 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2083 c22240R_85_9 (by norm_num)

theorem c22240R_85_7 : rowsJ2 85 86 32 340 ≤ 78344096579268 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2082 c22240R_85_8 (by norm_num)

theorem c22240R_85_6 : rowsJ2 85 86 28 340 ≤ 78344096579268 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2081 c22240R_85_7 (by norm_num)

theorem c22240R_85_5 : rowsJ2 85 86 25 340 ≤ 78344096579268 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2080 c22240R_85_6 (by norm_num)

theorem c22240R_85_4 : rowsJ2 85 86 23 340 ≤ 78344096579268 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2079 c22240R_85_5 (by norm_num)

theorem c22240R_85_3 : rowsJ2 85 86 21 340 ≤ 78344096579268 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2078 c22240R_85_4 (by norm_num)

theorem c22240R_85_2 : rowsJ2 85 86 19 340 ≤ 78346025259009 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2077 c22240R_85_3 (by norm_num)

theorem c22240R_85_1 : rowsJ2 85 86 17 340 ≤ 78354727445803 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2076 c22240R_85_2 (by norm_num)

theorem c22240R_85_0 : rowsJ2 85 86 0 340 ≤ 78436510613355 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22240R_2075 c22240R_85_1 (by norm_num)

theorem hr22240R_85 : rows2 85 86 ≤ 78436510613355 := rows2_le_of_rowsJ2 85 86 c22240R_85_0

theorem c22240R_86_44 : rowsJ2 86 87 85 340 ≤ 11113997331192 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2164 rows22240R_2165 (by norm_num)

theorem c22240R_86_43 : rowsJ2 86 87 84 340 ≤ 14955924618709 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2163 c22240R_86_44 (by norm_num)

theorem c22240R_86_42 : rowsJ2 86 87 83 340 ≤ 17870517892637 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2162 c22240R_86_43 (by norm_num)

theorem c22240R_86_41 : rowsJ2 86 87 82 340 ≤ 20020615831145 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2161 c22240R_86_42 (by norm_num)

theorem c22240R_86_40 : rowsJ2 86 87 81 340 ≤ 21543321320053 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2160 c22240R_86_41 (by norm_num)

theorem c22240R_86_39 : rowsJ2 86 87 80 340 ≤ 22707619148642 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2159 c22240R_86_40 (by norm_num)

theorem c22240R_86_38 : rowsJ2 86 87 79 340 ≤ 23754757330023 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2158 c22240R_86_39 (by norm_num)

theorem c22240R_86_37 : rowsJ2 86 87 77 340 ≤ 25070815083566 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2157 c22240R_86_38 (by norm_num)

theorem c22240R_86_36 : rowsJ2 86 87 74 340 ≤ 25136865224295 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2156 c22240R_86_37 (by norm_num)

theorem c22240R_86_35 : rowsJ2 86 87 71 340 ≤ 25136865224295 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2155 c22240R_86_36 (by norm_num)

theorem c22240R_86_34 : rowsJ2 86 87 68 340 ≤ 25136865224295 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2154 c22240R_86_35 (by norm_num)

theorem c22240R_86_33 : rowsJ2 86 87 66 340 ≤ 25136865224295 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2153 c22240R_86_34 (by norm_num)

theorem c22240R_86_32 : rowsJ2 86 87 64 340 ≤ 25136865224295 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2152 c22240R_86_33 (by norm_num)

theorem c22240R_86_31 : rowsJ2 86 87 62 340 ≤ 25136865224295 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2151 c22240R_86_32 (by norm_num)

theorem c22240R_86_30 : rowsJ2 86 87 61 340 ≤ 25136865224295 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2150 c22240R_86_31 (by norm_num)

theorem c22240R_86_29 : rowsJ2 86 87 60 340 ≤ 25136865224295 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2149 c22240R_86_30 (by norm_num)

theorem c22240R_86_28 : rowsJ2 86 87 59 340 ≤ 25136865224295 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2148 c22240R_86_29 (by norm_num)

theorem c22240R_86_27 : rowsJ2 86 87 58 340 ≤ 25136865224295 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2147 c22240R_86_28 (by norm_num)

theorem c22240R_86_26 : rowsJ2 86 87 57 340 ≤ 25136865224295 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2146 c22240R_86_27 (by norm_num)

theorem c22240R_86_25 : rowsJ2 86 87 56 340 ≤ 25136865224295 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2145 c22240R_86_26 (by norm_num)

theorem c22240R_86_24 : rowsJ2 86 87 55 340 ≤ 25136865224295 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2144 c22240R_86_25 (by norm_num)

theorem c22240R_86_23 : rowsJ2 86 87 54 340 ≤ 25136865224295 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2143 c22240R_86_24 (by norm_num)

theorem c22240R_86_22 : rowsJ2 86 87 53 340 ≤ 25136865224295 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2142 c22240R_86_23 (by norm_num)

theorem c22240R_86_21 : rowsJ2 86 87 52 340 ≤ 25136865224295 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2141 c22240R_86_22 (by norm_num)

theorem c22240R_86_20 : rowsJ2 86 87 51 340 ≤ 25136865224295 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2140 c22240R_86_21 (by norm_num)

theorem c22240R_86_19 : rowsJ2 86 87 50 340 ≤ 25136865224295 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2139 c22240R_86_20 (by norm_num)

theorem c22240R_86_18 : rowsJ2 86 87 49 340 ≤ 25136865224295 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2138 c22240R_86_19 (by norm_num)

theorem c22240R_86_17 : rowsJ2 86 87 48 340 ≤ 25136865224295 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2137 c22240R_86_18 (by norm_num)

theorem c22240R_86_16 : rowsJ2 86 87 47 340 ≤ 25136865224295 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2136 c22240R_86_17 (by norm_num)

theorem c22240R_86_15 : rowsJ2 86 87 46 340 ≤ 29290694165226 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2135 c22240R_86_16 (by norm_num)

theorem c22240R_86_14 : rowsJ2 86 87 45 340 ≤ 36552566396346 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2134 c22240R_86_15 (by norm_num)

theorem c22240R_86_13 : rowsJ2 86 87 44 340 ≤ 46222683469188 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2133 c22240R_86_14 (by norm_num)

theorem c22240R_86_12 : rowsJ2 86 87 43 340 ≤ 57191023837261 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2132 c22240R_86_13 (by norm_num)

theorem c22240R_86_11 : rowsJ2 86 87 42 340 ≤ 66771668863486 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2131 c22240R_86_12 (by norm_num)

theorem c22240R_86_10 : rowsJ2 86 87 41 340 ≤ 74976525490495 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2130 c22240R_86_11 (by norm_num)

theorem c22240R_86_9 : rowsJ2 86 87 40 340 ≤ 81920531158196 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2129 c22240R_86_10 (by norm_num)

theorem c22240R_86_8 : rowsJ2 86 87 38 340 ≤ 92516795379279 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2128 c22240R_86_9 (by norm_num)

theorem c22240R_86_7 : rowsJ2 86 87 35 340 ≤ 100604354797344 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2127 c22240R_86_8 (by norm_num)

theorem c22240R_86_6 : rowsJ2 86 87 31 340 ≤ 101651525869166 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2126 c22240R_86_7 (by norm_num)

theorem c22240R_86_5 : rowsJ2 86 87 27 340 ≤ 101651525869166 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2125 c22240R_86_6 (by norm_num)

theorem c22240R_86_4 : rowsJ2 86 87 24 340 ≤ 101651525869166 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2124 c22240R_86_5 (by norm_num)

theorem c22240R_86_3 : rowsJ2 86 87 22 340 ≤ 101651525869166 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2123 c22240R_86_4 (by norm_num)

theorem c22240R_86_2 : rowsJ2 86 87 20 340 ≤ 101651525869166 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2122 c22240R_86_3 (by norm_num)

theorem c22240R_86_1 : rowsJ2 86 87 17 340 ≤ 101657387192645 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2121 c22240R_86_2 (by norm_num)

theorem c22240R_86_0 : rowsJ2 86 87 0 340 ≤ 101714287129935 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22240R_2120 c22240R_86_1 (by norm_num)

theorem hr22240R_86 : rows2 86 87 ≤ 101714287129935 := rows2_le_of_rowsJ2 86 87 c22240R_86_0

theorem c22240R_87_43 : rowsJ2 87 88 86 340 ≤ 13848538994380 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2209 rows22240R_2210 (by norm_num)

theorem c22240R_87_42 : rowsJ2 87 88 85 340 ≤ 18769605201362 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2208 c22240R_87_43 (by norm_num)

theorem c22240R_87_41 : rowsJ2 87 88 84 340 ≤ 22602725901936 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2207 c22240R_87_42 (by norm_num)

theorem c22240R_87_40 : rowsJ2 87 88 83 340 ≤ 25505554825622 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2206 c22240R_87_41 (by norm_num)

theorem c22240R_87_39 : rowsJ2 87 88 82 340 ≤ 27643009703185 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2205 c22240R_87_40 (by norm_num)

theorem c22240R_87_38 : rowsJ2 87 88 81 340 ≤ 29153952033167 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2204 c22240R_87_39 (by norm_num)

theorem c22240R_87_37 : rowsJ2 87 88 80 340 ≤ 30186773393533 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2203 c22240R_87_38 (by norm_num)

theorem c22240R_87_36 : rowsJ2 87 88 79 340 ≤ 30988486094274 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2202 c22240R_87_37 (by norm_num)

theorem c22240R_87_35 : rowsJ2 87 88 77 340 ≤ 31956098583477 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2201 c22240R_87_36 (by norm_num)

theorem c22240R_87_34 : rowsJ2 87 88 74 340 ≤ 32021547195101 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2200 c22240R_87_35 (by norm_num)

theorem c22240R_87_33 : rowsJ2 87 88 70 340 ≤ 32021547195101 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2199 c22240R_87_34 (by norm_num)

theorem c22240R_87_32 : rowsJ2 87 88 67 340 ≤ 32021547195101 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2198 c22240R_87_33 (by norm_num)

theorem c22240R_87_31 : rowsJ2 87 88 65 340 ≤ 32021547195101 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2197 c22240R_87_32 (by norm_num)

theorem c22240R_87_30 : rowsJ2 87 88 63 340 ≤ 32021547195101 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2196 c22240R_87_31 (by norm_num)

theorem c22240R_87_29 : rowsJ2 87 88 61 340 ≤ 32021547195101 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2195 c22240R_87_30 (by norm_num)

theorem c22240R_87_28 : rowsJ2 87 88 60 340 ≤ 32021547195101 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2194 c22240R_87_29 (by norm_num)

theorem c22240R_87_27 : rowsJ2 87 88 59 340 ≤ 32021547195101 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2193 c22240R_87_28 (by norm_num)

theorem c22240R_87_26 : rowsJ2 87 88 58 340 ≤ 32021547195101 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2192 c22240R_87_27 (by norm_num)

theorem c22240R_87_25 : rowsJ2 87 88 57 340 ≤ 32021547195101 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2191 c22240R_87_26 (by norm_num)

theorem c22240R_87_24 : rowsJ2 87 88 56 340 ≤ 32021547195101 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2190 c22240R_87_25 (by norm_num)

theorem c22240R_87_23 : rowsJ2 87 88 55 340 ≤ 32021547195101 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2189 c22240R_87_24 (by norm_num)

theorem c22240R_87_22 : rowsJ2 87 88 54 340 ≤ 32021547195101 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2188 c22240R_87_23 (by norm_num)

theorem c22240R_87_21 : rowsJ2 87 88 53 340 ≤ 32021547195101 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2187 c22240R_87_22 (by norm_num)

theorem c22240R_87_20 : rowsJ2 87 88 52 340 ≤ 32021547195101 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2186 c22240R_87_21 (by norm_num)

theorem c22240R_87_19 : rowsJ2 87 88 51 340 ≤ 32021547195101 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2185 c22240R_87_20 (by norm_num)

theorem c22240R_87_18 : rowsJ2 87 88 50 340 ≤ 32021547195101 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2184 c22240R_87_19 (by norm_num)

theorem c22240R_87_17 : rowsJ2 87 88 49 340 ≤ 32021547195101 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2183 c22240R_87_18 (by norm_num)

theorem c22240R_87_16 : rowsJ2 87 88 48 340 ≤ 32021547195101 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2182 c22240R_87_17 (by norm_num)

theorem c22240R_87_15 : rowsJ2 87 88 47 340 ≤ 36337175807378 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2181 c22240R_87_16 (by norm_num)

theorem c22240R_87_14 : rowsJ2 87 88 46 340 ≤ 44391608271334 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2180 c22240R_87_15 (by norm_num)

theorem c22240R_87_13 : rowsJ2 87 88 45 340 ≤ 55200213839411 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2179 c22240R_87_14 (by norm_num)

theorem c22240R_87_12 : rowsJ2 87 88 44 340 ≤ 68121432211751 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2178 c22240R_87_13 (by norm_num)

theorem c22240R_87_11 : rowsJ2 87 88 43 340 ≤ 79663320930738 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2177 c22240R_87_12 (by norm_num)

theorem c22240R_87_10 : rowsJ2 87 88 42 340 ≤ 89835294673071 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2176 c22240R_87_11 (by norm_num)

theorem c22240R_87_9 : rowsJ2 87 88 41 340 ≤ 98649340087073 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2175 c22240R_87_10 (by norm_num)

theorem c22240R_87_8 : rowsJ2 87 88 39 340 ≤ 112367704353129 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2174 c22240R_87_9 (by norm_num)

theorem c22240R_87_7 : rowsJ2 87 88 37 340 ≤ 121703829371818 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2173 c22240R_87_8 (by norm_num)

theorem c22240R_87_6 : rowsJ2 87 88 34 340 ≤ 127490370230095 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2172 c22240R_87_7 (by norm_num)

theorem c22240R_87_5 : rowsJ2 87 88 29 340 ≤ 127875929163260 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2171 c22240R_87_6 (by norm_num)

theorem c22240R_87_4 : rowsJ2 87 88 25 340 ≤ 127875929163260 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2170 c22240R_87_5 (by norm_num)

theorem c22240R_87_3 : rowsJ2 87 88 22 340 ≤ 127875929163260 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2169 c22240R_87_4 (by norm_num)

theorem c22240R_87_2 : rowsJ2 87 88 20 340 ≤ 127875929163260 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2168 c22240R_87_3 (by norm_num)

theorem c22240R_87_1 : rowsJ2 87 88 17 340 ≤ 127877888687669 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2167 c22240R_87_2 (by norm_num)

theorem c22240R_87_0 : rowsJ2 87 88 0 340 ≤ 127915757781913 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22240R_2166 c22240R_87_1 (by norm_num)

theorem hr22240R_87 : rows2 87 88 ≤ 127915757781913 := rows2_le_of_rowsJ2 87 88 c22240R_87_0

theorem c22240R_88_43 : rowsJ2 88 89 87 340 ≤ 16945158068780 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2254 rows22240R_2255 (by norm_num)

theorem c22240R_88_42 : rowsJ2 88 89 86 340 ≤ 23149902833628 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2253 c22240R_88_43 (by norm_num)

theorem c22240R_88_41 : rowsJ2 88 89 85 340 ≤ 28070096261076 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2252 c22240R_88_42 (by norm_num)

theorem c22240R_88_40 : rowsJ2 88 89 84 340 ≤ 31895856148205 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2251 c22240R_88_41 (by norm_num)

theorem c22240R_88_39 : rowsJ2 88 89 83 340 ≤ 34787793828384 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2250 c22240R_88_40 (by norm_num)

theorem c22240R_88_38 : rowsJ2 88 89 82 340 ≤ 36913068172689 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2249 c22240R_88_39 (by norm_num)

theorem c22240R_88_37 : rowsJ2 88 89 81 340 ≤ 38412514918943 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2248 c22240R_88_38 (by norm_num)

theorem c22240R_88_36 : rowsJ2 88 89 80 340 ≤ 39435926561718 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2247 c22240R_88_37 (by norm_num)

theorem c22240R_88_35 : rowsJ2 88 89 79 340 ≤ 40109422886397 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2246 c22240R_88_36 (by norm_num)

theorem c22240R_88_34 : rowsJ2 88 89 77 340 ≤ 40950601666612 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2245 c22240R_88_35 (by norm_num)

theorem c22240R_88_33 : rowsJ2 88 89 73 340 ≤ 41015454687035 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2244 c22240R_88_34 (by norm_num)

theorem c22240R_88_32 : rowsJ2 88 89 69 340 ≤ 41015454687035 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2243 c22240R_88_33 (by norm_num)

theorem c22240R_88_31 : rowsJ2 88 89 66 340 ≤ 41015454687035 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2242 c22240R_88_32 (by norm_num)

theorem c22240R_88_30 : rowsJ2 88 89 64 340 ≤ 41015454687035 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2241 c22240R_88_31 (by norm_num)

theorem c22240R_88_29 : rowsJ2 88 89 62 340 ≤ 41015454687035 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2240 c22240R_88_30 (by norm_num)

theorem c22240R_88_28 : rowsJ2 88 89 60 340 ≤ 41015454687035 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2239 c22240R_88_29 (by norm_num)

theorem c22240R_88_27 : rowsJ2 88 89 59 340 ≤ 41015454687035 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2238 c22240R_88_28 (by norm_num)

theorem c22240R_88_26 : rowsJ2 88 89 58 340 ≤ 41015454687035 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2237 c22240R_88_27 (by norm_num)

theorem c22240R_88_25 : rowsJ2 88 89 57 340 ≤ 41015454687035 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2236 c22240R_88_26 (by norm_num)

theorem c22240R_88_24 : rowsJ2 88 89 56 340 ≤ 41015454687035 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2235 c22240R_88_25 (by norm_num)

theorem c22240R_88_23 : rowsJ2 88 89 55 340 ≤ 41015454687035 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2234 c22240R_88_24 (by norm_num)

theorem c22240R_88_22 : rowsJ2 88 89 54 340 ≤ 41015454687035 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2233 c22240R_88_23 (by norm_num)

theorem c22240R_88_21 : rowsJ2 88 89 53 340 ≤ 41015454687035 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2232 c22240R_88_22 (by norm_num)

theorem c22240R_88_20 : rowsJ2 88 89 52 340 ≤ 41015454687035 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2231 c22240R_88_21 (by norm_num)

theorem c22240R_88_19 : rowsJ2 88 89 51 340 ≤ 41015454687035 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2230 c22240R_88_20 (by norm_num)

theorem c22240R_88_18 : rowsJ2 88 89 50 340 ≤ 41015454687035 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2229 c22240R_88_19 (by norm_num)

theorem c22240R_88_17 : rowsJ2 88 89 49 340 ≤ 41015454687035 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2228 c22240R_88_18 (by norm_num)

theorem c22240R_88_16 : rowsJ2 88 89 48 340 ≤ 45302871161616 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2227 c22240R_88_17 (by norm_num)

theorem c22240R_88_15 : rowsJ2 88 89 47 340 ≤ 54298771033666 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2226 c22240R_88_16 (by norm_num)

theorem c22240R_88_14 : rowsJ2 88 89 46 340 ≤ 66673360117705 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2225 c22240R_88_15 (by norm_num)

theorem c22240R_88_13 : rowsJ2 88 89 45 340 ≤ 81393397018995 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2224 c22240R_88_14 (by norm_num)

theorem c22240R_88_12 : rowsJ2 88 89 44 340 ≤ 94870091004625 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2223 c22240R_88_13 (by norm_num)

theorem c22240R_88_11 : rowsJ2 88 89 43 340 ≤ 106984967314829 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2222 c22240R_88_12 (by norm_num)

theorem c22240R_88_10 : rowsJ2 88 89 42 340 ≤ 117747534685972 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2221 c22240R_88_11 (by norm_num)

theorem c22240R_88_9 : rowsJ2 88 89 41 340 ≤ 127169860337292 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2220 c22240R_88_10 (by norm_num)

theorem c22240R_88_8 : rowsJ2 88 89 40 340 ≤ 135266811196959 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2219 c22240R_88_9 (by norm_num)

theorem c22240R_88_7 : rowsJ2 88 89 38 340 ≤ 147663062564133 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2218 c22240R_88_8 (by norm_num)

theorem c22240R_88_6 : rowsJ2 88 89 35 340 ≤ 157820182734695 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2217 c22240R_88_7 (by norm_num)

theorem c22240R_88_5 : rowsJ2 88 89 31 340 ≤ 159441686946668 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2216 c22240R_88_6 (by norm_num)

theorem c22240R_88_4 : rowsJ2 88 89 26 340 ≤ 159441686946668 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2215 c22240R_88_5 (by norm_num)

theorem c22240R_88_3 : rowsJ2 88 89 23 340 ≤ 159441686946668 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2214 c22240R_88_4 (by norm_num)

theorem c22240R_88_2 : rowsJ2 88 89 20 340 ≤ 159441686946668 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2213 c22240R_88_3 (by norm_num)

theorem c22240R_88_1 : rowsJ2 88 89 17 340 ≤ 159441686946668 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2212 c22240R_88_2 (by norm_num)

theorem c22240R_88_0 : rowsJ2 88 89 0 340 ≤ 159464332740011 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22240R_2211 c22240R_88_1 (by norm_num)

theorem hr22240R_88 : rows2 88 89 ≤ 159464332740011 := rows2_le_of_rowsJ2 88 89 c22240R_88_0

theorem c22240R_89_43 : rowsJ2 89 90 88 340 ≤ 18381455659397 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2299 rows22240R_2300 (by norm_num)

theorem c22240R_89_42 : rowsJ2 89 90 87 340 ≤ 26085535608187 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2298 c22240R_89_43 (by norm_num)

theorem c22240R_89_41 : rowsJ2 89 90 86 340 ≤ 32302637536412 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2297 c22240R_89_42 (by norm_num)

theorem c22240R_89_40 : rowsJ2 89 90 85 340 ≤ 37224259234267 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2296 c22240R_89_41 (by norm_num)

theorem c22240R_89_39 : rowsJ2 89 90 84 340 ≤ 41044201741580 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2295 c22240R_89_40 (by norm_num)

theorem c22240R_89_38 : rowsJ2 89 90 83 340 ≤ 43926152548697 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2294 c22240R_89_39 (by norm_num)

theorem c22240R_89_37 : rowsJ2 89 90 82 340 ≤ 46039746809267 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2293 c22240R_89_38 (by norm_num)

theorem c22240R_89_36 : rowsJ2 89 90 81 340 ≤ 47527941083630 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2292 c22240R_89_37 (by norm_num)

theorem c22240R_89_35 : rowsJ2 89 90 80 340 ≤ 48542031073668 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2291 c22240R_89_36 (by norm_num)

theorem c22240R_89_34 : rowsJ2 89 90 79 340 ≤ 49209395084262 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2290 c22240R_89_35 (by norm_num)

theorem c22240R_89_33 : rowsJ2 89 90 76 340 ≤ 49864243937682 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2289 c22240R_89_34 (by norm_num)

theorem c22240R_89_32 : rowsJ2 89 90 72 340 ≤ 49864243937682 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2288 c22240R_89_33 (by norm_num)

theorem c22240R_89_31 : rowsJ2 89 90 68 340 ≤ 49864243937682 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2287 c22240R_89_32 (by norm_num)

theorem c22240R_89_30 : rowsJ2 89 90 65 340 ≤ 49864243937682 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2286 c22240R_89_31 (by norm_num)

theorem c22240R_89_29 : rowsJ2 89 90 63 340 ≤ 49864243937682 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2285 c22240R_89_30 (by norm_num)

theorem c22240R_89_28 : rowsJ2 89 90 61 340 ≤ 49864243937682 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2284 c22240R_89_29 (by norm_num)

theorem c22240R_89_27 : rowsJ2 89 90 59 340 ≤ 49864243937682 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2283 c22240R_89_28 (by norm_num)

theorem c22240R_89_26 : rowsJ2 89 90 58 340 ≤ 49864243937682 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2282 c22240R_89_27 (by norm_num)

theorem c22240R_89_25 : rowsJ2 89 90 57 340 ≤ 49864243937682 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2281 c22240R_89_26 (by norm_num)

theorem c22240R_89_24 : rowsJ2 89 90 56 340 ≤ 49864243937682 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2280 c22240R_89_25 (by norm_num)

theorem c22240R_89_23 : rowsJ2 89 90 55 340 ≤ 49864243937682 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2279 c22240R_89_24 (by norm_num)

theorem c22240R_89_22 : rowsJ2 89 90 54 340 ≤ 49864243937682 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2278 c22240R_89_23 (by norm_num)

theorem c22240R_89_21 : rowsJ2 89 90 53 340 ≤ 49864243937682 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2277 c22240R_89_22 (by norm_num)

theorem c22240R_89_20 : rowsJ2 89 90 52 340 ≤ 49864243937682 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2276 c22240R_89_21 (by norm_num)

theorem c22240R_89_19 : rowsJ2 89 90 51 340 ≤ 49864243937682 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2275 c22240R_89_20 (by norm_num)

theorem c22240R_89_18 : rowsJ2 89 90 50 340 ≤ 49864243937682 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2274 c22240R_89_19 (by norm_num)

theorem c22240R_89_17 : rowsJ2 89 90 49 340 ≤ 53090897145475 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2273 c22240R_89_18 (by norm_num)

theorem c22240R_89_16 : rowsJ2 89 90 48 340 ≤ 60557054313650 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2272 c22240R_89_17 (by norm_num)

theorem c22240R_89_15 : rowsJ2 89 90 47 340 ≤ 72741826878428 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2271 c22240R_89_16 (by norm_num)

theorem c22240R_89_14 : rowsJ2 89 90 46 340 ≤ 89071498914479 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2270 c22240R_89_15 (by norm_num)

theorem c22240R_89_13 : rowsJ2 89 90 45 340 ≤ 104313434087487 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2269 c22240R_89_14 (by norm_num)

theorem c22240R_89_12 : rowsJ2 89 90 44 340 ≤ 118291401921858 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2268 c22240R_89_13 (by norm_num)

theorem c22240R_89_11 : rowsJ2 89 90 43 340 ≤ 130885692033549 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2267 c22240R_89_12 (by norm_num)

theorem c22240R_89_10 : rowsJ2 89 90 42 340 ≤ 142144059281011 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2266 c22240R_89_11 (by norm_num)

theorem c22240R_89_9 : rowsJ2 89 90 41 340 ≤ 152078628349287 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2265 c22240R_89_10 (by norm_num)

theorem c22240R_89_8 : rowsJ2 89 90 40 340 ≤ 160704308062440 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2264 c22240R_89_9 (by norm_num)

theorem c22240R_89_7 : rowsJ2 89 90 38 340 ≤ 174104148431607 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2263 c22240R_89_8 (by norm_num)

theorem c22240R_89_6 : rowsJ2 89 90 36 340 ≤ 182646285218689 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2262 c22240R_89_7 (by norm_num)

theorem c22240R_89_5 : rowsJ2 89 90 32 340 ≤ 187405738865537 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2261 c22240R_89_6 (by norm_num)

theorem c22240R_89_4 : rowsJ2 89 90 27 340 ≤ 187405738865537 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2260 c22240R_89_5 (by norm_num)

theorem c22240R_89_3 : rowsJ2 89 90 23 340 ≤ 187405738865537 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2259 c22240R_89_4 (by norm_num)

theorem c22240R_89_2 : rowsJ2 89 90 20 340 ≤ 187405738865537 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2258 c22240R_89_3 (by norm_num)

theorem c22240R_89_1 : rowsJ2 89 90 17 340 ≤ 187405738865537 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2257 c22240R_89_2 (by norm_num)

theorem c22240R_89_0 : rowsJ2 89 90 0 340 ≤ 187416159946440 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22240R_2256 c22240R_89_1 (by norm_num)

theorem hr22240R_89 : rows2 89 90 ≤ 187416159946440 := rows2_le_of_rowsJ2 89 90 c22240R_89_0

theorem c22240R_90_43 : rowsJ2 90 91 89 340 ≤ 15085358155886 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2344 rows22240R_2345 (by norm_num)

theorem c22240R_90_42 : rowsJ2 90 91 88 340 ≤ 23952492552076 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2343 c22240R_90_43 (by norm_num)

theorem c22240R_90_41 : rowsJ2 90 91 87 340 ≤ 31590624368720 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2342 c22240R_90_42 (by norm_num)

theorem c22240R_90_40 : rowsJ2 90 91 86 340 ≤ 37823672322964 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2341 c22240R_90_41 (by norm_num)

theorem c22240R_90_39 : rowsJ2 90 91 85 340 ≤ 42749147044156 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2340 c22240R_90_40 (by norm_num)

theorem c22240R_90_38 : rowsJ2 90 91 84 340 ≤ 46564824068889 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2339 c22240R_90_39 (by norm_num)

theorem c22240R_90_37 : rowsJ2 90 91 83 340 ≤ 49437789283922 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2338 c22240R_90_38 (by norm_num)

theorem c22240R_90_36 : rowsJ2 90 91 82 340 ≤ 51540251820060 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2337 c22240R_90_37 (by norm_num)

theorem c22240R_90_35 : rowsJ2 90 91 81 340 ≤ 53017402390131 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2336 c22240R_90_36 (by norm_num)

theorem c22240R_90_34 : rowsJ2 90 91 80 340 ≤ 54022256311409 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2335 c22240R_90_35 (by norm_num)

theorem c22240R_90_33 : rowsJ2 90 91 78 340 ≤ 55078563479766 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2334 c22240R_90_34 (by norm_num)

theorem c22240R_90_32 : rowsJ2 90 91 75 340 ≤ 55332434892377 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2333 c22240R_90_33 (by norm_num)

theorem c22240R_90_31 : rowsJ2 90 91 71 340 ≤ 55332434892377 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2332 c22240R_90_32 (by norm_num)

theorem c22240R_90_30 : rowsJ2 90 91 67 340 ≤ 55332434892377 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2331 c22240R_90_31 (by norm_num)

theorem c22240R_90_29 : rowsJ2 90 91 64 340 ≤ 55332434892377 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2330 c22240R_90_30 (by norm_num)

theorem c22240R_90_28 : rowsJ2 90 91 62 340 ≤ 55332434892377 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2329 c22240R_90_29 (by norm_num)

theorem c22240R_90_27 : rowsJ2 90 91 60 340 ≤ 55332434892377 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2328 c22240R_90_28 (by norm_num)

theorem c22240R_90_26 : rowsJ2 90 91 58 340 ≤ 55332434892377 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2327 c22240R_90_27 (by norm_num)

theorem c22240R_90_25 : rowsJ2 90 91 57 340 ≤ 55332434892377 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2326 c22240R_90_26 (by norm_num)

theorem c22240R_90_24 : rowsJ2 90 91 56 340 ≤ 55332434892377 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2325 c22240R_90_25 (by norm_num)

theorem c22240R_90_23 : rowsJ2 90 91 55 340 ≤ 55332434892377 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2324 c22240R_90_24 (by norm_num)

theorem c22240R_90_22 : rowsJ2 90 91 54 340 ≤ 55332434892377 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2323 c22240R_90_23 (by norm_num)

theorem c22240R_90_21 : rowsJ2 90 91 53 340 ≤ 55332434892377 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2322 c22240R_90_22 (by norm_num)

theorem c22240R_90_20 : rowsJ2 90 91 52 340 ≤ 55332434892377 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2321 c22240R_90_21 (by norm_num)

theorem c22240R_90_19 : rowsJ2 90 91 51 340 ≤ 55332434892377 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2320 c22240R_90_20 (by norm_num)

theorem c22240R_90_18 : rowsJ2 90 91 50 340 ≤ 58239426763518 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2319 c22240R_90_19 (by norm_num)

theorem c22240R_90_17 : rowsJ2 90 91 49 340 ≤ 64383204050723 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2318 c22240R_90_18 (by norm_num)

theorem c22240R_90_16 : rowsJ2 90 91 48 340 ≤ 74775860502559 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2317 c22240R_90_17 (by norm_num)

theorem c22240R_90_15 : rowsJ2 90 91 47 340 ≤ 89841268314927 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2316 c22240R_90_16 (by norm_num)

theorem c22240R_90_14 : rowsJ2 90 91 46 340 ≤ 106750727832784 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2315 c22240R_90_15 (by norm_num)

theorem c22240R_90_13 : rowsJ2 90 91 45 340 ≤ 122553368332160 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2314 c22240R_90_14 (by norm_num)

theorem c22240R_90_12 : rowsJ2 90 91 44 340 ≤ 137127214184006 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2313 c22240R_90_13 (by norm_num)

theorem c22240R_90_11 : rowsJ2 90 91 43 340 ≤ 150295473129359 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2312 c22240R_90_12 (by norm_num)

theorem c22240R_90_10 : rowsJ2 90 91 42 340 ≤ 162049461500449 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2311 c22240R_90_11 (by norm_num)

theorem c22240R_90_9 : rowsJ2 90 91 41 340 ≤ 172495935313997 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2310 c22240R_90_10 (by norm_num)

theorem c22240R_90_8 : rowsJ2 90 91 40 340 ≤ 181649846541217 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2309 c22240R_90_9 (by norm_num)

theorem c22240R_90_7 : rowsJ2 90 91 38 340 ≤ 196155216219475 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2308 c22240R_90_8 (by norm_num)

theorem c22240R_90_6 : rowsJ2 90 91 36 340 ≤ 205447401258899 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2307 c22240R_90_7 (by norm_num)

theorem c22240R_90_5 : rowsJ2 90 91 33 340 ≤ 210986029582045 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2306 c22240R_90_6 (by norm_num)

theorem c22240R_90_4 : rowsJ2 90 91 27 340 ≤ 211181257065298 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2305 c22240R_90_5 (by norm_num)

theorem c22240R_90_3 : rowsJ2 90 91 23 340 ≤ 211181257065298 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2304 c22240R_90_4 (by norm_num)

theorem c22240R_90_2 : rowsJ2 90 91 20 340 ≤ 211181257065298 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2303 c22240R_90_3 (by norm_num)

theorem c22240R_90_1 : rowsJ2 90 91 17 340 ≤ 211181257065298 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2302 c22240R_90_2 (by norm_num)

theorem c22240R_90_0 : rowsJ2 90 91 0 340 ≤ 211186484342164 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22240R_2301 c22240R_90_1 (by norm_num)

theorem hr22240R_90 : rows2 90 91 ≤ 211186484342164 := rows2_le_of_rowsJ2 90 91 c22240R_90_0

theorem c22240R_91_43 : rowsJ2 91 92 90 340 ≤ 11508611958669 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2389 rows22240R_2390 (by norm_num)

theorem c22240R_91_42 : rowsJ2 91 92 89 340 ≤ 18239722077656 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2388 c22240R_91_43 (by norm_num)

theorem c22240R_91_41 : rowsJ2 91 92 88 340 ≤ 25816256117993 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2387 c22240R_91_42 (by norm_num)

theorem c22240R_91_40 : rowsJ2 91 92 87 340 ≤ 33291772099397 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2386 c22240R_91_41 (by norm_num)

theorem c22240R_91_39 : rowsJ2 91 92 86 340 ≤ 39544612831954 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2385 c22240R_91_40 (by norm_num)

theorem c22240R_91_38 : rowsJ2 91 92 85 340 ≤ 44476501909468 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2384 c22240R_91_39 (by norm_num)

theorem c22240R_91_37 : rowsJ2 91 92 84 340 ≤ 48289571892473 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2383 c22240R_91_38 (by norm_num)

theorem c22240R_91_36 : rowsJ2 91 92 83 340 ≤ 51154565769012 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2382 c22240R_91_37 (by norm_num)

theorem c22240R_91_35 : rowsJ2 91 92 82 340 ≤ 53246460271556 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2381 c22240R_91_36 (by norm_num)

theorem c22240R_91_34 : rowsJ2 91 92 81 340 ≤ 54712840085248 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2380 c22240R_91_35 (by norm_num)

theorem c22240R_91_33 : rowsJ2 91 92 80 340 ≤ 55708541185821 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2379 c22240R_91_34 (by norm_num)

theorem c22240R_91_32 : rowsJ2 91 92 78 340 ≤ 56755231945821 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2378 c22240R_91_33 (by norm_num)

theorem c22240R_91_31 : rowsJ2 91 92 74 340 ≤ 57006793817384 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2377 c22240R_91_32 (by norm_num)

theorem c22240R_91_30 : rowsJ2 91 92 70 340 ≤ 57006793817384 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2376 c22240R_91_31 (by norm_num)

theorem c22240R_91_29 : rowsJ2 91 92 66 340 ≤ 57006793817384 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2375 c22240R_91_30 (by norm_num)

theorem c22240R_91_28 : rowsJ2 91 92 63 340 ≤ 57006793817384 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2374 c22240R_91_29 (by norm_num)

theorem c22240R_91_27 : rowsJ2 91 92 61 340 ≤ 57006793817384 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2373 c22240R_91_28 (by norm_num)

theorem c22240R_91_26 : rowsJ2 91 92 59 340 ≤ 57006793817384 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2372 c22240R_91_27 (by norm_num)

theorem c22240R_91_25 : rowsJ2 91 92 57 340 ≤ 57006793817384 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2371 c22240R_91_26 (by norm_num)

theorem c22240R_91_24 : rowsJ2 91 92 56 340 ≤ 57006793817384 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2370 c22240R_91_25 (by norm_num)

theorem c22240R_91_23 : rowsJ2 91 92 55 340 ≤ 57006793817384 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2369 c22240R_91_24 (by norm_num)

theorem c22240R_91_22 : rowsJ2 91 92 54 340 ≤ 57006793817384 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2368 c22240R_91_23 (by norm_num)

theorem c22240R_91_21 : rowsJ2 91 92 53 340 ≤ 57006793817384 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2367 c22240R_91_22 (by norm_num)

theorem c22240R_91_20 : rowsJ2 91 92 52 340 ≤ 57006793817384 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2366 c22240R_91_21 (by norm_num)

theorem c22240R_91_19 : rowsJ2 91 92 51 340 ≤ 59164647958822 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2365 c22240R_91_20 (by norm_num)

theorem c22240R_91_18 : rowsJ2 91 92 50 340 ≤ 64234055885717 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2364 c22240R_91_19 (by norm_num)

theorem c22240R_91_17 : rowsJ2 91 92 49 340 ≤ 72546278210385 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2363 c22240R_91_18 (by norm_num)

theorem c22240R_91_16 : rowsJ2 91 92 48 340 ≤ 85054543713366 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2362 c22240R_91_17 (by norm_num)

theorem c22240R_91_15 : rowsJ2 91 92 47 340 ≤ 99229892324956 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2361 c22240R_91_16 (by norm_num)

theorem c22240R_91_14 : rowsJ2 91 92 46 340 ≤ 115188400516737 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2360 c22240R_91_15 (by norm_num)

theorem c22240R_91_13 : rowsJ2 91 92 45 340 ≤ 131554447995401 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2359 c22240R_91_14 (by norm_num)

theorem c22240R_91_12 : rowsJ2 91 92 44 340 ≤ 146670177318699 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2358 c22240R_91_13 (by norm_num)

theorem c22240R_91_11 : rowsJ2 91 92 43 340 ≤ 160413313065450 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2357 c22240R_91_12 (by norm_num)

theorem c22240R_91_10 : rowsJ2 91 92 42 340 ≤ 172662286710083 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2356 c22240R_91_11 (by norm_num)

theorem c22240R_91_9 : rowsJ2 91 92 41 340 ≤ 183522755983927 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2355 c22240R_91_10 (by norm_num)

theorem c22240R_91_8 : rowsJ2 91 92 40 340 ≤ 193105707964956 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2354 c22240R_91_9 (by norm_num)

theorem c22240R_91_7 : rowsJ2 91 92 39 340 ≤ 201429124738480 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2353 c22240R_91_8 (by norm_num)

theorem c22240R_91_6 : rowsJ2 91 92 37 340 ≤ 214386053539802 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2352 c22240R_91_7 (by norm_num)

theorem c22240R_91_5 : rowsJ2 91 92 34 340 ≤ 223802533002320 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2351 c22240R_91_6 (by norm_num)

theorem c22240R_91_4 : rowsJ2 91 92 29 340 ≤ 225370806337520 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2350 c22240R_91_5 (by norm_num)

theorem c22240R_91_3 : rowsJ2 91 92 24 340 ≤ 225370806337520 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2349 c22240R_91_4 (by norm_num)

theorem c22240R_91_2 : rowsJ2 91 92 20 340 ≤ 225370806337520 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2348 c22240R_91_3 (by norm_num)

theorem c22240R_91_1 : rowsJ2 91 92 17 340 ≤ 225370806337520 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2347 c22240R_91_2 (by norm_num)

theorem c22240R_91_0 : rowsJ2 91 92 0 340 ≤ 225370806337520 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22240R_2346 c22240R_91_1 (by norm_num)

theorem hr22240R_91 : rows2 91 92 ≤ 225370806337520 := rows2_le_of_rowsJ2 91 92 c22240R_91_0

theorem c22240R_92_43 : rowsJ2 92 93 91 340 ≤ 9322340173859 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2434 rows22240R_2435 (by norm_num)

theorem c22240R_92_42 : rowsJ2 92 93 90 340 ≤ 14397596321878 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2433 c22240R_92_43 (by norm_num)

theorem c22240R_92_41 : rowsJ2 92 93 89 340 ≤ 20049774646147 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2432 c22240R_92_42 (by norm_num)

theorem c22240R_92_40 : rowsJ2 92 93 88 340 ≤ 26434121829888 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2431 c22240R_92_41 (by norm_num)

theorem c22240R_92_39 : rowsJ2 92 93 87 340 ≤ 33647431411462 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2430 c22240R_92_40 (by norm_num)

theorem c22240R_92_38 : rowsJ2 92 93 86 340 ≤ 39824979973472 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2429 c22240R_92_39 (by norm_num)

theorem c22240R_92_37 : rowsJ2 92 93 85 340 ≤ 44766057707109 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2428 c22240R_92_38 (by norm_num)

theorem c22240R_92_36 : rowsJ2 92 93 84 340 ≤ 48578300766790 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2427 c22240R_92_37 (by norm_num)

theorem c22240R_92_35 : rowsJ2 92 93 83 340 ≤ 51436346317394 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2426 c22240R_92_36 (by norm_num)

theorem c22240R_92_34 : rowsJ2 92 93 82 340 ≤ 53518253932787 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2425 c22240R_92_35 (by norm_num)

theorem c22240R_92_33 : rowsJ2 92 93 81 340 ≤ 54974172587100 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2424 c22240R_92_34 (by norm_num)

theorem c22240R_92_32 : rowsJ2 92 93 80 340 ≤ 55960800357553 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2423 c22240R_92_33 (by norm_num)

theorem c22240R_92_31 : rowsJ2 92 93 78 340 ≤ 56997958932457 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2422 c22240R_92_32 (by norm_num)

theorem c22240R_92_30 : rowsJ2 92 93 74 340 ≤ 57247231906900 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2421 c22240R_92_31 (by norm_num)

theorem c22240R_92_29 : rowsJ2 92 93 69 340 ≤ 57247231906900 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2420 c22240R_92_30 (by norm_num)

theorem c22240R_92_28 : rowsJ2 92 93 65 340 ≤ 57247231906900 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2419 c22240R_92_29 (by norm_num)

theorem c22240R_92_27 : rowsJ2 92 93 62 340 ≤ 57247231906900 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2418 c22240R_92_28 (by norm_num)

theorem c22240R_92_26 : rowsJ2 92 93 60 340 ≤ 57247231906900 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2417 c22240R_92_27 (by norm_num)

theorem c22240R_92_25 : rowsJ2 92 93 58 340 ≤ 57247231906900 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2416 c22240R_92_26 (by norm_num)

theorem c22240R_92_24 : rowsJ2 92 93 56 340 ≤ 57247231906900 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2415 c22240R_92_25 (by norm_num)

theorem c22240R_92_23 : rowsJ2 92 93 55 340 ≤ 57247231906900 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2414 c22240R_92_24 (by norm_num)

theorem c22240R_92_22 : rowsJ2 92 93 54 340 ≤ 57247231906900 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2413 c22240R_92_23 (by norm_num)

theorem c22240R_92_21 : rowsJ2 92 93 53 340 ≤ 57247231906900 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2412 c22240R_92_22 (by norm_num)

theorem c22240R_92_20 : rowsJ2 92 93 52 340 ≤ 59105570237254 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2411 c22240R_92_21 (by norm_num)

theorem c22240R_92_19 : rowsJ2 92 93 51 340 ≤ 63128591468964 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2410 c22240R_92_20 (by norm_num)

theorem c22240R_92_18 : rowsJ2 92 93 50 340 ≤ 70068350597404 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2409 c22240R_92_19 (by norm_num)

theorem c22240R_92_17 : rowsJ2 92 93 49 340 ≤ 80257567353149 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2408 c22240R_92_18 (by norm_num)

theorem c22240R_92_16 : rowsJ2 92 93 48 340 ≤ 91941896872927 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2407 c22240R_92_17 (by norm_num)

theorem c22240R_92_15 : rowsJ2 92 93 47 340 ≤ 105232188005489 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2406 c22240R_92_16 (by norm_num)

theorem c22240R_92_14 : rowsJ2 92 93 46 340 ≤ 120302225671107 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2405 c22240R_92_15 (by norm_num)

theorem c22240R_92_13 : rowsJ2 92 93 45 340 ≤ 137172758437409 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2404 c22240R_92_14 (by norm_num)

theorem c22240R_92_12 : rowsJ2 92 93 44 340 ≤ 152928666115976 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2403 c22240R_92_13 (by norm_num)

theorem c22240R_92_11 : rowsJ2 92 93 43 340 ≤ 167289052644452 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2402 c22240R_92_12 (by norm_num)

theorem c22240R_92_10 : rowsJ2 92 93 42 340 ≤ 180131110740606 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2401 c22240R_92_11 (by norm_num)

theorem c22240R_92_9 : rowsJ2 92 93 41 340 ≤ 191503214206646 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2400 c22240R_92_10 (by norm_num)

theorem c22240R_92_8 : rowsJ2 92 93 40 340 ≤ 201515187647714 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2399 c22240R_92_9 (by norm_num)

theorem c22240R_92_7 : rowsJ2 92 93 39 340 ≤ 210282527582049 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2398 c22240R_92_8 (by norm_num)

theorem c22240R_92_6 : rowsJ2 92 93 37 340 ≤ 224171922770111 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2397 c22240R_92_7 (by norm_num)

theorem c22240R_92_5 : rowsJ2 92 93 35 340 ≤ 232132846753210 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2396 c22240R_92_6 (by norm_num)

theorem c22240R_92_4 : rowsJ2 92 93 30 340 ≤ 236614281528493 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2395 c22240R_92_5 (by norm_num)

theorem c22240R_92_3 : rowsJ2 92 93 24 340 ≤ 236614281528493 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2394 c22240R_92_4 (by norm_num)

theorem c22240R_92_2 : rowsJ2 92 93 20 340 ≤ 236614281528493 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2393 c22240R_92_3 (by norm_num)

theorem c22240R_92_1 : rowsJ2 92 93 17 340 ≤ 236614281528493 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2392 c22240R_92_2 (by norm_num)

theorem c22240R_92_0 : rowsJ2 92 93 0 340 ≤ 236614281528493 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22240R_2391 c22240R_92_1 (by norm_num)

theorem hr22240R_92 : rows2 92 93 ≤ 236614281528493 := rows2_le_of_rowsJ2 92 93 c22240R_92_0

theorem c22240R_93_44 : rowsJ2 93 94 92 340 ≤ 8810604161480 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2480 rows22240R_2481 (by norm_num)

theorem c22240R_93_43 : rowsJ2 93 94 91 340 ≤ 13043630600261 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2479 c22240R_93_44 (by norm_num)

theorem c22240R_93_42 : rowsJ2 93 94 90 340 ≤ 17276640051942 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2478 c22240R_93_43 (by norm_num)

theorem c22240R_93_41 : rowsJ2 93 94 89 340 ≤ 21959070326941 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2477 c22240R_93_42 (by norm_num)

theorem c22240R_93_40 : rowsJ2 93 94 88 340 ≤ 27253729191920 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2476 c22240R_93_41 (by norm_num)

theorem c22240R_93_39 : rowsJ2 93 94 87 340 ≤ 33298995737126 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2475 c22240R_93_40 (by norm_num)

theorem c22240R_93_38 : rowsJ2 93 94 86 340 ≤ 39303391538951 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2474 c22240R_93_39 (by norm_num)

theorem c22240R_93_37 : rowsJ2 93 94 85 340 ≤ 44256576093045 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2473 c22240R_93_38 (by norm_num)

theorem c22240R_93_36 : rowsJ2 93 94 84 340 ≤ 48069868495981 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2472 c22240R_93_37 (by norm_num)

theorem c22240R_93_35 : rowsJ2 93 94 83 340 ≤ 50922100768859 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2471 c22240R_93_36 (by norm_num)

theorem c22240R_93_34 : rowsJ2 93 94 82 340 ≤ 52994622814153 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2470 c22240R_93_35 (by norm_num)

theorem c22240R_93_33 : rowsJ2 93 94 81 340 ≤ 54440332522795 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2469 c22240R_93_34 (by norm_num)

theorem c22240R_93_32 : rowsJ2 93 94 80 340 ≤ 55418025215018 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2468 c22240R_93_33 (by norm_num)

theorem c22240R_93_31 : rowsJ2 93 94 79 340 ≤ 56061404967498 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2467 c22240R_93_32 (by norm_num)

theorem c22240R_93_30 : rowsJ2 93 94 77 340 ≤ 56630779484921 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2466 c22240R_93_31 (by norm_num)

theorem c22240R_93_29 : rowsJ2 93 94 73 340 ≤ 56692737053843 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2465 c22240R_93_30 (by norm_num)

theorem c22240R_93_28 : rowsJ2 93 94 68 340 ≤ 56692737053843 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2464 c22240R_93_29 (by norm_num)

theorem c22240R_93_27 : rowsJ2 93 94 64 340 ≤ 56692737053843 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2463 c22240R_93_28 (by norm_num)

theorem c22240R_93_26 : rowsJ2 93 94 61 340 ≤ 56692737053843 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2462 c22240R_93_27 (by norm_num)

theorem c22240R_93_25 : rowsJ2 93 94 59 340 ≤ 56692737053843 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2461 c22240R_93_26 (by norm_num)

theorem c22240R_93_24 : rowsJ2 93 94 57 340 ≤ 56692737053843 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2460 c22240R_93_25 (by norm_num)

theorem c22240R_93_23 : rowsJ2 93 94 55 340 ≤ 56692737053843 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2459 c22240R_93_24 (by norm_num)

theorem c22240R_93_22 : rowsJ2 93 94 54 340 ≤ 56692737053843 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2458 c22240R_93_23 (by norm_num)

theorem c22240R_93_21 : rowsJ2 93 94 53 340 ≤ 57879558926356 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2457 c22240R_93_22 (by norm_num)

theorem c22240R_93_20 : rowsJ2 93 94 52 340 ≤ 60865800708211 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2456 c22240R_93_21 (by norm_num)

theorem c22240R_93_19 : rowsJ2 93 94 51 340 ≤ 66019654863716 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2455 c22240R_93_20 (by norm_num)

theorem c22240R_93_18 : rowsJ2 93 94 50 340 ≤ 74032063627481 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2454 c22240R_93_19 (by norm_num)

theorem c22240R_93_17 : rowsJ2 93 94 49 340 ≤ 83371152964437 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2453 c22240R_93_18 (by norm_num)

theorem c22240R_93_16 : rowsJ2 93 94 48 340 ≤ 94142903089259 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2452 c22240R_93_17 (by norm_num)

theorem c22240R_93_15 : rowsJ2 93 94 47 340 ≤ 106516875548596 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2451 c22240R_93_16 (by norm_num)

theorem c22240R_93_14 : rowsJ2 93 94 46 340 ≤ 120608656152425 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2450 c22240R_93_15 (by norm_num)

theorem c22240R_93_13 : rowsJ2 93 94 45 340 ≤ 136496505194965 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2449 c22240R_93_14 (by norm_num)

theorem c22240R_93_12 : rowsJ2 93 94 44 340 ≤ 152737060048206 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2448 c22240R_93_13 (by norm_num)

theorem c22240R_93_11 : rowsJ2 93 94 43 340 ≤ 167716958065909 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2447 c22240R_93_12 (by norm_num)

theorem c22240R_93_10 : rowsJ2 93 94 42 340 ≤ 181153114761204 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2446 c22240R_93_11 (by norm_num)

theorem c22240R_93_9 : rowsJ2 93 94 41 340 ≤ 193036206749795 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2445 c22240R_93_10 (by norm_num)

theorem c22240R_93_8 : rowsJ2 93 94 40 340 ≤ 203474942112885 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2444 c22240R_93_9 (by norm_num)

theorem c22240R_93_7 : rowsJ2 93 94 39 340 ≤ 212583560016005 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2443 c22240R_93_8 (by norm_num)

theorem c22240R_93_6 : rowsJ2 93 94 38 340 ≤ 220482338319562 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2442 c22240R_93_7 (by norm_num)

theorem c22240R_93_5 : rowsJ2 93 94 36 340 ≤ 232334634570754 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2441 c22240R_93_6 (by norm_num)

theorem c22240R_93_4 : rowsJ2 93 94 32 340 ≤ 241002764713682 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2440 c22240R_93_5 (by norm_num)

theorem c22240R_93_3 : rowsJ2 93 94 25 340 ≤ 241203865637276 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2439 c22240R_93_4 (by norm_num)

theorem c22240R_93_2 : rowsJ2 93 94 20 340 ≤ 241203865637276 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2438 c22240R_93_3 (by norm_num)

theorem c22240R_93_1 : rowsJ2 93 94 16 340 ≤ 241203865637276 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2437 c22240R_93_2 (by norm_num)

theorem c22240R_93_0 : rowsJ2 93 94 0 340 ≤ 241203865637276 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22240R_2436 c22240R_93_1 (by norm_num)

theorem hr22240R_93 : rows2 93 94 ≤ 241203865637276 := rows2_le_of_rowsJ2 93 94 c22240R_93_0

theorem c22240R_94_44 : rowsJ2 94 95 93 340 ≤ 8856573099026 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2526 rows22240R_2527 (by norm_num)

theorem c22240R_94_43 : rowsJ2 94 95 92 340 ≤ 12901732112650 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2525 c22240R_94_44 (by norm_num)

theorem c22240R_94_42 : rowsJ2 94 95 91 340 ≤ 16800411639867 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2524 c22240R_94_43 (by norm_num)

theorem c22240R_94_41 : rowsJ2 94 95 90 340 ≤ 20644582306892 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2523 c22240R_94_42 (by norm_num)

theorem c22240R_94_40 : rowsJ2 94 95 89 340 ≤ 24507136916427 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2522 c22240R_94_41 (by norm_num)

theorem c22240R_94_39 : rowsJ2 94 95 88 340 ≤ 28854888343698 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2521 c22240R_94_40 (by norm_num)

theorem c22240R_94_38 : rowsJ2 94 95 87 340 ≤ 33833911897239 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2520 c22240R_94_39 (by norm_num)

theorem c22240R_94_37 : rowsJ2 94 95 86 340 ≤ 39564292074147 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2519 c22240R_94_38 (by norm_num)

theorem c22240R_94_36 : rowsJ2 94 95 85 340 ≤ 44433457816973 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2518 c22240R_94_37 (by norm_num)

theorem c22240R_94_35 : rowsJ2 94 95 84 340 ≤ 48249783428433 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2517 c22240R_94_36 (by norm_num)

theorem c22240R_94_34 : rowsJ2 94 95 83 340 ≤ 51097426472895 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2516 c22240R_94_35 (by norm_num)

theorem c22240R_94_33 : rowsJ2 94 95 82 340 ≤ 53161186107306 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2515 c22240R_94_34 (by norm_num)

theorem c22240R_94_32 : rowsJ2 94 95 81 340 ≤ 54596970470739 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2514 c22240R_94_33 (by norm_num)

theorem c22240R_94_31 : rowsJ2 94 95 80 340 ≤ 55565837093355 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2513 c22240R_94_32 (by norm_num)

theorem c22240R_94_30 : rowsJ2 94 95 79 340 ≤ 56203348008735 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2512 c22240R_94_31 (by norm_num)

theorem c22240R_94_29 : rowsJ2 94 95 77 340 ≤ 56767533691288 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2511 c22240R_94_30 (by norm_num)

theorem c22240R_94_28 : rowsJ2 94 95 73 340 ≤ 56828926963643 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2510 c22240R_94_29 (by norm_num)

theorem c22240R_94_27 : rowsJ2 94 95 68 340 ≤ 56828926963643 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2509 c22240R_94_28 (by norm_num)

theorem c22240R_94_26 : rowsJ2 94 95 63 340 ≤ 56828926963643 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2508 c22240R_94_27 (by norm_num)

theorem c22240R_94_25 : rowsJ2 94 95 60 340 ≤ 56828926963643 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2507 c22240R_94_26 (by norm_num)

theorem c22240R_94_24 : rowsJ2 94 95 58 340 ≤ 56828926963643 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2506 c22240R_94_25 (by norm_num)

theorem c22240R_94_23 : rowsJ2 94 95 56 340 ≤ 56828926963643 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2505 c22240R_94_24 (by norm_num)

theorem c22240R_94_22 : rowsJ2 94 95 54 340 ≤ 57792274982129 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2504 c22240R_94_23 (by norm_num)

theorem c22240R_94_21 : rowsJ2 94 95 53 340 ≤ 59946339572423 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2503 c22240R_94_22 (by norm_num)

theorem c22240R_94_20 : rowsJ2 94 95 52 340 ≤ 63902245763120 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2502 c22240R_94_21 (by norm_num)

theorem c22240R_94_19 : rowsJ2 94 95 51 340 ≤ 69968745646092 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2501 c22240R_94_20 (by norm_num)

theorem c22240R_94_18 : rowsJ2 94 95 50 340 ≤ 77197529668355 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2500 c22240R_94_19 (by norm_num)

theorem c22240R_94_17 : rowsJ2 94 95 49 340 ≤ 85690071461042 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2499 c22240R_94_18 (by norm_num)

theorem c22240R_94_16 : rowsJ2 94 95 48 340 ≤ 95612139625310 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2498 c22240R_94_17 (by norm_num)

theorem c22240R_94_15 : rowsJ2 94 95 47 340 ≤ 107074172257513 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2497 c22240R_94_16 (by norm_num)

theorem c22240R_94_14 : rowsJ2 94 95 46 340 ≤ 120250673429405 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2496 c22240R_94_15 (by norm_num)

theorem c22240R_94_13 : rowsJ2 94 95 45 340 ≤ 135161098427418 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2495 c22240R_94_14 (by norm_num)

theorem c22240R_94_12 : rowsJ2 94 95 44 340 ≤ 151884633530902 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2494 c22240R_94_13 (by norm_num)

theorem c22240R_94_11 : rowsJ2 94 95 43 340 ≤ 167425902561635 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2493 c22240R_94_12 (by norm_num)

theorem c22240R_94_10 : rowsJ2 94 95 42 340 ≤ 181558614365881 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2492 c22240R_94_11 (by norm_num)

theorem c22240R_94_9 : rowsJ2 94 95 41 340 ≤ 194054552563503 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2491 c22240R_94_10 (by norm_num)

theorem c22240R_94_8 : rowsJ2 94 95 40 340 ≤ 205021383541847 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2490 c22240R_94_9 (by norm_num)

theorem c22240R_94_7 : rowsJ2 94 95 39 340 ≤ 214572162457412 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2489 c22240R_94_8 (by norm_num)

theorem c22240R_94_6 : rowsJ2 94 95 38 340 ≤ 222825837130670 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2488 c22240R_94_7 (by norm_num)

theorem c22240R_94_5 : rowsJ2 94 95 36 340 ≤ 235425587983181 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2487 c22240R_94_6 (by norm_num)

theorem c22240R_94_4 : rowsJ2 94 95 32 340 ≤ 245072065192626 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2486 c22240R_94_5 (by norm_num)

theorem c22240R_94_3 : rowsJ2 94 95 25 340 ≤ 245478006732931 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2485 c22240R_94_4 (by norm_num)

theorem c22240R_94_2 : rowsJ2 94 95 20 340 ≤ 245478006732931 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2484 c22240R_94_3 (by norm_num)

theorem c22240R_94_1 : rowsJ2 94 95 16 340 ≤ 245478006732931 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2483 c22240R_94_2 (by norm_num)

theorem c22240R_94_0 : rowsJ2 94 95 0 340 ≤ 245478006732931 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22240R_2482 c22240R_94_1 (by norm_num)

theorem hr22240R_94 : rows2 94 95 ≤ 245478006732931 := rows2_le_of_rowsJ2 94 95 c22240R_94_0

theorem c22240R_95_44 : rowsJ2 95 96 94 340 ≤ 9379378333401 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2572 rows22240R_2573 (by norm_num)

theorem c22240R_95_43 : rowsJ2 95 96 93 340 ≤ 13474887569562 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2571 c22240R_95_44 (by norm_num)

theorem c22240R_95_42 : rowsJ2 95 96 92 340 ≤ 17286399144753 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2570 c22240R_95_43 (by norm_num)

theorem c22240R_95_41 : rowsJ2 95 96 91 340 ≤ 20893115800408 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2569 c22240R_95_42 (by norm_num)

theorem c22240R_95_40 : rowsJ2 95 96 90 340 ≤ 24389122847378 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2568 c22240R_95_41 (by norm_num)

theorem c22240R_95_39 : rowsJ2 95 96 89 340 ≤ 27849417328327 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2567 c22240R_95_40 (by norm_num)

theorem c22240R_95_38 : rowsJ2 95 96 88 340 ≤ 31364013356669 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2566 c22240R_95_39 (by norm_num)

theorem c22240R_95_37 : rowsJ2 95 96 87 340 ≤ 35383197961316 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2565 c22240R_95_38 (by norm_num)

theorem c22240R_95_36 : rowsJ2 95 96 86 340 ≤ 40070061379110 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2564 c22240R_95_37 (by norm_num)

theorem c22240R_95_35 : rowsJ2 95 96 85 340 ≤ 44756237638490 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2563 c22240R_95_36 (by norm_num)

theorem c22240R_95_34 : rowsJ2 95 96 84 340 ≤ 48577701515839 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2562 c22240R_95_35 (by norm_num)

theorem c22240R_95_33 : rowsJ2 95 96 83 340 ≤ 51421978241972 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2561 c22240R_95_34 (by norm_num)

theorem c22240R_95_32 : rowsJ2 95 96 82 340 ≤ 53477684895780 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2560 c22240R_95_33 (by norm_num)

theorem c22240R_95_31 : rowsJ2 95 96 81 340 ≤ 54903867431124 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2559 c22240R_95_32 (by norm_num)

theorem c22240R_95_30 : rowsJ2 95 96 80 340 ≤ 55863979436140 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2558 c22240R_95_31 (by norm_num)

theorem c22240R_95_29 : rowsJ2 95 96 79 340 ≤ 56495668224106 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2557 c22240R_95_30 (by norm_num)

theorem c22240R_95_28 : rowsJ2 95 96 76 340 ≤ 57115540216686 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2556 c22240R_95_29 (by norm_num)

theorem c22240R_95_27 : rowsJ2 95 96 72 340 ≤ 57115540216686 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2555 c22240R_95_28 (by norm_num)

theorem c22240R_95_26 : rowsJ2 95 96 67 340 ≤ 57115540216686 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2554 c22240R_95_27 (by norm_num)

theorem c22240R_95_25 : rowsJ2 95 96 62 340 ≤ 57115540216686 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2553 c22240R_95_26 (by norm_num)

theorem c22240R_95_24 : rowsJ2 95 96 59 340 ≤ 57115540216686 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2552 c22240R_95_25 (by norm_num)

theorem c22240R_95_23 : rowsJ2 95 96 57 340 ≤ 57115540216686 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2551 c22240R_95_24 (by norm_num)

theorem c22240R_95_22 : rowsJ2 95 96 55 340 ≤ 57609216156866 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2550 c22240R_95_23 (by norm_num)

theorem c22240R_95_21 : rowsJ2 95 96 53 340 ≤ 61652033546090 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2549 c22240R_95_22 (by norm_num)

theorem c22240R_95_20 : rowsJ2 95 96 52 340 ≤ 65974829917126 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2548 c22240R_95_21 (by norm_num)

theorem c22240R_95_19 : rowsJ2 95 96 51 340 ≤ 71324126203286 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2547 c22240R_95_20 (by norm_num)

theorem c22240R_95_18 : rowsJ2 95 96 50 340 ≤ 77772176877642 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2546 c22240R_95_19 (by norm_num)

theorem c22240R_95_17 : rowsJ2 95 96 49 340 ≤ 85481372471420 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2545 c22240R_95_18 (by norm_num)

theorem c22240R_95_16 : rowsJ2 95 96 48 340 ≤ 94557383506819 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2544 c22240R_95_17 (by norm_num)

theorem c22240R_95_15 : rowsJ2 95 96 47 340 ≤ 105170642233546 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2543 c22240R_95_16 (by norm_num)

theorem c22240R_95_14 : rowsJ2 95 96 46 340 ≤ 117436323627751 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2542 c22240R_95_15 (by norm_num)

theorem c22240R_95_13 : rowsJ2 95 96 45 340 ≤ 131432598991230 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2541 c22240R_95_14 (by norm_num)

theorem c22240R_95_12 : rowsJ2 95 96 44 340 ≤ 147179622325699 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2540 c22240R_95_13 (by norm_num)

theorem c22240R_95_11 : rowsJ2 95 96 43 340 ≤ 163281177499537 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2539 c22240R_95_12 (by norm_num)

theorem c22240R_95_10 : rowsJ2 95 96 42 340 ≤ 178052609977628 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2538 c22240R_95_11 (by norm_num)

theorem c22240R_95_9 : rowsJ2 95 96 41 340 ≤ 191265500694764 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2537 c22240R_95_10 (by norm_num)

theorem c22240R_95_8 : rowsJ2 95 96 40 340 ≤ 202863937295979 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2536 c22240R_95_9 (by norm_num)

theorem c22240R_95_7 : rowsJ2 95 96 39 340 ≤ 212959867038553 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2535 c22240R_95_8 (by norm_num)

theorem c22240R_95_6 : rowsJ2 95 96 38 340 ≤ 221670982352400 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2534 c22240R_95_7 (by norm_num)

theorem c22240R_95_5 : rowsJ2 95 96 36 340 ≤ 235018135628567 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2533 c22240R_95_6 (by norm_num)

theorem c22240R_95_4 : rowsJ2 95 96 33 340 ≤ 244336585690110 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2532 c22240R_95_5 (by norm_num)

theorem c22240R_95_3 : rowsJ2 95 96 26 340 ≤ 246358840617875 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2531 c22240R_95_4 (by norm_num)

theorem c22240R_95_2 : rowsJ2 95 96 20 340 ≤ 246358840617875 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2530 c22240R_95_3 (by norm_num)

theorem c22240R_95_1 : rowsJ2 95 96 16 340 ≤ 246358840617875 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2529 c22240R_95_2 (by norm_num)

theorem c22240R_95_0 : rowsJ2 95 96 0 340 ≤ 246358840617875 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22240R_2528 c22240R_95_1 (by norm_num)

theorem hr22240R_95 : rows2 95 96 ≤ 246358840617875 := rows2_le_of_rowsJ2 95 96 c22240R_95_0

theorem c22240R_96_43 : rowsJ2 96 97 95 340 ≤ 10339869045919 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2617 rows22240R_2618 (by norm_num)

theorem c22240R_96_42 : rowsJ2 96 97 94 340 ≤ 14747406485318 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2616 c22240R_96_43 (by norm_num)

theorem c22240R_96_41 : rowsJ2 96 97 93 340 ≤ 18751365735279 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2615 c22240R_96_42 (by norm_num)

theorem c22240R_96_40 : rowsJ2 96 97 92 340 ≤ 22408701988772 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2614 c22240R_96_41 (by norm_num)

theorem c22240R_96_39 : rowsJ2 96 97 91 340 ≤ 25801179876561 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2613 c22240R_96_40 (by norm_num)

theorem c22240R_96_38 : rowsJ2 96 97 90 340 ≤ 29025161633347 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2612 c22240R_96_39 (by norm_num)

theorem c22240R_96_37 : rowsJ2 96 97 89 340 ≤ 32157893075089 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2611 c22240R_96_38 (by norm_num)

theorem c22240R_96_36 : rowsJ2 96 97 88 340 ≤ 35291343364305 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2610 c22240R_96_37 (by norm_num)

theorem c22240R_96_35 : rowsJ2 96 97 87 340 ≤ 38498995611764 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2609 c22240R_96_36 (by norm_num)

theorem c22240R_96_34 : rowsJ2 96 97 86 340 ≤ 42248109503411 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2608 c22240R_96_35 (by norm_num)

theorem c22240R_96_33 : rowsJ2 96 97 85 340 ≤ 46649212481798 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2607 c22240R_96_34 (by norm_num)

theorem c22240R_96_32 : rowsJ2 96 97 84 340 ≤ 50378744812013 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2606 c22240R_96_33 (by norm_num)

theorem c22240R_96_31 : rowsJ2 96 97 83 340 ≤ 53220974076800 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2605 c22240R_96_32 (by norm_num)

theorem c22240R_96_30 : rowsJ2 96 97 82 340 ≤ 55269339182671 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2604 c22240R_96_31 (by norm_num)

theorem c22240R_96_29 : rowsJ2 96 97 81 340 ≤ 56686249030568 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2603 c22240R_96_30 (by norm_num)

theorem c22240R_96_28 : rowsJ2 96 97 80 340 ≤ 57637737559105 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2602 c22240R_96_29 (by norm_num)

theorem c22240R_96_27 : rowsJ2 96 97 79 340 ≤ 58263650489938 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2601 c22240R_96_28 (by norm_num)

theorem c22240R_96_26 : rowsJ2 96 97 76 340 ≤ 58877860790315 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2600 c22240R_96_27 (by norm_num)

theorem c22240R_96_25 : rowsJ2 96 97 71 340 ≤ 58877860790315 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2599 c22240R_96_26 (by norm_num)

theorem c22240R_96_24 : rowsJ2 96 97 66 340 ≤ 58877860790315 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2598 c22240R_96_25 (by norm_num)

theorem c22240R_96_23 : rowsJ2 96 97 61 340 ≤ 58877860790315 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2597 c22240R_96_24 (by norm_num)

theorem c22240R_96_22 : rowsJ2 96 97 58 340 ≤ 58877860790315 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2596 c22240R_96_23 (by norm_num)

theorem c22240R_96_21 : rowsJ2 96 97 56 340 ≤ 59205897290836 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2595 c22240R_96_22 (by norm_num)

theorem c22240R_96_20 : rowsJ2 96 97 54 340 ≤ 61749699156935 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2594 c22240R_96_21 (by norm_num)

theorem c22240R_96_19 : rowsJ2 96 97 52 340 ≤ 68335380269852 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2593 c22240R_96_20 (by norm_num)

theorem c22240R_96_18 : rowsJ2 96 97 51 340 ≤ 73032275875815 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2592 c22240R_96_19 (by norm_num)

theorem c22240R_96_17 : rowsJ2 96 97 50 340 ≤ 78763207238117 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2591 c22240R_96_18 (by norm_num)

theorem c22240R_96_16 : rowsJ2 96 97 49 340 ≤ 85691983134301 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2590 c22240R_96_17 (by norm_num)

theorem c22240R_96_15 : rowsJ2 96 97 48 340 ≤ 93985397029212 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2589 c22240R_96_16 (by norm_num)

theorem c22240R_96_14 : rowsJ2 96 97 47 340 ≤ 103753577806418 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2588 c22240R_96_15 (by norm_num)

theorem c22240R_96_13 : rowsJ2 96 97 46 340 ≤ 115171911550913 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2587 c22240R_96_14 (by norm_num)

theorem c22240R_96_12 : rowsJ2 96 97 45 340 ≤ 128258586270151 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2586 c22240R_96_13 (by norm_num)

theorem c22240R_96_11 : rowsJ2 96 97 44 340 ≤ 143092688538129 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2585 c22240R_96_12 (by norm_num)

theorem c22240R_96_10 : rowsJ2 96 97 43 340 ≤ 159695100645781 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2584 c22240R_96_11 (by norm_num)

theorem c22240R_96_9 : rowsJ2 96 97 42 340 ≤ 175104747583819 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2583 c22240R_96_10 (by norm_num)

theorem c22240R_96_8 : rowsJ2 96 97 41 340 ≤ 189034411586916 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2582 c22240R_96_9 (by norm_num)

theorem c22240R_96_7 : rowsJ2 96 97 40 340 ≤ 201370282111456 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2581 c22240R_96_8 (by norm_num)

theorem c22240R_96_6 : rowsJ2 96 97 39 340 ≤ 212116597785366 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2580 c22240R_96_7 (by norm_num)

theorem c22240R_96_5 : rowsJ2 96 97 37 340 ≤ 229312750726030 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2579 c22240R_96_6 (by norm_num)

theorem c22240R_96_4 : rowsJ2 96 97 34 340 ≤ 243626981553907 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2578 c22240R_96_5 (by norm_num)

theorem c22240R_96_3 : rowsJ2 96 97 29 340 ≤ 248215130750583 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2577 c22240R_96_4 (by norm_num)

theorem c22240R_96_2 : rowsJ2 96 97 21 340 ≤ 248215130750583 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2576 c22240R_96_3 (by norm_num)

theorem c22240R_96_1 : rowsJ2 96 97 16 340 ≤ 248215130750583 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2575 c22240R_96_2 (by norm_num)

theorem c22240R_96_0 : rowsJ2 96 97 0 340 ≤ 248215130750583 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22240R_2574 c22240R_96_1 (by norm_num)

theorem hr22240R_96 : rows2 96 97 ≤ 248215130750583 := rows2_le_of_rowsJ2 96 97 c22240R_96_0

theorem c22240R_97_44 : rowsJ2 97 98 96 340 ≤ 11688370253888 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2663 rows22240R_2664 (by norm_num)

theorem c22240R_97_43 : rowsJ2 97 98 95 340 ≤ 16584268047482 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2662 c22240R_97_44 (by norm_num)

theorem c22240R_97_42 : rowsJ2 97 98 94 340 ≤ 20968938084749 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2661 c22240R_97_43 (by norm_num)

theorem c22240R_97_41 : rowsJ2 97 98 93 340 ≤ 24884624237926 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2660 c22240R_97_42 (by norm_num)

theorem c22240R_97_40 : rowsJ2 97 98 92 340 ≤ 28433349435229 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2659 c22240R_97_41 (by norm_num)

theorem c22240R_97_39 : rowsJ2 97 98 91 340 ≤ 31655033424485 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2658 c22240R_97_40 (by norm_num)

theorem c22240R_97_38 : rowsJ2 97 98 90 340 ≤ 34648446266805 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2657 c22240R_97_39 (by norm_num)

theorem c22240R_97_37 : rowsJ2 97 98 89 340 ≤ 37493239233226 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2656 c22240R_97_38 (by norm_num)

theorem c22240R_97_36 : rowsJ2 97 98 88 340 ≤ 40283477997992 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2655 c22240R_97_37 (by norm_num)

theorem c22240R_97_35 : rowsJ2 97 98 87 340 ≤ 43094729756199 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2654 c22240R_97_36 (by norm_num)

theorem c22240R_97_34 : rowsJ2 97 98 86 340 ≤ 46017119582735 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2653 c22240R_97_35 (by norm_num)

theorem c22240R_97_33 : rowsJ2 97 98 85 340 ≤ 49502027357083 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2652 c22240R_97_34 (by norm_num)

theorem c22240R_97_32 : rowsJ2 97 98 84 340 ≤ 53039613399176 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2651 c22240R_97_33 (by norm_num)

theorem c22240R_97_31 : rowsJ2 97 98 83 340 ≤ 55881225786210 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2650 c22240R_97_32 (by norm_num)

theorem c22240R_97_30 : rowsJ2 97 98 82 340 ≤ 57922956472946 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2649 c22240R_97_31 (by norm_num)

theorem c22240R_97_29 : rowsJ2 97 98 81 340 ≤ 59330929576376 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2648 c22240R_97_30 (by norm_num)

theorem c22240R_97_28 : rowsJ2 97 98 80 340 ≤ 60273956956745 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2647 c22240R_97_29 (by norm_num)

theorem c22240R_97_27 : rowsJ2 97 98 79 340 ≤ 60894137456798 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2646 c22240R_97_28 (by norm_num)

theorem c22240R_97_26 : rowsJ2 97 98 76 340 ≤ 61502728741653 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2645 c22240R_97_27 (by norm_num)

theorem c22240R_97_25 : rowsJ2 97 98 71 340 ≤ 61502728741653 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2644 c22240R_97_26 (by norm_num)

theorem c22240R_97_24 : rowsJ2 97 98 65 340 ≤ 61502728741653 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2643 c22240R_97_25 (by norm_num)

theorem c22240R_97_23 : rowsJ2 97 98 60 340 ≤ 61502728741653 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2642 c22240R_97_24 (by norm_num)

theorem c22240R_97_22 : rowsJ2 97 98 57 340 ≤ 61586301673723 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2641 c22240R_97_23 (by norm_num)

theorem c22240R_97_21 : rowsJ2 97 98 55 340 ≤ 62753479611249 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2640 c22240R_97_22 (by norm_num)

theorem c22240R_97_20 : rowsJ2 97 98 53 340 ≤ 66809572088920 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2639 c22240R_97_21 (by norm_num)

theorem c22240R_97_19 : rowsJ2 97 98 51 340 ≤ 74137681515639 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2638 c22240R_97_20 (by norm_num)

theorem c22240R_97_18 : rowsJ2 97 98 50 340 ≤ 79216528323625 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2637 c22240R_97_19 (by norm_num)

theorem c22240R_97_17 : rowsJ2 97 98 49 340 ≤ 85428746884274 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2636 c22240R_97_18 (by norm_num)

theorem c22240R_97_16 : rowsJ2 97 98 48 340 ≤ 92942551015145 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2635 c22240R_97_17 (by norm_num)

theorem c22240R_97_15 : rowsJ2 97 98 47 340 ≤ 101929409751758 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2634 c22240R_97_16 (by norm_num)

theorem c22240R_97_14 : rowsJ2 97 98 46 340 ≤ 112504190839952 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2633 c22240R_97_15 (by norm_num)

theorem c22240R_97_13 : rowsJ2 97 98 45 340 ≤ 124745062725159 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2632 c22240R_97_14 (by norm_num)

theorem c22240R_97_12 : rowsJ2 97 98 44 340 ≤ 138670891262229 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2631 c22240R_97_13 (by norm_num)

theorem c22240R_97_11 : rowsJ2 97 98 43 340 ≤ 154361718482853 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2630 c22240R_97_12 (by norm_num)

theorem c22240R_97_10 : rowsJ2 97 98 42 340 ≤ 170350525350386 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2629 c22240R_97_11 (by norm_num)

theorem c22240R_97_9 : rowsJ2 97 98 41 340 ≤ 184997033001112 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2628 c22240R_97_10 (by norm_num)

theorem c22240R_97_8 : rowsJ2 97 98 40 340 ≤ 198070236141916 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2627 c22240R_97_9 (by norm_num)

theorem c22240R_97_7 : rowsJ2 97 98 39 340 ≤ 209574563270073 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2626 c22240R_97_8 (by norm_num)

theorem c22240R_97_6 : rowsJ2 97 98 38 340 ≤ 219517034647408 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2625 c22240R_97_7 (by norm_num)

theorem c22240R_97_5 : rowsJ2 97 98 36 340 ≤ 234674205703697 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2624 c22240R_97_6 (by norm_num)

theorem c22240R_97_4 : rowsJ2 97 98 34 340 ≤ 243501563098534 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2623 c22240R_97_5 (by norm_num)

theorem c22240R_97_3 : rowsJ2 97 98 29 340 ≤ 248692957701551 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2622 c22240R_97_4 (by norm_num)

theorem c22240R_97_2 : rowsJ2 97 98 21 340 ≤ 248692957701551 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2621 c22240R_97_3 (by norm_num)

theorem c22240R_97_1 : rowsJ2 97 98 16 340 ≤ 248692957701551 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2620 c22240R_97_2 (by norm_num)

theorem c22240R_97_0 : rowsJ2 97 98 0 340 ≤ 248692957701551 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22240R_2619 c22240R_97_1 (by norm_num)

theorem hr22240R_97 : rows2 97 98 ≤ 248692957701551 := rows2_le_of_rowsJ2 97 98 c22240R_97_0

theorem c22240R_98_44 : rowsJ2 98 99 97 340 ≤ 13516456882742 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2709 rows22240R_2710 (by norm_num)

theorem c22240R_98_43 : rowsJ2 98 99 96 340 ≤ 19138555745503 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2708 c22240R_98_44 (by norm_num)

theorem c22240R_98_42 : rowsJ2 98 99 95 340 ≤ 24118410604815 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2707 c22240R_98_43 (by norm_num)

theorem c22240R_98_41 : rowsJ2 98 99 94 340 ≤ 28518535998078 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2706 c22240R_98_42 (by norm_num)

theorem c22240R_98_40 : rowsJ2 98 99 93 340 ≤ 32427588279729 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2705 c22240R_98_41 (by norm_num)

theorem c22240R_98_39 : rowsJ2 98 99 92 340 ≤ 35904854988075 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2704 c22240R_98_40 (by norm_num)

theorem c22240R_98_38 : rowsJ2 98 99 91 340 ≤ 39035463813906 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2703 c22240R_98_39 (by norm_num)

theorem c22240R_98_37 : rowsJ2 98 99 90 340 ≤ 41876179085559 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2702 c22240R_98_38 (by norm_num)

theorem c22240R_98_36 : rowsJ2 98 99 89 340 ≤ 44509190397809 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2701 c22240R_98_37 (by norm_num)

theorem c22240R_98_35 : rowsJ2 98 99 88 340 ≤ 47030821163023 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2700 c22240R_98_36 (by norm_num)

theorem c22240R_98_34 : rowsJ2 98 99 87 340 ≤ 49518866646148 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2699 c22240R_98_35 (by norm_num)

theorem c22240R_98_33 : rowsJ2 98 99 86 340 ≤ 52065389972167 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2698 c22240R_98_34 (by norm_num)

theorem c22240R_98_32 : rowsJ2 98 99 85 340 ≤ 54744548360621 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2697 c22240R_98_33 (by norm_num)

theorem c22240R_98_31 : rowsJ2 98 99 84 340 ≤ 57986892651882 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2696 c22240R_98_32 (by norm_num)

theorem c22240R_98_30 : rowsJ2 98 99 83 340 ≤ 60729951648615 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2695 c22240R_98_31 (by norm_num)

theorem c22240R_98_29 : rowsJ2 98 99 82 340 ≤ 62765853109547 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2694 c22240R_98_30 (by norm_num)

theorem c22240R_98_28 : rowsJ2 98 99 81 340 ≤ 64165235647963 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2693 c22240R_98_29 (by norm_num)

theorem c22240R_98_27 : rowsJ2 98 99 80 340 ≤ 65099900674622 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2692 c22240R_98_28 (by norm_num)

theorem c22240R_98_26 : rowsJ2 98 99 78 340 ≤ 66081538762006 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2691 c22240R_98_27 (by norm_num)

theorem c22240R_98_25 : rowsJ2 98 99 75 340 ≤ 66317466769296 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2690 c22240R_98_26 (by norm_num)

theorem c22240R_98_24 : rowsJ2 98 99 70 340 ≤ 66317466769296 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2689 c22240R_98_25 (by norm_num)

theorem c22240R_98_23 : rowsJ2 98 99 64 340 ≤ 66317466769296 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2688 c22240R_98_24 (by norm_num)

theorem c22240R_98_22 : rowsJ2 98 99 59 340 ≤ 66317466769296 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2687 c22240R_98_23 (by norm_num)

theorem c22240R_98_21 : rowsJ2 98 99 56 340 ≤ 66738034769113 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2686 c22240R_98_22 (by norm_num)

theorem c22240R_98_20 : rowsJ2 98 99 54 340 ≤ 68845058194444 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2685 c22240R_98_21 (by norm_num)

theorem c22240R_98_19 : rowsJ2 98 99 52 340 ≤ 73632591025304 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2684 c22240R_98_20 (by norm_num)

theorem c22240R_98_18 : rowsJ2 98 99 50 340 ≤ 81718617593076 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2683 c22240R_98_19 (by norm_num)

theorem c22240R_98_17 : rowsJ2 98 99 49 340 ≤ 87279581295054 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2682 c22240R_98_18 (by norm_num)

theorem c22240R_98_16 : rowsJ2 98 99 48 340 ≤ 94077923226363 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2681 c22240R_98_17 (by norm_num)

theorem c22240R_98_15 : rowsJ2 98 99 47 340 ≤ 102286535700504 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2680 c22240R_98_16 (by norm_num)

theorem c22240R_98_14 : rowsJ2 98 99 46 340 ≤ 112081855280393 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2679 c22240R_98_15 (by norm_num)

theorem c22240R_98_13 : rowsJ2 98 99 45 340 ≤ 123480827406842 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2678 c22240R_98_14 (by norm_num)

theorem c22240R_98_12 : rowsJ2 98 99 44 340 ≤ 136562525920954 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2677 c22240R_98_13 (by norm_num)

theorem c22240R_98_11 : rowsJ2 98 99 43 340 ≤ 151346523464965 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2676 c22240R_98_12 (by norm_num)

theorem c22240R_98_10 : rowsJ2 98 99 42 340 ≤ 167913859647605 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2675 c22240R_98_11 (by norm_num)

theorem c22240R_98_9 : rowsJ2 98 99 41 340 ≤ 183218517166396 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2674 c22240R_98_10 (by norm_num)

theorem c22240R_98_8 : rowsJ2 98 99 40 340 ≤ 197029210121070 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2673 c22240R_98_9 (by norm_num)

theorem c22240R_98_7 : rowsJ2 98 99 39 340 ≤ 209291540852171 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2672 c22240R_98_8 (by norm_num)

theorem c22240R_98_6 : rowsJ2 98 99 38 340 ≤ 220012709526112 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2671 c22240R_98_7 (by norm_num)

theorem c22240R_98_5 : rowsJ2 98 99 37 340 ≤ 229202760552281 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2670 c22240R_98_6 (by norm_num)

theorem c22240R_98_4 : rowsJ2 98 99 35 340 ≤ 241882272525233 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2669 c22240R_98_5 (by norm_num)

theorem c22240R_98_3 : rowsJ2 98 99 31 340 ≤ 251226281899177 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2668 c22240R_98_4 (by norm_num)

theorem c22240R_98_2 : rowsJ2 98 99 22 340 ≤ 251856329790498 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2667 c22240R_98_3 (by norm_num)

theorem c22240R_98_1 : rowsJ2 98 99 16 340 ≤ 251856329790498 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2666 c22240R_98_2 (by norm_num)

theorem c22240R_98_0 : rowsJ2 98 99 0 340 ≤ 251856329790498 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22240R_2665 c22240R_98_1 (by norm_num)

theorem hr22240R_98 : rows2 98 99 ≤ 251856329790498 := rows2_le_of_rowsJ2 98 99 c22240R_98_0

theorem c22240R_99_43 : rowsJ2 99 100 98 340 ≤ 15782210382782 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2754 rows22240R_2755 (by norm_num)

theorem c22240R_99_42 : rowsJ2 99 100 97 340 ≤ 22328464823907 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2753 c22240R_99_43 (by norm_num)

theorem c22240R_99_41 : rowsJ2 99 100 96 340 ≤ 28111133269072 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2752 c22240R_99_42 (by norm_num)

theorem c22240R_99_40 : rowsJ2 99 100 95 340 ≤ 33179172028617 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2751 c22240R_99_41 (by norm_num)

theorem c22240R_99_39 : rowsJ2 99 100 94 340 ≤ 37642725737699 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2750 c22240R_99_40 (by norm_num)

theorem c22240R_99_38 : rowsJ2 99 100 93 340 ≤ 41547205866159 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2749 c22240R_99_39 (by norm_num)

theorem c22240R_99_37 : rowsJ2 99 100 92 340 ≤ 44998168261607 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2748 c22240R_99_38 (by norm_num)

theorem c22240R_99_36 : rowsJ2 99 100 91 340 ≤ 48038117934028 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2747 c22240R_99_37 (by norm_num)

theorem c22240R_99_35 : rowsJ2 99 100 90 340 ≤ 50768889316165 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2746 c22240R_99_36 (by norm_num)

theorem c22240R_99_34 : rowsJ2 99 100 89 340 ≤ 53230775365630 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2745 c22240R_99_35 (by norm_num)

theorem c22240R_99_33 : rowsJ2 99 100 88 340 ≤ 55522487022282 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2744 c22240R_99_34 (by norm_num)

theorem c22240R_99_32 : rowsJ2 99 100 87 340 ≤ 57724203154715 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2743 c22240R_99_33 (by norm_num)

theorem c22240R_99_31 : rowsJ2 99 100 86 340 ≤ 59930065524572 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2742 c22240R_99_32 (by norm_num)

theorem c22240R_99_30 : rowsJ2 99 100 85 340 ≤ 62216296020093 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2741 c22240R_99_31 (by norm_num)

theorem c22240R_99_29 : rowsJ2 99 100 84 340 ≤ 64673231077788 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2740 c22240R_99_30 (by norm_num)

theorem c22240R_99_28 : rowsJ2 99 100 83 340 ≤ 67216701453747 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2739 c22240R_99_29 (by norm_num)

theorem c22240R_99_27 : rowsJ2 99 100 82 340 ≤ 69247653556839 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2738 c22240R_99_28 (by norm_num)

theorem c22240R_99_26 : rowsJ2 99 100 81 340 ≤ 70638800084509 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2737 c22240R_99_27 (by norm_num)

theorem c22240R_99_25 : rowsJ2 99 100 80 340 ≤ 71565226285525 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2736 c22240R_99_26 (by norm_num)

theorem c22240R_99_24 : rowsJ2 99 100 78 340 ≤ 72537939435733 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2735 c22240R_99_25 (by norm_num)

theorem c22240R_99_23 : rowsJ2 99 100 74 340 ≤ 72771702430657 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2734 c22240R_99_24 (by norm_num)

theorem c22240R_99_22 : rowsJ2 99 100 69 340 ≤ 72771702430657 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2733 c22240R_99_23 (by norm_num)

theorem c22240R_99_21 : rowsJ2 99 100 63 340 ≤ 72771702430657 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2732 c22240R_99_22 (by norm_num)

theorem c22240R_99_20 : rowsJ2 99 100 58 340 ≤ 72771702430657 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2731 c22240R_99_21 (by norm_num)

theorem c22240R_99_19 : rowsJ2 99 100 55 340 ≤ 73456536898094 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2730 c22240R_99_20 (by norm_num)

theorem c22240R_99_18 : rowsJ2 99 100 53 340 ≤ 76110987207486 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2729 c22240R_99_19 (by norm_num)

theorem c22240R_99_17 : rowsJ2 99 100 51 340 ≤ 81466128762237 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2728 c22240R_99_18 (by norm_num)

theorem c22240R_99_16 : rowsJ2 99 100 49 340 ≤ 90236136404944 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2727 c22240R_99_17 (by norm_num)

theorem c22240R_99_15 : rowsJ2 99 100 48 340 ≤ 96291875111745 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2726 c22240R_99_16 (by norm_num)

theorem c22240R_99_14 : rowsJ2 99 100 47 340 ≤ 103692973443535 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2725 c22240R_99_15 (by norm_num)

theorem c22240R_99_13 : rowsJ2 99 100 46 340 ≤ 112617273683767 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2724 c22240R_99_14 (by norm_num)

theorem c22240R_99_12 : rowsJ2 99 100 45 340 ≤ 123143007253018 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2723 c22240R_99_13 (by norm_num)

theorem c22240R_99_11 : rowsJ2 99 100 44 340 ≤ 135287754283958 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2722 c22240R_99_12 (by norm_num)

theorem c22240R_99_10 : rowsJ2 99 100 43 340 ≤ 149131510200103 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2721 c22240R_99_11 (by norm_num)

theorem c22240R_99_9 : rowsJ2 99 100 42 340 ≤ 164694560675572 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2720 c22240R_99_10 (by norm_num)

theorem c22240R_99_8 : rowsJ2 99 100 41 340 ≤ 180557237693741 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2719 c22240R_99_9 (by norm_num)

theorem c22240R_99_7 : rowsJ2 99 100 40 340 ≤ 195004525623954 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2718 c22240R_99_8 (by norm_num)

theorem c22240R_99_6 : rowsJ2 99 100 39 340 ≤ 207922623523802 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2717 c22240R_99_7 (by norm_num)

theorem c22240R_99_5 : rowsJ2 99 100 38 340 ≤ 219318883947734 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2716 c22240R_99_6 (by norm_num)

theorem c22240R_99_4 : rowsJ2 99 100 36 340 ≤ 236935567854373 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2715 c22240R_99_5 (by norm_num)

theorem c22240R_99_3 : rowsJ2 99 100 33 340 ≤ 250399915334662 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2714 c22240R_99_4 (by norm_num)

theorem c22240R_99_2 : rowsJ2 99 100 25 340 ≤ 254052674934020 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2713 c22240R_99_3 (by norm_num)

theorem c22240R_99_1 : rowsJ2 99 100 17 340 ≤ 254052674934020 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2712 c22240R_99_2 (by norm_num)

theorem c22240R_99_0 : rowsJ2 99 100 0 340 ≤ 254052674934020 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22240R_2711 c22240R_99_1 (by norm_num)

theorem hr22240R_99 : rows2 99 100 ≤ 254052674934020 := rows2_le_of_rowsJ2 99 100 c22240R_99_0

theorem c22240R_100_43 : rowsJ2 100 101 99 340 ≤ 18584249928381 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2799 rows22240R_2800 (by norm_num)

theorem c22240R_100_42 : rowsJ2 100 101 98 340 ≤ 26318228408415 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2798 c22240R_100_43 (by norm_num)

theorem c22240R_100_41 : rowsJ2 100 101 97 340 ≤ 33141907759195 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2797 c22240R_100_42 (by norm_num)

theorem c22240R_100_40 : rowsJ2 100 101 96 340 ≤ 39125469778155 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2796 c22240R_100_41 (by norm_num)

theorem c22240R_100_39 : rowsJ2 100 101 95 340 ≤ 44366912329248 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2795 c22240R_100_40 (by norm_num)

theorem c22240R_100_38 : rowsJ2 100 101 94 340 ≤ 48932130213818 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2794 c22240R_100_39 (by norm_num)

theorem c22240R_100_37 : rowsJ2 100 101 93 340 ≤ 52914300262160 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2793 c22240R_100_38 (by norm_num)

theorem c22240R_100_36 : rowsJ2 100 101 92 340 ≤ 56375571184103 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2792 c22240R_100_37 (by norm_num)

theorem c22240R_100_35 : rowsJ2 100 101 91 340 ≤ 59404857187283 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2791 c22240R_100_36 (by norm_num)

theorem c22240R_100_34 : rowsJ2 100 101 90 340 ≤ 62061205699120 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2790 c22240R_100_35 (by norm_num)

theorem c22240R_100_33 : rowsJ2 100 101 89 340 ≤ 64430126205587 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2789 c22240R_100_34 (by norm_num)

theorem c22240R_100_32 : rowsJ2 100 101 88 340 ≤ 66568266336892 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2788 c22240R_100_33 (by norm_num)

theorem c22240R_100_31 : rowsJ2 100 101 87 340 ≤ 68558320671312 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2787 c22240R_100_32 (by norm_num)

theorem c22240R_100_30 : rowsJ2 100 101 86 340 ≤ 70496669868627 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2786 c22240R_100_31 (by norm_num)

theorem c22240R_100_29 : rowsJ2 100 101 85 340 ≤ 72461743691959 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2785 c22240R_100_30 (by norm_num)

theorem c22240R_100_28 : rowsJ2 100 101 84 340 ≤ 74545800209624 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2784 c22240R_100_29 (by norm_num)

theorem c22240R_100_27 : rowsJ2 100 101 83 340 ≤ 76785291678546 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2783 c22240R_100_28 (by norm_num)

theorem c22240R_100_26 : rowsJ2 100 101 82 340 ≤ 78712531062932 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2782 c22240R_100_27 (by norm_num)

theorem c22240R_100_25 : rowsJ2 100 101 81 340 ≤ 80095869019421 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2781 c22240R_100_26 (by norm_num)

theorem c22240R_100_24 : rowsJ2 100 101 80 340 ≤ 81014213245198 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2780 c22240R_100_25 (by norm_num)

theorem c22240R_100_23 : rowsJ2 100 101 78 340 ≤ 81978063222370 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2779 c22240R_100_24 (by norm_num)

theorem c22240R_100_22 : rowsJ2 100 101 74 340 ≤ 82209675512144 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2778 c22240R_100_23 (by norm_num)

theorem c22240R_100_21 : rowsJ2 100 101 69 340 ≤ 82209675512144 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2777 c22240R_100_22 (by norm_num)

theorem c22240R_100_20 : rowsJ2 100 101 62 340 ≤ 82209675512144 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2776 c22240R_100_21 (by norm_num)

theorem c22240R_100_19 : rowsJ2 100 101 57 340 ≤ 82209675512144 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2775 c22240R_100_20 (by norm_num)

theorem c22240R_100_18 : rowsJ2 100 101 54 340 ≤ 83432348773006 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2774 c22240R_100_19 (by norm_num)

theorem c22240R_100_17 : rowsJ2 100 101 52 340 ≤ 86645388873954 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2773 c22240R_100_18 (by norm_num)

theorem c22240R_100_16 : rowsJ2 100 101 50 340 ≤ 92580199702429 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2772 c22240R_100_17 (by norm_num)

theorem c22240R_100_15 : rowsJ2 100 101 48 340 ≤ 102237629348206 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2771 c22240R_100_16 (by norm_num)

theorem c22240R_100_14 : rowsJ2 100 101 47 340 ≤ 108897146061653 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2770 c22240R_100_15 (by norm_num)

theorem c22240R_100_13 : rowsJ2 100 101 46 340 ≤ 117015242605104 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2769 c22240R_100_14 (by norm_num)

theorem c22240R_100_12 : rowsJ2 100 101 45 340 ≤ 126671037193604 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2768 c22240R_100_13 (by norm_num)

theorem c22240R_100_11 : rowsJ2 100 101 44 340 ≤ 137943634081298 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2767 c22240R_100_12 (by norm_num)

theorem c22240R_100_10 : rowsJ2 100 101 43 340 ≤ 150851274903469 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2766 c22240R_100_11 (by norm_num)

theorem c22240R_100_9 : rowsJ2 100 101 42 340 ≤ 165474916753981 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2765 c22240R_100_10 (by norm_num)

theorem c22240R_100_8 : rowsJ2 100 101 41 340 ≤ 181939359016354 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2764 c22240R_100_9 (by norm_num)

theorem c22240R_100_7 : rowsJ2 100 101 40 340 ≤ 197023901987571 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2763 c22240R_100_8 (by norm_num)

theorem c22240R_100_6 : rowsJ2 100 101 39 340 ≤ 210598274726274 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2762 c22240R_100_7 (by norm_num)

theorem c22240R_100_5 : rowsJ2 100 101 38 340 ≤ 222669982674512 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2761 c22240R_100_6 (by norm_num)

theorem c22240R_100_4 : rowsJ2 100 101 36 340 ≤ 241578419165109 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2760 c22240R_100_5 (by norm_num)

theorem c22240R_100_3 : rowsJ2 100 101 33 340 ≤ 256347630027953 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2759 c22240R_100_4 (by norm_num)

theorem c22240R_100_2 : rowsJ2 100 101 26 340 ≤ 260509582570792 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2758 c22240R_100_3 (by norm_num)

theorem c22240R_100_1 : rowsJ2 100 101 17 340 ≤ 260509582570792 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2757 c22240R_100_2 (by norm_num)

theorem c22240R_100_0 : rowsJ2 100 101 0 340 ≤ 260509582570792 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22240R_2756 c22240R_100_1 (by norm_num)

theorem hr22240R_100 : rows2 100 101 ≤ 260509582570792 := rows2_le_of_rowsJ2 100 101 c22240R_100_0

theorem c22240R_101_45 : rowsJ2 101 102 100 340 ≤ 21886786021205 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2846 rows22240R_2847 (by norm_num)

theorem c22240R_101_44 : rowsJ2 101 102 99 340 ≤ 31035091134917 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2845 c22240R_101_45 (by norm_num)

theorem c22240R_101_43 : rowsJ2 101 102 98 340 ≤ 39134363842971 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2844 c22240R_101_44 (by norm_num)

theorem c22240R_101_42 : rowsJ2 101 102 97 340 ≤ 46242139863676 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2843 c22240R_101_43 (by norm_num)

theorem c22240R_101_41 : rowsJ2 101 102 96 340 ≤ 52478851557079 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2842 c22240R_101_42 (by norm_num)

theorem c22240R_101_40 : rowsJ2 101 102 95 340 ≤ 57897486419806 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2841 c22240R_101_41 (by norm_num)

theorem c22240R_101_39 : rowsJ2 101 102 94 340 ≤ 62612834919925 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2840 c22240R_101_40 (by norm_num)

theorem c22240R_101_38 : rowsJ2 101 102 93 340 ≤ 66673931357701 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2839 c22240R_101_39 (by norm_num)

theorem c22240R_101_37 : rowsJ2 101 102 92 340 ≤ 70190550818475 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2838 c22240R_101_38 (by norm_num)

theorem c22240R_101_36 : rowsJ2 101 102 91 340 ≤ 73208304682918 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2837 c22240R_101_37 (by norm_num)

theorem c22240R_101_35 : rowsJ2 101 102 90 340 ≤ 75832517052076 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2836 c22240R_101_36 (by norm_num)

theorem c22240R_101_34 : rowsJ2 101 102 89 340 ≤ 78106011598502 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2835 c22240R_101_35 (by norm_num)

theorem c22240R_101_33 : rowsJ2 101 102 88 340 ≤ 80130526033538 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2834 c22240R_101_34 (by norm_num)

theorem c22240R_101_32 : rowsJ2 101 102 87 340 ≤ 81946789544965 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2833 c22240R_101_33 (by norm_num)

theorem c22240R_101_31 : rowsJ2 101 102 86 340 ≤ 83653550152801 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2832 c22240R_101_32 (by norm_num)

theorem c22240R_101_30 : rowsJ2 101 102 85 340 ≤ 85331599931959 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2831 c22240R_101_31 (by norm_num)

theorem c22240R_101_29 : rowsJ2 101 102 84 340 ≤ 87075258014554 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2830 c22240R_101_30 (by norm_num)

theorem c22240R_101_28 : rowsJ2 101 102 83 340 ≤ 88961491993780 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2829 c22240R_101_29 (by norm_num)

theorem c22240R_101_27 : rowsJ2 101 102 82 340 ≤ 90683098878943 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2828 c22240R_101_28 (by norm_num)

theorem c22240R_101_26 : rowsJ2 101 102 81 340 ≤ 92059043137826 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2827 c22240R_101_27 (by norm_num)

theorem c22240R_101_25 : rowsJ2 101 102 80 340 ≤ 92969459162140 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2826 c22240R_101_26 (by norm_num)

theorem c22240R_101_24 : rowsJ2 101 102 79 340 ≤ 93567528355342 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2825 c22240R_101_25 (by norm_num)

theorem c22240R_101_23 : rowsJ2 101 102 77 340 ≤ 94096480227196 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2824 c22240R_101_24 (by norm_num)

theorem c22240R_101_22 : rowsJ2 101 102 73 340 ≤ 94154044917906 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2823 c22240R_101_23 (by norm_num)

theorem c22240R_101_21 : rowsJ2 101 102 68 340 ≤ 94154044917906 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2822 c22240R_101_22 (by norm_num)

theorem c22240R_101_20 : rowsJ2 101 102 61 340 ≤ 94154044917906 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2821 c22240R_101_21 (by norm_num)

theorem c22240R_101_19 : rowsJ2 101 102 56 340 ≤ 94154044917906 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2820 c22240R_101_20 (by norm_num)

theorem c22240R_101_18 : rowsJ2 101 102 53 340 ≤ 95838705542389 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2819 c22240R_101_19 (by norm_num)

theorem c22240R_101_17 : rowsJ2 101 102 51 340 ≤ 99438153292652 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2818 c22240R_101_18 (by norm_num)

theorem c22240R_101_16 : rowsJ2 101 102 49 340 ≤ 105871068254789 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2817 c22240R_101_17 (by norm_num)

theorem c22240R_101_15 : rowsJ2 101 102 47 340 ≤ 116438488273278 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2816 c22240R_101_16 (by norm_num)

theorem c22240R_101_14 : rowsJ2 101 102 46 340 ≤ 123719264875931 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2815 c22240R_101_15 (by norm_num)

theorem c22240R_101_13 : rowsJ2 101 102 45 340 ≤ 132471822578777 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2814 c22240R_101_14 (by norm_num)

theorem c22240R_101_12 : rowsJ2 101 102 44 340 ≤ 142776120010571 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2813 c22240R_101_13 (by norm_num)

theorem c22240R_101_11 : rowsJ2 101 102 43 340 ≤ 154712147844056 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2812 c22240R_101_12 (by norm_num)

theorem c22240R_101_10 : rowsJ2 101 102 42 340 ≤ 168298812519404 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2811 c22240R_101_11 (by norm_num)

theorem c22240R_101_9 : rowsJ2 101 102 41 340 ≤ 183722305606744 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2810 c22240R_101_10 (by norm_num)

theorem c22240R_101_8 : rowsJ2 101 102 40 340 ≤ 199385774670295 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2809 c22240R_101_9 (by norm_num)

theorem c22240R_101_7 : rowsJ2 101 102 39 340 ≤ 213511803521494 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2808 c22240R_101_8 (by norm_num)

theorem c22240R_101_6 : rowsJ2 101 102 38 340 ≤ 226152949514726 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2807 c22240R_101_7 (by norm_num)

theorem c22240R_101_5 : rowsJ2 101 102 37 340 ≤ 237319649919717 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2806 c22240R_101_6 (by norm_num)

theorem c22240R_101_4 : rowsJ2 101 102 35 340 ≤ 253283419036275 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2805 c22240R_101_5 (by norm_num)

theorem c22240R_101_3 : rowsJ2 101 102 33 340 ≤ 262435792555682 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2804 c22240R_101_4 (by norm_num)

theorem c22240R_101_2 : rowsJ2 101 102 27 340 ≤ 267324765505863 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2803 c22240R_101_3 (by norm_num)

theorem c22240R_101_1 : rowsJ2 101 102 17 340 ≤ 267324765505863 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2802 c22240R_101_2 (by norm_num)

theorem c22240R_101_0 : rowsJ2 101 102 0 340 ≤ 267324765505863 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22240R_2801 c22240R_101_1 (by norm_num)

theorem hr22240R_101 : rows2 101 102 ≤ 267324765505863 := rows2_le_of_rowsJ2 101 102 c22240R_101_0

theorem c22240R_102_45 : rowsJ2 102 103 101 340 ≤ 25796326177427 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2893 rows22240R_2894 (by norm_num)

theorem c22240R_102_44 : rowsJ2 102 103 100 340 ≤ 36654746904079 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2892 c22240R_102_45 (by norm_num)

theorem c22240R_102_43 : rowsJ2 102 103 99 340 ≤ 46298121139455 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2891 c22240R_102_44 (by norm_num)

theorem c22240R_102_42 : rowsJ2 102 103 98 340 ≤ 54806238220297 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2890 c22240R_102_43 (by norm_num)

theorem c22240R_102_41 : rowsJ2 102 103 97 340 ≤ 62288455832219 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2889 c22240R_102_42 (by norm_num)

theorem c22240R_102_40 : rowsJ2 102 103 96 340 ≤ 68819138686467 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2888 c22240R_102_41 (by norm_num)

theorem c22240R_102_39 : rowsJ2 102 103 95 340 ≤ 74501654310779 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2887 c22240R_102_40 (by norm_num)

theorem c22240R_102_38 : rowsJ2 102 103 94 340 ≤ 79405618008629 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2886 c22240R_102_39 (by norm_num)

theorem c22240R_102_37 : rowsJ2 102 103 93 340 ≤ 83629095435959 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2885 c22240R_102_38 (by norm_num)

theorem c22240R_102_36 : rowsJ2 102 103 92 340 ≤ 87237552781899 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2884 c22240R_102_37 (by norm_num)

theorem c22240R_102_35 : rowsJ2 102 103 91 340 ≤ 90324369303593 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2883 c22240R_102_36 (by norm_num)

theorem c22240R_102_34 : rowsJ2 102 103 90 340 ≤ 92951398249694 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2882 c22240R_102_35 (by norm_num)

theorem c22240R_102_33 : rowsJ2 102 103 89 340 ≤ 95207887356560 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2881 c22240R_102_34 (by norm_num)

theorem c22240R_102_32 : rowsJ2 102 103 88 340 ≤ 97152718123746 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2880 c22240R_102_33 (by norm_num)

theorem c22240R_102_31 : rowsJ2 102 103 87 340 ≤ 98871862699648 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2879 c22240R_102_32 (by norm_num)

theorem c22240R_102_30 : rowsJ2 102 103 86 340 ≤ 100421931021736 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2878 c22240R_102_31 (by norm_num)

theorem c22240R_102_29 : rowsJ2 102 103 85 340 ≤ 101886208430202 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2877 c22240R_102_30 (by norm_num)

theorem c22240R_102_28 : rowsJ2 102 103 84 340 ≤ 103361234687760 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2876 c22240R_102_29 (by norm_num)

theorem c22240R_102_27 : rowsJ2 102 103 83 340 ≤ 104926165815311 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2875 c22240R_102_28 (by norm_num)

theorem c22240R_102_26 : rowsJ2 102 103 82 340 ≤ 106633985835774 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2874 c22240R_102_27 (by norm_num)

theorem c22240R_102_25 : rowsJ2 102 103 81 340 ≤ 107903098230575 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2873 c22240R_102_26 (by norm_num)

theorem c22240R_102_24 : rowsJ2 102 103 80 340 ≤ 108805737786071 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2872 c22240R_102_25 (by norm_num)

theorem c22240R_102_23 : rowsJ2 102 103 79 340 ≤ 109398524935487 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2871 c22240R_102_24 (by norm_num)

theorem c22240R_102_22 : rowsJ2 102 103 77 340 ≤ 109922582272977 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2870 c22240R_102_23 (by norm_num)

theorem c22240R_102_21 : rowsJ2 102 103 73 340 ≤ 109979615027077 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2869 c22240R_102_22 (by norm_num)

theorem c22240R_102_20 : rowsJ2 102 103 67 340 ≤ 109979615027077 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2868 c22240R_102_21 (by norm_num)

theorem c22240R_102_19 : rowsJ2 102 103 60 340 ≤ 109979615027077 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2867 c22240R_102_20 (by norm_num)

theorem c22240R_102_18 : rowsJ2 102 103 55 340 ≤ 110070271966576 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2866 c22240R_102_19 (by norm_num)

theorem c22240R_102_17 : rowsJ2 102 103 52 340 ≤ 112319352874653 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2865 c22240R_102_18 (by norm_num)

theorem c22240R_102_16 : rowsJ2 102 103 50 340 ≤ 116313582675849 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2864 c22240R_102_17 (by norm_num)

theorem c22240R_102_15 : rowsJ2 102 103 48 340 ≤ 123446391596378 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2863 c22240R_102_16 (by norm_num)

theorem c22240R_102_14 : rowsJ2 102 103 46 340 ≤ 135145408777313 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2862 c22240R_102_15 (by norm_num)

theorem c22240R_102_13 : rowsJ2 102 103 45 340 ≤ 143061325222345 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2861 c22240R_102_14 (by norm_num)

theorem c22240R_102_12 : rowsJ2 102 103 44 340 ≤ 152462797654043 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2860 c22240R_102_13 (by norm_num)

theorem c22240R_102_11 : rowsJ2 102 103 43 340 ≤ 163430661072093 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2859 c22240R_102_12 (by norm_num)

theorem c22240R_102_10 : rowsJ2 102 103 42 340 ≤ 176045830534952 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2858 c22240R_102_11 (by norm_num)

theorem c22240R_102_9 : rowsJ2 102 103 41 340 ≤ 190432670089913 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2857 c22240R_102_10 (by norm_num)

theorem c22240R_102_8 : rowsJ2 102 103 40 340 ≤ 206783346577058 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2856 c22240R_102_9 (by norm_num)

theorem c22240R_102_7 : rowsJ2 102 103 39 340 ≤ 221569159737841 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2855 c22240R_102_8 (by norm_num)

theorem c22240R_102_6 : rowsJ2 102 103 38 340 ≤ 234780520061289 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2854 c22240R_102_7 (by norm_num)

theorem c22240R_102_5 : rowsJ2 102 103 37 340 ≤ 246535188754073 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2853 c22240R_102_6 (by norm_num)

theorem c22240R_102_4 : rowsJ2 102 103 35 340 ≤ 263711292969939 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2852 c22240R_102_5 (by norm_num)

theorem c22240R_102_3 : rowsJ2 102 103 33 340 ≤ 273673983534482 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2851 c22240R_102_4 (by norm_num)

theorem c22240R_102_2 : rowsJ2 102 103 28 340 ≤ 279395330403726 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2850 c22240R_102_3 (by norm_num)

theorem c22240R_102_1 : rowsJ2 102 103 17 340 ≤ 279395330403726 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2849 c22240R_102_2 (by norm_num)

theorem c22240R_102_0 : rowsJ2 102 103 0 340 ≤ 279395330403726 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22240R_2848 c22240R_102_1 (by norm_num)

theorem hr22240R_102 : rows2 102 103 ≤ 279395330403726 := rows2_le_of_rowsJ2 102 103 c22240R_102_0

theorem c22240R_103_45 : rowsJ2 103 104 102 340 ≤ 30285042754723 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2940 rows22240R_2941 (by norm_num)

theorem c22240R_103_44 : rowsJ2 103 104 101 340 ≤ 43115956419158 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2939 c22240R_103_45 (by norm_num)

theorem c22240R_103_43 : rowsJ2 103 104 100 340 ≤ 54571632743254 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2938 c22240R_103_44 (by norm_num)

theorem c22240R_103_42 : rowsJ2 103 104 99 340 ≤ 64720374339428 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2937 c22240R_103_43 (by norm_num)

theorem c22240R_103_41 : rowsJ2 103 104 98 340 ≤ 73695180903071 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2936 c22240R_103_42 (by norm_num)

theorem c22240R_103_40 : rowsJ2 103 104 97 340 ≤ 81558528138679 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2935 c22240R_103_41 (by norm_num)

theorem c22240R_103_39 : rowsJ2 103 104 96 340 ≤ 88436453891986 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2934 c22240R_103_40 (by norm_num)

theorem c22240R_103_38 : rowsJ2 103 104 95 340 ≤ 94386358950836 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2933 c22240R_103_39 (by norm_num)

theorem c22240R_103_37 : rowsJ2 103 104 94 340 ≤ 99528097392107 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2932 c22240R_103_38 (by norm_num)

theorem c22240R_103_36 : rowsJ2 103 104 93 340 ≤ 103914658078000 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2931 c22240R_103_37 (by norm_num)

theorem c22240R_103_35 : rowsJ2 103 104 92 340 ≤ 107660404403409 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2930 c22240R_103_36 (by norm_num)

theorem c22240R_103_34 : rowsJ2 103 104 91 340 ≤ 110814502486503 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2929 c22240R_103_35 (by norm_num)

theorem c22240R_103_33 : rowsJ2 103 104 90 340 ≤ 113486445939983 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2928 c22240R_103_34 (by norm_num)

theorem c22240R_103_32 : rowsJ2 103 104 89 340 ≤ 115722104553479 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2927 c22240R_103_33 (by norm_num)

theorem c22240R_103_31 : rowsJ2 103 104 88 340 ≤ 117626662687194 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2926 c22240R_103_32 (by norm_num)

theorem c22240R_103_30 : rowsJ2 103 104 87 340 ≤ 119243326100870 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2925 c22240R_103_31 (by norm_num)

theorem c22240R_103_29 : rowsJ2 103 104 86 340 ≤ 120673832498390 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2924 c22240R_103_30 (by norm_num)

theorem c22240R_103_28 : rowsJ2 103 104 85 340 ≤ 121959415940713 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2923 c22240R_103_29 (by norm_num)

theorem c22240R_103_27 : rowsJ2 103 104 84 340 ≤ 123198963438739 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2922 c22240R_103_28 (by norm_num)

theorem c22240R_103_26 : rowsJ2 103 104 83 340 ≤ 124473972994150 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2921 c22240R_103_27 (by norm_num)

theorem c22240R_103_25 : rowsJ2 103 104 82 340 ≤ 125879048608378 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2920 c22240R_103_26 (by norm_num)

theorem c22240R_103_24 : rowsJ2 103 104 81 340 ≤ 127137807385752 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2919 c22240R_103_25 (by norm_num)

theorem c22240R_103_23 : rowsJ2 103 104 80 340 ≤ 128032821449376 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2918 c22240R_103_24 (by norm_num)

theorem c22240R_103_22 : rowsJ2 103 104 79 340 ≤ 128620396026491 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2917 c22240R_103_23 (by norm_num)

theorem c22240R_103_21 : rowsJ2 103 104 77 340 ≤ 129139650778725 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2916 c22240R_103_22 (by norm_num)

theorem c22240R_103_20 : rowsJ2 103 104 73 340 ≤ 129196155005083 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2915 c22240R_103_21 (by norm_num)

theorem c22240R_103_19 : rowsJ2 103 104 67 340 ≤ 129196155005083 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2914 c22240R_103_20 (by norm_num)

theorem c22240R_103_18 : rowsJ2 103 104 59 340 ≤ 129196155005083 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2913 c22240R_103_19 (by norm_num)

theorem c22240R_103_17 : rowsJ2 103 104 54 340 ≤ 129380639916709 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2912 c22240R_103_18 (by norm_num)

theorem c22240R_103_16 : rowsJ2 103 104 51 340 ≤ 131923749640860 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2911 c22240R_103_17 (by norm_num)

theorem c22240R_103_15 : rowsJ2 103 104 49 340 ≤ 136223098641511 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2910 c22240R_103_16 (by norm_num)

theorem c22240R_103_14 : rowsJ2 103 104 47 340 ≤ 144071262399897 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2909 c22240R_103_15 (by norm_num)

theorem c22240R_103_13 : rowsJ2 103 104 45 340 ≤ 156828454308270 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2908 c22240R_103_14 (by norm_num)

theorem c22240R_103_12 : rowsJ2 103 104 44 340 ≤ 165291641520730 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2907 c22240R_103_13 (by norm_num)

theorem c22240R_103_11 : rowsJ2 103 104 43 340 ≤ 175253614701540 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2906 c22240R_103_12 (by norm_num)

theorem c22240R_103_10 : rowsJ2 103 104 42 340 ≤ 186796097067782 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2905 c22240R_103_11 (by norm_num)

theorem c22240R_103_9 : rowsJ2 103 104 41 340 ≤ 200106235093670 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2904 c22240R_103_10 (by norm_num)

theorem c22240R_103_8 : rowsJ2 103 104 40 340 ≤ 215314058389570 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2903 c22240R_103_9 (by norm_num)

theorem c22240R_103_7 : rowsJ2 103 104 39 340 ≤ 230762026019887 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2902 c22240R_103_8 (by norm_num)

theorem c22240R_103_6 : rowsJ2 103 104 38 340 ≤ 244543940446659 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2901 c22240R_103_7 (by norm_num)

theorem c22240R_103_5 : rowsJ2 103 104 37 340 ≤ 256776445493921 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2900 c22240R_103_6 (by norm_num)

theorem c22240R_103_4 : rowsJ2 103 104 36 340 ≤ 267019139461643 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2899 c22240R_103_5 (by norm_num)

theorem c22240R_103_3 : rowsJ2 103 104 34 340 ≤ 281358315328689 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2898 c22240R_103_4 (by norm_num)

theorem c22240R_103_2 : rowsJ2 103 104 30 340 ≤ 292297521792678 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2897 c22240R_103_3 (by norm_num)

theorem c22240R_103_1 : rowsJ2 103 104 18 340 ≤ 292721325749740 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2896 c22240R_103_2 (by norm_num)

theorem c22240R_103_0 : rowsJ2 103 104 0 340 ≤ 292721325749740 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22240R_2895 c22240R_103_1 (by norm_num)

theorem hr22240R_103 : rows2 103 104 ≤ 292721325749740 := rows2_le_of_rowsJ2 103 104 c22240R_103_0

theorem c22240R_104_43 : rowsJ2 104 105 101 340 ≤ 292370357960702 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2985 rows22240R_2986 (by norm_num)

theorem c22240R_104_42 : rowsJ2 104 105 100 340 ≤ 304471447390601 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2984 c22240R_104_43 (by norm_num)

theorem c22240R_104_41 : rowsJ2 104 105 99 340 ≤ 315222530085010 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2983 c22240R_104_42 (by norm_num)

theorem c22240R_104_40 : rowsJ2 104 105 98 340 ≤ 324708618546794 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2982 c22240R_104_41 (by norm_num)

theorem c22240R_104_39 : rowsJ2 104 105 97 340 ≤ 333045521391048 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2981 c22240R_104_40 (by norm_num)

theorem c22240R_104_38 : rowsJ2 104 105 96 340 ≤ 340312225798078 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2980 c22240R_104_39 (by norm_num)

theorem c22240R_104_37 : rowsJ2 104 105 95 340 ≤ 346617935202422 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2979 c22240R_104_38 (by norm_num)

theorem c22240R_104_36 : rowsJ2 104 105 94 340 ≤ 352036367261217 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2978 c22240R_104_37 (by norm_num)

theorem c22240R_104_35 : rowsJ2 104 105 93 340 ≤ 356670885533515 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2977 c22240R_104_36 (by norm_num)

theorem c22240R_104_34 : rowsJ2 104 105 92 340 ≤ 360590605798599 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2976 c22240R_104_35 (by norm_num)

theorem c22240R_104_33 : rowsJ2 104 105 91 340 ≤ 363893733838618 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2975 c22240R_104_34 (by norm_num)

theorem c22240R_104_32 : rowsJ2 104 105 90 340 ≤ 366645377453615 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2974 c22240R_104_33 (by norm_num)

theorem c22240R_104_31 : rowsJ2 104 105 89 340 ≤ 368939195270266 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2973 c22240R_104_32 (by norm_num)

theorem c22240R_104_30 : rowsJ2 104 105 88 340 ≤ 370836819203171 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2972 c22240R_104_31 (by norm_num)

theorem c22240R_104_29 : rowsJ2 104 105 87 340 ≤ 372427911818437 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2971 c22240R_104_30 (by norm_num)

theorem c22240R_104_28 : rowsJ2 104 105 86 340 ≤ 373771267946567 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2970 c22240R_104_29 (by norm_num)

theorem c22240R_104_27 : rowsJ2 104 105 85 340 ≤ 374953409263696 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2969 c22240R_104_28 (by norm_num)

theorem c22240R_104_26 : rowsJ2 104 105 84 340 ≤ 376030992324725 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2968 c22240R_104_27 (by norm_num)

theorem c22240R_104_25 : rowsJ2 104 105 83 340 ≤ 377087986829893 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2967 c22240R_104_26 (by norm_num)

theorem c22240R_104_24 : rowsJ2 104 105 82 340 ≤ 378221199339923 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2966 c22240R_104_25 (by norm_num)

theorem c22240R_104_23 : rowsJ2 104 105 81 340 ≤ 379469871409803 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2965 c22240R_104_24 (by norm_num)

theorem c22240R_104_22 : rowsJ2 104 105 80 340 ≤ 380357408076399 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2964 c22240R_104_23 (by norm_num)

theorem c22240R_104_21 : rowsJ2 104 105 79 340 ≤ 380939865456497 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2963 c22240R_104_22 (by norm_num)

theorem c22240R_104_20 : rowsJ2 104 105 76 340 ≤ 381510361121977 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2962 c22240R_104_21 (by norm_num)

theorem c22240R_104_19 : rowsJ2 104 105 72 340 ≤ 381510361121977 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2961 c22240R_104_20 (by norm_num)

theorem c22240R_104_18 : rowsJ2 104 105 66 340 ≤ 381510361121977 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2960 c22240R_104_19 (by norm_num)

theorem c22240R_104_17 : rowsJ2 104 105 58 340 ≤ 381510361121977 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2959 c22240R_104_18 (by norm_num)

theorem c22240R_104_16 : rowsJ2 104 105 53 340 ≤ 381884873346857 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2958 c22240R_104_17 (by norm_num)

theorem c22240R_104_15 : rowsJ2 104 105 50 340 ≤ 384728467179325 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2957 c22240R_104_16 (by norm_num)

theorem c22240R_104_14 : rowsJ2 104 105 48 340 ≤ 389532971205343 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2956 c22240R_104_15 (by norm_num)

theorem c22240R_104_13 : rowsJ2 104 105 46 340 ≤ 398316358940249 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2955 c22240R_104_14 (by norm_num)

theorem c22240R_104_12 : rowsJ2 104 105 44 340 ≤ 412155846599649 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2954 c22240R_104_13 (by norm_num)

theorem c22240R_104_11 : rowsJ2 104 105 43 340 ≤ 421179150319949 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2953 c22240R_104_12 (by norm_num)

theorem c22240R_104_10 : rowsJ2 104 105 42 340 ≤ 431715040305232 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2952 c22240R_104_11 (by norm_num)

theorem c22240R_104_9 : rowsJ2 104 105 41 340 ≤ 443952011120584 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2951 c22240R_104_10 (by norm_num)

theorem c22240R_104_8 : rowsJ2 104 105 40 340 ≤ 458083172099438 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2950 c22240R_104_9 (by norm_num)

theorem c22240R_104_7 : rowsJ2 104 105 39 340 ≤ 474244593416156 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2949 c22240R_104_8 (by norm_num)

theorem c22240R_104_6 : rowsJ2 104 105 38 340 ≤ 488709672838562 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2948 c22240R_104_7 (by norm_num)

theorem c22240R_104_5 : rowsJ2 104 105 37 340 ≤ 501531875869308 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2947 c22240R_104_6 (by norm_num)

theorem c22240R_104_4 : rowsJ2 104 105 36 340 ≤ 512265959259841 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2946 c22240R_104_5 (by norm_num)

theorem c22240R_104_3 : rowsJ2 104 105 34 340 ≤ 527735817509586 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2945 c22240R_104_4 (by norm_num)

theorem c22240R_104_2 : rowsJ2 104 105 30 340 ≤ 540145948989103 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2944 c22240R_104_3 (by norm_num)

theorem c22240R_104_1 : rowsJ2 104 105 18 340 ≤ 540674685060092 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2943 c22240R_104_2 (by norm_num)

theorem c22240R_104_0 : rowsJ2 104 105 0 340 ≤ 540674685060092 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22240R_2942 c22240R_104_1 (by norm_num)

theorem hr22240R_104 : rows2 104 105 ≤ 540674685060092 := rows2_le_of_rowsJ2 104 105 c22240R_104_0

theorem c22240R_105_38 : rowsJ2 105 106 101 340 ≤ 402915166733972 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3025 rows22240R_3026 (by norm_num)

theorem c22240R_105_37 : rowsJ2 105 106 100 340 ≤ 415709770524812 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3024 c22240R_105_38 (by norm_num)

theorem c22240R_105_36 : rowsJ2 105 106 99 340 ≤ 427074105103787 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3023 c22240R_105_37 (by norm_num)

theorem c22240R_105_35 : rowsJ2 105 106 98 340 ≤ 437130999574728 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3022 c22240R_105_36 (by norm_num)

theorem c22240R_105_34 : rowsJ2 105 106 97 340 ≤ 445948368563036 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3021 c22240R_105_35 (by norm_num)

theorem c22240R_105_33 : rowsJ2 105 106 96 340 ≤ 453658387266137 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3020 c22240R_105_34 (by norm_num)

theorem c22240R_105_32 : rowsJ2 105 106 95 340 ≤ 460323299766945 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3019 c22240R_105_33 (by norm_num)

theorem c22240R_105_31 : rowsJ2 105 106 94 340 ≤ 466068489356846 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3018 c22240R_105_32 (by norm_num)

theorem c22240R_105_30 : rowsJ2 105 106 92 340 ≤ 475091009749035 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3017 c22240R_105_31 (by norm_num)

theorem c22240R_105_29 : rowsJ2 105 106 90 340 ≤ 481414506930097 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3016 c22240R_105_30 (by norm_num)

theorem c22240R_105_28 : rowsJ2 105 106 88 340 ≤ 485691476129951 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3015 c22240R_105_29 (by norm_num)

theorem c22240R_105_27 : rowsJ2 105 106 86 340 ≤ 488542905433538 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3014 c22240R_105_28 (by norm_num)

theorem c22240R_105_26 : rowsJ2 105 106 85 340 ≤ 489613306330829 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3013 c22240R_105_27 (by norm_num)

theorem c22240R_105_25 : rowsJ2 105 106 84 340 ≤ 490563223839766 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3012 c22240R_105_26 (by norm_num)

theorem c22240R_105_24 : rowsJ2 105 106 83 340 ≤ 491434472966644 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3011 c22240R_105_25 (by norm_num)

theorem c22240R_105_23 : rowsJ2 105 106 82 340 ≤ 492326188139021 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3010 c22240R_105_24 (by norm_num)

theorem c22240R_105_22 : rowsJ2 105 106 81 340 ≤ 493320673339958 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3009 c22240R_105_23 (by norm_num)

theorem c22240R_105_21 : rowsJ2 105 106 80 340 ≤ 494200941090417 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3008 c22240R_105_22 (by norm_num)

theorem c22240R_105_20 : rowsJ2 105 106 79 340 ≤ 494778411035618 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3007 c22240R_105_21 (by norm_num)

theorem c22240R_105_19 : rowsJ2 105 106 76 340 ≤ 495343673979260 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3006 c22240R_105_20 (by norm_num)

theorem c22240R_105_18 : rowsJ2 105 106 72 340 ≤ 495343673979260 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3005 c22240R_105_19 (by norm_num)

theorem c22240R_105_17 : rowsJ2 105 106 66 340 ≤ 495343673979260 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3004 c22240R_105_18 (by norm_num)

theorem c22240R_105_16 : rowsJ2 105 106 57 340 ≤ 495368970275502 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3003 c22240R_105_17 (by norm_num)

theorem c22240R_105_15 : rowsJ2 105 106 52 340 ≤ 495744774995887 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3002 c22240R_105_16 (by norm_num)

theorem c22240R_105_14 : rowsJ2 105 106 49 340 ≤ 498694859575049 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3001 c22240R_105_15 (by norm_num)

theorem c22240R_105_13 : rowsJ2 105 106 47 340 ≤ 504012454949390 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_3000 c22240R_105_14 (by norm_num)

theorem c22240R_105_12 : rowsJ2 105 106 45 340 ≤ 513648759059464 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_2999 c22240R_105_13 (by norm_num)

theorem c22240R_105_11 : rowsJ2 105 106 43 340 ≤ 528383767565824 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_2998 c22240R_105_12 (by norm_num)

theorem c22240R_105_10 : rowsJ2 105 106 42 340 ≤ 537872827366996 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_2997 c22240R_105_11 (by norm_num)

theorem c22240R_105_9 : rowsJ2 105 106 41 340 ≤ 548994057652385 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_2996 c22240R_105_10 (by norm_num)

theorem c22240R_105_8 : rowsJ2 105 106 40 340 ≤ 561941891322353 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_2995 c22240R_105_9 (by norm_num)

theorem c22240R_105_7 : rowsJ2 105 106 39 340 ≤ 576915759731033 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_2994 c22240R_105_8 (by norm_num)

theorem c22240R_105_6 : rowsJ2 105 106 38 340 ≤ 592066543993650 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_2993 c22240R_105_7 (by norm_num)

theorem c22240R_105_5 : rowsJ2 105 106 37 340 ≤ 605478799730149 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_2992 c22240R_105_6 (by norm_num)

theorem c22240R_105_4 : rowsJ2 105 106 35 340 ≤ 625977390211093 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_2991 c22240R_105_5 (by norm_num)

theorem c22240R_105_3 : rowsJ2 105 106 33 340 ≤ 638722500964755 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_2990 c22240R_105_4 (by norm_num)

theorem c22240R_105_2 : rowsJ2 105 106 30 340 ≤ 647197517560862 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_2989 c22240R_105_3 (by norm_num)

theorem c22240R_105_1 : rowsJ2 105 106 19 340 ≤ 647941238024148 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_2988 c22240R_105_2 (by norm_num)

theorem c22240R_105_0 : rowsJ2 105 106 0 340 ≤ 647941238024148 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22240R_2987 c22240R_105_1 (by norm_num)

theorem hr22240R_105 : rows2 105 106 ≤ 647941238024148 := rows2_le_of_rowsJ2 105 106 c22240R_105_0

theorem c22240R_106_35 : rowsJ2 106 107 100 340 ≤ 620274257583977 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3062 rows22240R_3063 (by norm_num)

theorem c22240R_106_34 : rowsJ2 106 107 99 340 ≤ 632318040715970 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3061 c22240R_106_35 (by norm_num)

theorem c22240R_106_33 : rowsJ2 106 107 98 340 ≤ 642975061536340 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3060 c22240R_106_34 (by norm_num)

theorem c22240R_106_32 : rowsJ2 106 107 97 340 ≤ 652367721840014 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3059 c22240R_106_33 (by norm_num)

theorem c22240R_106_31 : rowsJ2 106 107 96 340 ≤ 660563537362361 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3058 c22240R_106_32 (by norm_num)

theorem c22240R_106_30 : rowsJ2 106 107 95 340 ≤ 667678069443725 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3057 c22240R_106_31 (by norm_num)

theorem c22240R_106_29 : rowsJ2 106 107 94 340 ≤ 673789567037591 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3056 c22240R_106_30 (by norm_num)

theorem c22240R_106_28 : rowsJ2 106 107 93 340 ≤ 679007148712911 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3055 c22240R_106_29 (by norm_num)

theorem c22240R_106_27 : rowsJ2 106 107 91 340 ≤ 687083409384563 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3054 c22240R_106_28 (by norm_num)

theorem c22240R_106_26 : rowsJ2 106 107 89 340 ≤ 692594770678388 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3053 c22240R_106_27 (by norm_num)

theorem c22240R_106_25 : rowsJ2 106 107 87 340 ≤ 696193681599764 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3052 c22240R_106_26 (by norm_num)

theorem c22240R_106_24 : rowsJ2 106 107 85 340 ≤ 698501661668232 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3051 c22240R_106_25 (by norm_num)

theorem c22240R_106_23 : rowsJ2 106 107 83 340 ≤ 700114240087073 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3050 c22240R_106_24 (by norm_num)

theorem c22240R_106_22 : rowsJ2 106 107 82 340 ≤ 700836655816004 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3049 c22240R_106_23 (by norm_num)

theorem c22240R_106_21 : rowsJ2 106 107 81 340 ≤ 701606842166116 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3048 c22240R_106_22 (by norm_num)

theorem c22240R_106_20 : rowsJ2 106 107 80 340 ≤ 702480021424670 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3047 c22240R_106_21 (by norm_num)

theorem c22240R_106_19 : rowsJ2 106 107 78 340 ≤ 703393760681752 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3046 c22240R_106_20 (by norm_num)

theorem c22240R_106_18 : rowsJ2 106 107 75 340 ≤ 703612754015735 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3045 c22240R_106_19 (by norm_num)

theorem c22240R_106_17 : rowsJ2 106 107 71 340 ≤ 703612754015735 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3044 c22240R_106_18 (by norm_num)

theorem c22240R_106_16 : rowsJ2 106 107 65 340 ≤ 703612754015735 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3043 c22240R_106_17 (by norm_num)

theorem c22240R_106_15 : rowsJ2 106 107 56 340 ≤ 703790580688319 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3042 c22240R_106_16 (by norm_num)

theorem c22240R_106_14 : rowsJ2 106 107 51 340 ≤ 704167737336591 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3041 c22240R_106_15 (by norm_num)

theorem c22240R_106_13 : rowsJ2 106 107 48 340 ≤ 707422567654193 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3040 c22240R_106_14 (by norm_num)

theorem c22240R_106_12 : rowsJ2 106 107 46 340 ≤ 713471271876286 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3039 c22240R_106_13 (by norm_num)

theorem c22240R_106_11 : rowsJ2 106 107 44 340 ≤ 723980084371291 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3038 c22240R_106_12 (by norm_num)

theorem c22240R_106_10 : rowsJ2 106 107 42 340 ≤ 739632031238535 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3037 c22240R_106_11 (by norm_num)

theorem c22240R_106_9 : rowsJ2 106 107 41 340 ≤ 749705342211260 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3036 c22240R_106_10 (by norm_num)

theorem c22240R_106_8 : rowsJ2 106 107 40 340 ≤ 761536584832083 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3035 c22240R_106_9 (by norm_num)

theorem c22240R_106_7 : rowsJ2 106 107 39 340 ≤ 775326518022956 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3034 c22240R_106_8 (by norm_num)

theorem c22240R_106_6 : rowsJ2 106 107 38 340 ≤ 791281311409332 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3033 c22240R_106_7 (by norm_num)

theorem c22240R_106_5 : rowsJ2 106 107 37 340 ≤ 805400996125314 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3032 c22240R_106_6 (by norm_num)

theorem c22240R_106_4 : rowsJ2 106 107 36 340 ≤ 817117844836801 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3031 c22240R_106_5 (by norm_num)

theorem c22240R_106_3 : rowsJ2 106 107 34 340 ≤ 834745504745590 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3030 c22240R_106_4 (by norm_num)

theorem c22240R_106_2 : rowsJ2 106 107 31 340 ≤ 848100035840185 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3029 c22240R_106_3 (by norm_num)

theorem c22240R_106_1 : rowsJ2 106 107 20 340 ≤ 851296543696098 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3028 c22240R_106_2 (by norm_num)

theorem c22240R_106_0 : rowsJ2 106 107 0 340 ≤ 851296543696098 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22240R_3027 c22240R_106_1 (by norm_num)

theorem hr22240R_106 : rows2 106 107 ≤ 851296543696098 := rows2_le_of_rowsJ2 106 107 c22240R_106_0

theorem c22240R_107_33 : rowsJ2 107 108 100 340 ≤ 720758834464609 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3097 rows22240R_3098 (by norm_num)

theorem c22240R_107_32 : rowsJ2 107 108 99 340 ≤ 733460303130544 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3096 c22240R_107_33 (by norm_num)

theorem c22240R_107_31 : rowsJ2 107 108 98 340 ≤ 744745786854302 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3095 c22240R_107_32 (by norm_num)

theorem c22240R_107_30 : rowsJ2 107 108 97 340 ≤ 754688279001312 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3094 c22240R_107_31 (by norm_num)

theorem c22240R_107_29 : rowsJ2 107 108 96 340 ≤ 763409771882967 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3093 c22240R_107_30 (by norm_num)

theorem c22240R_107_28 : rowsJ2 107 108 95 340 ≤ 770977395751437 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3092 c22240R_107_29 (by norm_num)

theorem c22240R_107_27 : rowsJ2 107 108 94 340 ≤ 777506395892136 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3091 c22240R_107_28 (by norm_num)

theorem c22240R_107_26 : rowsJ2 107 108 93 340 ≤ 783058836227228 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3090 c22240R_107_27 (by norm_num)

theorem c22240R_107_25 : rowsJ2 107 108 91 340 ≤ 791665766714394 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3089 c22240R_107_26 (by norm_num)

theorem c22240R_107_24 : rowsJ2 107 108 89 340 ≤ 797504892624191 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3088 c22240R_107_25 (by norm_num)

theorem c22240R_107_23 : rowsJ2 107 108 87 340 ≤ 801245601068460 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3087 c22240R_107_24 (by norm_num)

theorem c22240R_107_22 : rowsJ2 107 108 85 340 ≤ 803524733075570 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3086 c22240R_107_23 (by norm_num)

theorem c22240R_107_21 : rowsJ2 107 108 83 340 ≤ 804951044498108 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3085 c22240R_107_22 (by norm_num)

theorem c22240R_107_20 : rowsJ2 107 108 81 340 ≤ 806110926091587 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3084 c22240R_107_21 (by norm_num)

theorem c22240R_107_19 : rowsJ2 107 108 80 340 ≤ 806776511723130 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3083 c22240R_107_20 (by norm_num)

theorem c22240R_107_18 : rowsJ2 107 108 78 340 ≤ 807682564927500 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3082 c22240R_107_19 (by norm_num)

theorem c22240R_107_17 : rowsJ2 107 108 75 340 ≤ 807899496944546 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3081 c22240R_107_18 (by norm_num)

theorem c22240R_107_16 : rowsJ2 107 108 71 340 ≤ 807899496944546 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3080 c22240R_107_17 (by norm_num)

theorem c22240R_107_15 : rowsJ2 107 108 64 340 ≤ 807899496944546 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3079 c22240R_107_16 (by norm_num)

theorem c22240R_107_14 : rowsJ2 107 108 55 340 ≤ 808333071251009 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3078 c22240R_107_15 (by norm_num)

theorem c22240R_107_13 : rowsJ2 107 108 50 340 ≤ 808711640448475 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3077 c22240R_107_14 (by norm_num)

theorem c22240R_107_12 : rowsJ2 107 108 47 340 ≤ 812577737960953 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3076 c22240R_107_13 (by norm_num)

theorem c22240R_107_11 : rowsJ2 107 108 45 340 ≤ 819479527668476 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3075 c22240R_107_12 (by norm_num)

theorem c22240R_107_10 : rowsJ2 107 108 43 340 ≤ 830881371149033 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3074 c22240R_107_11 (by norm_num)

theorem c22240R_107_9 : rowsJ2 107 108 41 340 ≤ 847580318948385 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3073 c22240R_107_10 (by norm_num)

theorem c22240R_107_8 : rowsJ2 107 108 40 340 ≤ 858363189616957 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3072 c22240R_107_9 (by norm_num)

theorem c22240R_107_7 : rowsJ2 107 108 39 340 ≤ 871036344752435 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3071 c22240R_107_8 (by norm_num)

theorem c22240R_107_6 : rowsJ2 107 108 38 340 ≤ 885807286777247 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3070 c22240R_107_7 (by norm_num)

theorem c22240R_107_5 : rowsJ2 107 108 37 340 ≤ 900754833815318 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3069 c22240R_107_6 (by norm_num)

theorem c22240R_107_4 : rowsJ2 107 108 36 340 ≤ 913078019105897 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3068 c22240R_107_5 (by norm_num)

theorem c22240R_107_3 : rowsJ2 107 108 34 340 ≤ 931614937415570 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3067 c22240R_107_4 (by norm_num)

theorem c22240R_107_2 : rowsJ2 107 108 31 340 ≤ 946131322791212 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3066 c22240R_107_3 (by norm_num)

theorem c22240R_107_1 : rowsJ2 107 108 21 340 ≤ 950207493297340 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3065 c22240R_107_2 (by norm_num)

theorem c22240R_107_0 : rowsJ2 107 108 0 340 ≤ 950207493297340 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22240R_3064 c22240R_107_1 (by norm_num)

theorem hr22240R_107 : rows2 107 108 ≤ 950207493297340 := rows2_le_of_rowsJ2 107 108 c22240R_107_0

theorem c22240R_108_31 : rowsJ2 108 109 99 340 ≤ 926174006579669 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3130 rows22240R_3131 (by norm_num)

theorem c22240R_108_30 : rowsJ2 108 109 98 340 ≤ 938102365636816 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3129 c22240R_108_31 (by norm_num)

theorem c22240R_108_29 : rowsJ2 108 109 97 340 ≤ 948659518339168 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3128 c22240R_108_30 (by norm_num)

theorem c22240R_108_28 : rowsJ2 108 109 96 340 ≤ 957917997279713 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3127 c22240R_108_29 (by norm_num)

theorem c22240R_108_27 : rowsJ2 108 109 95 340 ≤ 965999407098779 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3126 c22240R_108_28 (by norm_num)

theorem c22240R_108_26 : rowsJ2 108 109 94 340 ≤ 972970510058489 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3125 c22240R_108_27 (by norm_num)

theorem c22240R_108_25 : rowsJ2 108 109 93 340 ≤ 978946258028385 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3124 c22240R_108_26 (by norm_num)

theorem c22240R_108_24 : rowsJ2 108 109 91 340 ≤ 988206146521547 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3123 c22240R_108_25 (by norm_num)

theorem c22240R_108_23 : rowsJ2 108 109 89 340 ≤ 994489642447572 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3122 c22240R_108_24 (by norm_num)

theorem c22240R_108_22 : rowsJ2 108 109 87 340 ≤ 998483835030666 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3121 c22240R_108_23 (by norm_num)

theorem c22240R_108_21 : rowsJ2 108 109 85 340 ≤ 1000841558889263 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3120 c22240R_108_22 (by norm_num)

theorem c22240R_108_20 : rowsJ2 108 109 83 340 ≤ 1002185906150314 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3119 c22240R_108_21 (by norm_num)

theorem c22240R_108_19 : rowsJ2 108 109 81 340 ≤ 1003115153084237 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3118 c22240R_108_20 (by norm_num)

theorem c22240R_108_18 : rowsJ2 108 109 79 340 ≤ 1004165395789627 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3117 c22240R_108_19 (by norm_num)

theorem c22240R_108_17 : rowsJ2 108 109 77 340 ≤ 1004661705177001 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3116 c22240R_108_18 (by norm_num)

theorem c22240R_108_16 : rowsJ2 108 109 74 340 ≤ 1004715612892127 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3115 c22240R_108_17 (by norm_num)

theorem c22240R_108_15 : rowsJ2 108 109 70 340 ≤ 1004715612892127 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3114 c22240R_108_16 (by norm_num)

theorem c22240R_108_14 : rowsJ2 108 109 63 340 ≤ 1005100224176078 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3113 c22240R_108_15 (by norm_num)

theorem c22240R_108_13 : rowsJ2 108 109 54 340 ≤ 1005689350910754 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3112 c22240R_108_14 (by norm_num)

theorem c22240R_108_12 : rowsJ2 108 109 49 340 ≤ 1006167396258284 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3111 c22240R_108_13 (by norm_num)

theorem c22240R_108_11 : rowsJ2 108 109 46 340 ≤ 1010968442696900 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3110 c22240R_108_12 (by norm_num)

theorem c22240R_108_10 : rowsJ2 108 109 44 340 ≤ 1018743104761018 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3109 c22240R_108_11 (by norm_num)

theorem c22240R_108_9 : rowsJ2 108 109 42 340 ≤ 1031059479093158 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3108 c22240R_108_10 (by norm_num)

theorem c22240R_108_8 : rowsJ2 108 109 40 340 ≤ 1049051179910016 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3107 c22240R_108_9 (by norm_num)

theorem c22240R_108_7 : rowsJ2 108 109 39 340 ≤ 1060676221502621 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3106 c22240R_108_8 (by norm_num)

theorem c22240R_108_6 : rowsJ2 108 109 38 340 ≤ 1074330939321818 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3105 c22240R_108_7 (by norm_num)

theorem c22240R_108_5 : rowsJ2 108 109 37 340 ≤ 1090107513732414 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3104 c22240R_108_6 (by norm_num)

theorem c22240R_108_4 : rowsJ2 108 109 36 340 ≤ 1103155812473179 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3103 c22240R_108_5 (by norm_num)

theorem c22240R_108_3 : rowsJ2 108 109 34 340 ≤ 1122600999379149 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3102 c22240R_108_4 (by norm_num)

theorem c22240R_108_2 : rowsJ2 108 109 31 340 ≤ 1138393151353012 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3101 c22240R_108_3 (by norm_num)

theorem c22240R_108_1 : rowsJ2 108 109 23 340 ≤ 1143351307090598 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3100 c22240R_108_2 (by norm_num)

theorem c22240R_108_0 : rowsJ2 108 109 0 340 ≤ 1143351307090598 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22240R_3099 c22240R_108_1 (by norm_num)

theorem hr22240R_108 : rows2 108 109 ≤ 1143351307090598 := rows2_le_of_rowsJ2 108 109 c22240R_108_0

theorem c22240R_109_31 : rowsJ2 109 110 99 340 ≤ 1017129784661619 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3163 rows22240R_3164 (by norm_num)

theorem c22240R_109_30 : rowsJ2 109 110 98 340 ≤ 1029731809394191 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3162 c22240R_109_31 (by norm_num)

theorem c22240R_109_29 : rowsJ2 109 110 97 340 ≤ 1040878996563971 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3161 c22240R_109_30 (by norm_num)

theorem c22240R_109_28 : rowsJ2 109 110 96 340 ≤ 1050700049984235 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3160 c22240R_109_29 (by norm_num)

theorem c22240R_109_27 : rowsJ2 109 110 95 340 ≤ 1059267054869797 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3159 c22240R_109_28 (by norm_num)

theorem c22240R_109_26 : rowsJ2 109 110 94 340 ≤ 1066701246679712 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3158 c22240R_109_27 (by norm_num)

theorem c22240R_109_25 : rowsJ2 109 110 92 340 ≤ 1078485093912822 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3157 c22240R_109_26 (by norm_num)

theorem c22240R_109_24 : rowsJ2 109 110 90 340 ≤ 1086755509360776 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3156 c22240R_109_25 (by norm_num)

theorem c22240R_109_23 : rowsJ2 109 110 88 340 ≤ 1092191382702184 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3155 c22240R_109_24 (by norm_num)

theorem c22240R_109_22 : rowsJ2 109 110 86 340 ≤ 1095479622247216 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3154 c22240R_109_23 (by norm_num)

theorem c22240R_109_21 : rowsJ2 109 110 84 340 ≤ 1097273504378601 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3153 c22240R_109_22 (by norm_num)

theorem c22240R_109_20 : rowsJ2 109 110 82 340 ≤ 1098197175508918 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3152 c22240R_109_21 (by norm_num)

theorem c22240R_109_19 : rowsJ2 109 110 80 340 ≤ 1098850573603753 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3151 c22240R_109_20 (by norm_num)

theorem c22240R_109_18 : rowsJ2 109 110 78 340 ≤ 1099583582852083 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3150 c22240R_109_19 (by norm_num)

theorem c22240R_109_17 : rowsJ2 109 110 76 340 ≤ 1099796582341242 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3149 c22240R_109_18 (by norm_num)

theorem c22240R_109_16 : rowsJ2 109 110 73 340 ≤ 1099796582341242 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3148 c22240R_109_17 (by norm_num)

theorem c22240R_109_15 : rowsJ2 109 110 68 340 ≤ 1099796582341242 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3147 c22240R_109_16 (by norm_num)

theorem c22240R_109_14 : rowsJ2 109 110 62 340 ≤ 1101005086645036 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3146 c22240R_109_15 (by norm_num)

theorem c22240R_109_13 : rowsJ2 109 110 53 340 ≤ 1101495236182580 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3145 c22240R_109_14 (by norm_num)

theorem c22240R_109_12 : rowsJ2 109 110 48 340 ≤ 1102275051853852 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3144 c22240R_109_13 (by norm_num)

theorem c22240R_109_11 : rowsJ2 109 110 45 340 ≤ 1108243306020875 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3143 c22240R_109_12 (by norm_num)

theorem c22240R_109_10 : rowsJ2 109 110 43 340 ≤ 1116911581698162 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3142 c22240R_109_11 (by norm_num)

theorem c22240R_109_9 : rowsJ2 109 110 41 340 ≤ 1130273972777441 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3141 c22240R_109_10 (by norm_num)

theorem c22240R_109_8 : rowsJ2 109 110 39 340 ≤ 1149818518959062 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3140 c22240R_109_9 (by norm_num)

theorem c22240R_109_7 : rowsJ2 109 110 38 340 ≤ 1162426173082807 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3139 c22240R_109_8 (by norm_num)

theorem c22240R_109_6 : rowsJ2 109 110 37 340 ≤ 1177087215567389 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3138 c22240R_109_7 (by norm_num)

theorem c22240R_109_5 : rowsJ2 109 110 36 340 ≤ 1190982547617856 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3137 c22240R_109_6 (by norm_num)

theorem c22240R_109_4 : rowsJ2 109 110 35 340 ≤ 1202278776461009 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3136 c22240R_109_5 (by norm_num)

theorem c22240R_109_3 : rowsJ2 109 110 33 340 ≤ 1218870446534446 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3135 c22240R_109_4 (by norm_num)

theorem c22240R_109_2 : rowsJ2 109 110 31 340 ≤ 1228523795006183 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3134 c22240R_109_3 (by norm_num)

theorem c22240R_109_1 : rowsJ2 109 110 24 340 ≤ 1234369790740323 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3133 c22240R_109_2 (by norm_num)

theorem c22240R_109_0 : rowsJ2 109 110 0 340 ≤ 1234369790740323 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22240R_3132 c22240R_109_1 (by norm_num)

theorem hr22240R_109 : rows2 109 110 ≤ 1234369790740323 := rows2_le_of_rowsJ2 109 110 c22240R_109_0

theorem c22240R_110_29 : rowsJ2 110 111 98 340 ≤ 1211295627348543 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3194 rows22240R_3195 (by norm_num)

theorem c22240R_110_28 : rowsJ2 110 111 97 340 ≤ 1223100887442344 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3193 c22240R_110_29 (by norm_num)

theorem c22240R_110_27 : rowsJ2 110 111 96 340 ≤ 1233497418902753 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3192 c22240R_110_28 (by norm_num)

theorem c22240R_110_26 : rowsJ2 110 111 95 340 ≤ 1242613477210967 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3191 c22240R_110_27 (by norm_num)

theorem c22240R_110_25 : rowsJ2 110 111 94 340 ≤ 1250520717762205 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3190 c22240R_110_26 (by norm_num)

theorem c22240R_110_24 : rowsJ2 110 111 93 340 ≤ 1257340029621988 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3189 c22240R_110_25 (by norm_num)

theorem c22240R_110_23 : rowsJ2 110 111 91 340 ≤ 1268027513610462 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3188 c22240R_110_24 (by norm_num)

theorem c22240R_110_22 : rowsJ2 110 111 89 340 ≤ 1275377862725165 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3187 c22240R_110_23 (by norm_num)

theorem c22240R_110_21 : rowsJ2 110 111 87 340 ≤ 1280053928984906 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3186 c22240R_110_22 (by norm_num)

theorem c22240R_110_20 : rowsJ2 110 111 85 340 ≤ 1282727593155952 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3185 c22240R_110_21 (by norm_num)

theorem c22240R_110_19 : rowsJ2 110 111 82 340 ≤ 1284402231896027 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3184 c22240R_110_20 (by norm_num)

theorem c22240R_110_18 : rowsJ2 110 111 80 340 ≤ 1284869808397542 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3183 c22240R_110_19 (by norm_num)

theorem c22240R_110_17 : rowsJ2 110 111 78 340 ≤ 1285465505007684 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3182 c22240R_110_18 (by norm_num)

theorem c22240R_110_16 : rowsJ2 110 111 75 340 ≤ 1285676570171362 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3181 c22240R_110_17 (by norm_num)

theorem c22240R_110_15 : rowsJ2 110 111 71 340 ≤ 1285676570171362 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3180 c22240R_110_16 (by norm_num)

theorem c22240R_110_14 : rowsJ2 110 111 66 340 ≤ 1285910780345557 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3179 c22240R_110_15 (by norm_num)

theorem c22240R_110_13 : rowsJ2 110 111 61 340 ≤ 1288180381983756 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3178 c22240R_110_14 (by norm_num)

theorem c22240R_110_12 : rowsJ2 110 111 52 340 ≤ 1288547533652777 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3177 c22240R_110_13 (by norm_num)

theorem c22240R_110_11 : rowsJ2 110 111 47 340 ≤ 1289942359888081 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3176 c22240R_110_12 (by norm_num)

theorem c22240R_110_10 : rowsJ2 110 111 44 340 ≤ 1297212727180892 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3175 c22240R_110_11 (by norm_num)

theorem c22240R_110_9 : rowsJ2 110 111 42 340 ≤ 1306796360728431 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3174 c22240R_110_10 (by norm_num)

theorem c22240R_110_8 : rowsJ2 110 111 40 340 ≤ 1321453479758579 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3173 c22240R_110_9 (by norm_num)

theorem c22240R_110_7 : rowsJ2 110 111 38 340 ≤ 1342826338360461 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3172 c22240R_110_8 (by norm_num)

theorem c22240R_110_6 : rowsJ2 110 111 37 340 ≤ 1356441532223216 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3171 c22240R_110_7 (by norm_num)

theorem c22240R_110_5 : rowsJ2 110 111 36 340 ≤ 1371185258032137 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3170 c22240R_110_6 (by norm_num)

theorem c22240R_110_4 : rowsJ2 110 111 35 340 ≤ 1383224185966590 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3169 c22240R_110_5 (by norm_num)

theorem c22240R_110_3 : rowsJ2 110 111 33 340 ≤ 1400751259719380 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3168 c22240R_110_4 (by norm_num)

theorem c22240R_110_2 : rowsJ2 110 111 31 340 ≤ 1411267383953533 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3167 c22240R_110_3 (by norm_num)

theorem c22240R_110_1 : rowsJ2 110 111 25 340 ≤ 1418001276910124 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3166 c22240R_110_2 (by norm_num)

theorem c22240R_110_0 : rowsJ2 110 111 0 340 ≤ 1418001276910124 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22240R_3165 c22240R_110_1 (by norm_num)

theorem hr22240R_110 : rows2 110 111 ≤ 1418001276910124 := rows2_le_of_rowsJ2 110 111 c22240R_110_0

theorem c22240R_111_27 : rowsJ2 111 112 98 340 ≤ 1293330076931236 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3223 rows22240R_3224 (by norm_num)

theorem c22240R_111_26 : rowsJ2 111 112 97 340 ≤ 1305769803892851 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3222 c22240R_111_27 (by norm_num)

theorem c22240R_111_25 : rowsJ2 111 112 96 340 ≤ 1316769620100422 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3221 c22240R_111_26 (by norm_num)

theorem c22240R_111_24 : rowsJ2 111 112 95 340 ≤ 1326407137599160 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3220 c22240R_111_25 (by norm_num)

theorem c22240R_111_23 : rowsJ2 111 112 94 340 ≤ 1334810182068149 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3219 c22240R_111_24 (by norm_num)

theorem c22240R_111_22 : rowsJ2 111 112 92 340 ≤ 1348247132854319 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3218 c22240R_111_23 (by norm_num)

theorem c22240R_111_21 : rowsJ2 111 112 90 340 ≤ 1357824852869551 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3217 c22240R_111_22 (by norm_num)

theorem c22240R_111_20 : rowsJ2 111 112 88 340 ≤ 1364243436098544 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3216 c22240R_111_21 (by norm_num)

theorem c22240R_111_19 : rowsJ2 111 112 86 340 ≤ 1368164610104742 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3215 c22240R_111_20 (by norm_num)

theorem c22240R_111_18 : rowsJ2 111 112 83 340 ≤ 1370766973266201 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3214 c22240R_111_19 (by norm_num)

theorem c22240R_111_17 : rowsJ2 111 112 80 340 ≤ 1371390793530879 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3213 c22240R_111_18 (by norm_num)

theorem c22240R_111_16 : rowsJ2 111 112 78 340 ≤ 1371759930317297 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3212 c22240R_111_17 (by norm_num)

theorem c22240R_111_15 : rowsJ2 111 112 75 340 ≤ 1371969133833598 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3211 c22240R_111_16 (by norm_num)

theorem c22240R_111_14 : rowsJ2 111 112 71 340 ≤ 1371969133833598 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3210 c22240R_111_15 (by norm_num)

theorem c22240R_111_13 : rowsJ2 111 112 66 340 ≤ 1372702111026217 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3209 c22240R_111_14 (by norm_num)

theorem c22240R_111_12 : rowsJ2 111 112 61 340 ≤ 1375756173765119 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3208 c22240R_111_13 (by norm_num)

theorem c22240R_111_11 : rowsJ2 111 112 51 340 ≤ 1376283400381261 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3207 c22240R_111_12 (by norm_num)

theorem c22240R_111_10 : rowsJ2 111 112 46 340 ≤ 1378316857611541 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3206 c22240R_111_11 (by norm_num)

theorem c22240R_111_9 : rowsJ2 111 112 43 340 ≤ 1386602831952505 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3205 c22240R_111_10 (by norm_num)

theorem c22240R_111_8 : rowsJ2 111 112 41 340 ≤ 1397017245984489 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3204 c22240R_111_9 (by norm_num)

theorem c22240R_111_7 : rowsJ2 111 112 39 340 ≤ 1413009650270544 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3203 c22240R_111_8 (by norm_num)

theorem c22240R_111_6 : rowsJ2 111 112 37 340 ≤ 1436150010409469 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3202 c22240R_111_7 (by norm_num)

theorem c22240R_111_5 : rowsJ2 111 112 36 340 ≤ 1449842547424772 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3201 c22240R_111_6 (by norm_num)

theorem c22240R_111_4 : rowsJ2 111 112 35 340 ≤ 1462747669377837 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3200 c22240R_111_5 (by norm_num)

theorem c22240R_111_3 : rowsJ2 111 112 33 340 ≤ 1481329784501124 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3199 c22240R_111_4 (by norm_num)

theorem c22240R_111_2 : rowsJ2 111 112 31 340 ≤ 1492710986673181 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3198 c22240R_111_3 (by norm_num)

theorem c22240R_111_1 : rowsJ2 111 112 26 340 ≤ 1500451238897392 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3197 c22240R_111_2 (by norm_num)

theorem c22240R_111_0 : rowsJ2 111 112 0 340 ≤ 1500451238897392 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22240R_3196 c22240R_111_1 (by norm_num)

theorem hr22240R_111 : rows2 111 112 ≤ 1500451238897392 := rows2_le_of_rowsJ2 111 112 c22240R_111_0

theorem c22240R_112_26 : rowsJ2 112 113 97 340 ≤ 1476658761492630 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3251 rows22240R_3252 (by norm_num)

theorem c22240R_112_25 : rowsJ2 112 113 96 340 ≤ 1488276578219028 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3250 c22240R_112_26 (by norm_num)

theorem c22240R_112_24 : rowsJ2 112 113 95 340 ≤ 1498502040356177 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3249 c22240R_112_25 (by norm_num)

theorem c22240R_112_23 : rowsJ2 112 113 94 340 ≤ 1507412260033901 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3248 c22240R_112_24 (by norm_num)

theorem c22240R_112_22 : rowsJ2 112 113 93 340 ≤ 1515134656043166 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3247 c22240R_112_23 (by norm_num)

theorem c22240R_112_21 : rowsJ2 112 113 91 340 ≤ 1527348763320644 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3246 c22240R_112_22 (by norm_num)

theorem c22240R_112_20 : rowsJ2 112 113 89 340 ≤ 1535886328589409 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3245 c22240R_112_21 (by norm_num)

theorem c22240R_112_19 : rowsJ2 112 113 87 340 ≤ 1541445790539526 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3244 c22240R_112_20 (by norm_num)

theorem c22240R_112_18 : rowsJ2 112 113 85 340 ≤ 1544687947598846 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3243 c22240R_112_19 (by norm_num)

theorem c22240R_112_17 : rowsJ2 112 113 82 340 ≤ 1546581097458176 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3242 c22240R_112_18 (by norm_num)

theorem c22240R_112_16 : rowsJ2 112 113 79 340 ≤ 1546879768588810 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3241 c22240R_112_17 (by norm_num)

theorem c22240R_112_15 : rowsJ2 112 113 76 340 ≤ 1547204975057141 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3240 c22240R_112_16 (by norm_num)

theorem c22240R_112_14 : rowsJ2 112 113 73 340 ≤ 1547204975057141 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3239 c22240R_112_15 (by norm_num)

theorem c22240R_112_13 : rowsJ2 112 113 69 340 ≤ 1547204975057141 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3238 c22240R_112_14 (by norm_num)

theorem c22240R_112_12 : rowsJ2 112 113 65 340 ≤ 1549643181567731 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3237 c22240R_112_13 (by norm_num)

theorem c22240R_112_11 : rowsJ2 112 113 60 340 ≤ 1553203889399848 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3236 c22240R_112_12 (by norm_num)

theorem c22240R_112_10 : rowsJ2 112 113 50 340 ≤ 1553580307838355 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3235 c22240R_112_11 (by norm_num)

theorem c22240R_112_9 : rowsJ2 112 113 45 340 ≤ 1556586799054633 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3234 c22240R_112_10 (by norm_num)

theorem c22240R_112_8 : rowsJ2 112 113 42 340 ≤ 1565913291121988 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3233 c22240R_112_9 (by norm_num)

theorem c22240R_112_7 : rowsJ2 112 113 40 340 ≤ 1577405097296550 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3232 c22240R_112_8 (by norm_num)

theorem c22240R_112_6 : rowsJ2 112 113 38 340 ≤ 1595006179533278 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3231 c22240R_112_7 (by norm_num)

theorem c22240R_112_5 : rowsJ2 112 113 36 340 ≤ 1619113524432159 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3230 c22240R_112_6 (by norm_num)

theorem c22240R_112_4 : rowsJ2 112 113 35 340 ≤ 1632886415065688 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3229 c22240R_112_5 (by norm_num)

theorem c22240R_112_3 : rowsJ2 112 113 33 340 ≤ 1652762652314122 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3228 c22240R_112_4 (by norm_num)

theorem c22240R_112_2 : rowsJ2 112 113 31 340 ≤ 1665010431799113 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3227 c22240R_112_3 (by norm_num)

theorem c22240R_112_1 : rowsJ2 112 113 26 340 ≤ 1673756472895441 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3226 c22240R_112_2 (by norm_num)

theorem c22240R_112_0 : rowsJ2 112 113 0 340 ≤ 1673756472895441 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22240R_3225 c22240R_112_1 (by norm_num)

theorem hr22240R_112 : rows2 112 113 ≤ 1673756472895441 := rows2_le_of_rowsJ2 112 113 c22240R_112_0

theorem c22240R_113_25 : rowsJ2 113 114 97 340 ≤ 1550003120595835 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3278 rows22240R_3279 (by norm_num)

theorem c22240R_113_24 : rowsJ2 113 114 96 340 ≤ 1562269229386565 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3277 c22240R_113_25 (by norm_num)

theorem c22240R_113_23 : rowsJ2 113 114 95 340 ≤ 1573055798318983 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3276 c22240R_113_24 (by norm_num)

theorem c22240R_113_22 : rowsJ2 113 114 94 340 ≤ 1582497923373569 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3275 c22240R_113_23 (by norm_num)

theorem c22240R_113_21 : rowsJ2 113 114 93 340 ≤ 1590672230781538 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3274 c22240R_113_22 (by norm_num)

theorem c22240R_113_20 : rowsJ2 113 114 91 340 ≤ 1603668946545162 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3273 c22240R_113_21 (by norm_num)

theorem c22240R_113_19 : rowsJ2 113 114 89 340 ≤ 1612809452109804 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3272 c22240R_113_20 (by norm_num)

theorem c22240R_113_18 : rowsJ2 113 114 87 340 ≤ 1618811288543722 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3271 c22240R_113_19 (by norm_num)

theorem c22240R_113_17 : rowsJ2 113 114 84 340 ≤ 1623408200042336 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3270 c22240R_113_18 (by norm_num)

theorem c22240R_113_16 : rowsJ2 113 114 81 340 ≤ 1624596578709239 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3269 c22240R_113_17 (by norm_num)

theorem c22240R_113_15 : rowsJ2 113 114 78 340 ≤ 1624688492620745 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3268 c22240R_113_16 (by norm_num)

theorem c22240R_113_14 : rowsJ2 113 114 75 340 ≤ 1624817375225514 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3267 c22240R_113_15 (by norm_num)

theorem c22240R_113_13 : rowsJ2 113 114 71 340 ≤ 1624817375225514 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3266 c22240R_113_14 (by norm_num)

theorem c22240R_113_12 : rowsJ2 113 114 67 340 ≤ 1626647543160487 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3265 c22240R_113_13 (by norm_num)

theorem c22240R_113_11 : rowsJ2 113 114 64 340 ≤ 1629813973021059 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3264 c22240R_113_12 (by norm_num)

theorem c22240R_113_10 : rowsJ2 113 114 60 340 ≤ 1633076653547721 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3263 c22240R_113_11 (by norm_num)

theorem c22240R_113_9 : rowsJ2 113 114 49 340 ≤ 1633617251669318 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3262 c22240R_113_10 (by norm_num)

theorem c22240R_113_8 : rowsJ2 113 114 44 340 ≤ 1637407698851726 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3261 c22240R_113_9 (by norm_num)

theorem c22240R_113_7 : rowsJ2 113 114 41 340 ≤ 1647577715715188 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3260 c22240R_113_8 (by norm_num)

theorem c22240R_113_6 : rowsJ2 113 114 39 340 ≤ 1660178427383740 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3259 c22240R_113_7 (by norm_num)

theorem c22240R_113_5 : rowsJ2 113 114 37 340 ≤ 1679316633518884 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3258 c22240R_113_6 (by norm_num)

theorem c22240R_113_4 : rowsJ2 113 114 35 340 ≤ 1703564718642009 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3257 c22240R_113_5 (by norm_num)

theorem c22240R_113_3 : rowsJ2 113 114 33 340 ≤ 1724980520420892 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3256 c22240R_113_4 (by norm_num)

theorem c22240R_113_2 : rowsJ2 113 114 31 340 ≤ 1738096683350155 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3255 c22240R_113_3 (by norm_num)

theorem c22240R_113_1 : rowsJ2 113 114 26 340 ≤ 1747969972894450 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3254 c22240R_113_2 (by norm_num)

theorem c22240R_113_0 : rowsJ2 113 114 0 340 ≤ 1747969972894450 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22240R_3253 c22240R_113_1 (by norm_num)

theorem hr22240R_113 : rows2 113 114 ≤ 1747969972894450 := rows2_le_of_rowsJ2 113 114 c22240R_113_0

theorem c22240R_114_24 : rowsJ2 114 115 96 340 ≤ 1722755469527435 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3304 rows22240R_3305 (by norm_num)

theorem c22240R_114_23 : rowsJ2 114 115 95 340 ≤ 1734172956724373 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3303 c22240R_114_24 (by norm_num)

theorem c22240R_114_22 : rowsJ2 114 115 94 340 ≤ 1744159962886631 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3302 c22240R_114_23 (by norm_num)

theorem c22240R_114_21 : rowsJ2 114 115 93 340 ≤ 1752851107819160 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3301 c22240R_114_22 (by norm_num)

theorem c22240R_114_20 : rowsJ2 114 115 91 340 ≤ 1766700958467677 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3300 c22240R_114_21 (by norm_num)

theorem c22240R_114_19 : rowsJ2 114 115 89 340 ≤ 1776508681953164 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3299 c22240R_114_20 (by norm_num)

theorem c22240R_114_18 : rowsJ2 114 115 87 340 ≤ 1783011891221828 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3298 c22240R_114_19 (by norm_num)

theorem c22240R_114_17 : rowsJ2 114 115 84 340 ≤ 1788076348672819 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3297 c22240R_114_18 (by norm_num)

theorem c22240R_114_16 : rowsJ2 114 115 81 340 ≤ 1789475177626655 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3296 c22240R_114_17 (by norm_num)

theorem c22240R_114_15 : rowsJ2 114 115 78 340 ≤ 1789488210483771 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3295 c22240R_114_16 (by norm_num)

theorem c22240R_114_14 : rowsJ2 114 115 75 340 ≤ 1789564954783059 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3294 c22240R_114_15 (by norm_num)

theorem c22240R_114_13 : rowsJ2 114 115 71 340 ≤ 1789564954783059 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3293 c22240R_114_14 (by norm_num)

theorem c22240R_114_12 : rowsJ2 114 115 68 340 ≤ 1791677527184341 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3292 c22240R_114_13 (by norm_num)

theorem c22240R_114_11 : rowsJ2 114 115 65 340 ≤ 1795474000759142 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3291 c22240R_114_12 (by norm_num)

theorem c22240R_114_10 : rowsJ2 114 115 62 340 ≤ 1799186567239152 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3290 c22240R_114_11 (by norm_num)

theorem c22240R_114_9 : rowsJ2 114 115 55 340 ≤ 1801586449870498 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3289 c22240R_114_10 (by norm_num)

theorem c22240R_114_8 : rowsJ2 114 115 46 340 ≤ 1802127378395001 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3288 c22240R_114_9 (by norm_num)

theorem c22240R_114_7 : rowsJ2 114 115 42 340 ≤ 1809146561399016 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3287 c22240R_114_8 (by norm_num)

theorem c22240R_114_6 : rowsJ2 114 115 39 340 ≤ 1823860829165082 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3286 c22240R_114_7 (by norm_num)

theorem c22240R_114_5 : rowsJ2 114 115 37 340 ≤ 1841110700927663 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3285 c22240R_114_6 (by norm_num)

theorem c22240R_114_4 : rowsJ2 114 115 35 340 ≤ 1863266116253070 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3284 c22240R_114_5 (by norm_num)

theorem c22240R_114_3 : rowsJ2 114 115 33 340 ≤ 1886230014053259 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3283 c22240R_114_4 (by norm_num)

theorem c22240R_114_2 : rowsJ2 114 115 31 340 ≤ 1900334328988741 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3282 c22240R_114_3 (by norm_num)

theorem c22240R_114_1 : rowsJ2 114 115 27 340 ≤ 1910747373332128 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3281 c22240R_114_2 (by norm_num)

theorem c22240R_114_0 : rowsJ2 114 115 0 340 ≤ 1911451895037239 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22240R_3280 c22240R_114_1 (by norm_num)

theorem hr22240R_114 : rows2 114 115 ≤ 1911451895037239 := rows2_le_of_rowsJ2 114 115 c22240R_114_0

theorem c22240R_115_25 : rowsJ2 115 116 96 340 ≤ 1578401392866752 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3331 rows22240R_3332 (by norm_num)

theorem c22240R_115_24 : rowsJ2 115 116 95 340 ≤ 1590423908570495 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3330 c22240R_115_25 (by norm_num)

theorem c22240R_115_23 : rowsJ2 115 116 94 340 ≤ 1600982738487229 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3329 c22240R_115_24 (by norm_num)

theorem c22240R_115_22 : rowsJ2 115 116 93 340 ≤ 1610160531281227 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3328 c22240R_115_23 (by norm_num)

theorem c22240R_115_21 : rowsJ2 115 116 91 340 ≤ 1624851200741275 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3327 c22240R_115_22 (by norm_num)

theorem c22240R_115_20 : rowsJ2 115 116 89 340 ≤ 1635305923520445 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3326 c22240R_115_21 (by norm_num)

theorem c22240R_115_19 : rowsJ2 115 116 87 340 ≤ 1642283379178510 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3325 c22240R_115_20 (by norm_num)

theorem c22240R_115_18 : rowsJ2 115 116 84 340 ≤ 1647787791525266 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3324 c22240R_115_19 (by norm_num)

theorem c22240R_115_17 : rowsJ2 115 116 81 340 ≤ 1649309768310854 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3323 c22240R_115_18 (by norm_num)

theorem c22240R_115_16 : rowsJ2 115 116 78 340 ≤ 1649309768310854 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3322 c22240R_115_17 (by norm_num)

theorem c22240R_115_15 : rowsJ2 115 116 75 340 ≤ 1649322473320927 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3321 c22240R_115_16 (by norm_num)

theorem c22240R_115_14 : rowsJ2 115 116 72 340 ≤ 1649322473320927 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3320 c22240R_115_15 (by norm_num)

theorem c22240R_115_13 : rowsJ2 115 116 69 340 ≤ 1651673212225825 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3319 c22240R_115_14 (by norm_num)

theorem c22240R_115_12 : rowsJ2 115 116 67 340 ≤ 1654497881733532 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3318 c22240R_115_13 (by norm_num)

theorem c22240R_115_11 : rowsJ2 115 116 65 340 ≤ 1657692930367773 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3317 c22240R_115_12 (by norm_num)

theorem c22240R_115_10 : rowsJ2 115 116 63 340 ≤ 1660738950327973 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3316 c22240R_115_11 (by norm_num)

theorem c22240R_115_9 : rowsJ2 115 116 58 340 ≤ 1664804845226845 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3315 c22240R_115_10 (by norm_num)

theorem c22240R_115_8 : rowsJ2 115 116 47 340 ≤ 1665029221449769 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3314 c22240R_115_9 (by norm_num)

theorem c22240R_115_7 : rowsJ2 115 116 42 340 ≤ 1670437840259132 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3313 c22240R_115_8 (by norm_num)

theorem c22240R_115_6 : rowsJ2 115 116 39 340 ≤ 1682820870880472 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3312 c22240R_115_7 (by norm_num)

theorem c22240R_115_5 : rowsJ2 115 116 37 340 ≤ 1698098771573168 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3311 c22240R_115_6 (by norm_num)

theorem c22240R_115_4 : rowsJ2 115 116 35 340 ≤ 1718194304116640 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3310 c22240R_115_5 (by norm_num)

theorem c22240R_115_3 : rowsJ2 115 116 33 340 ≤ 1740912282672272 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3309 c22240R_115_4 (by norm_num)

theorem c22240R_115_2 : rowsJ2 115 116 31 340 ≤ 1756127805786057 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3308 c22240R_115_3 (by norm_num)

theorem c22240R_115_1 : rowsJ2 115 116 27 340 ≤ 1767669926245924 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3307 c22240R_115_2 (by norm_num)

theorem c22240R_115_0 : rowsJ2 115 116 0 340 ≤ 1768613411889424 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22240R_3306 c22240R_115_1 (by norm_num)

theorem hr22240R_115 : rows2 115 116 ≤ 1768613411889424 := rows2_le_of_rowsJ2 115 116 c22240R_115_0

theorem c22240R_116_23 : rowsJ2 116 117 95 340 ≤ 1568060899109769 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3356 rows22240R_3357 (by norm_num)

theorem c22240R_116_22 : rowsJ2 116 117 94 340 ≤ 1579206358433082 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3355 c22240R_116_23 (by norm_num)

theorem c22240R_116_21 : rowsJ2 116 117 92 340 ≤ 1597340440295359 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3354 c22240R_116_22 (by norm_num)

theorem c22240R_116_20 : rowsJ2 116 117 90 340 ≤ 1610627474621769 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3353 c22240R_116_21 (by norm_num)

theorem c22240R_116_19 : rowsJ2 116 117 88 340 ≤ 1619874457772888 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3352 c22240R_116_20 (by norm_num)

theorem c22240R_116_18 : rowsJ2 116 117 85 340 ≤ 1627818957783888 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3351 c22240R_116_19 (by norm_num)

theorem c22240R_116_17 : rowsJ2 116 117 82 340 ≤ 1630728837915141 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3350 c22240R_116_18 (by norm_num)

theorem c22240R_116_16 : rowsJ2 116 117 79 340 ≤ 1630975463324947 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3349 c22240R_116_17 (by norm_num)

theorem c22240R_116_15 : rowsJ2 116 117 76 340 ≤ 1630975463324947 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3348 c22240R_116_16 (by norm_num)

theorem c22240R_116_14 : rowsJ2 116 117 73 340 ≤ 1630975463324947 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3347 c22240R_116_15 (by norm_num)

theorem c22240R_116_13 : rowsJ2 116 117 70 340 ≤ 1633621097516884 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3346 c22240R_116_14 (by norm_num)

theorem c22240R_116_12 : rowsJ2 116 117 68 340 ≤ 1636847505570962 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3345 c22240R_116_13 (by norm_num)

theorem c22240R_116_11 : rowsJ2 116 117 66 340 ≤ 1640600080729107 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3344 c22240R_116_12 (by norm_num)

theorem c22240R_116_10 : rowsJ2 116 117 64 340 ≤ 1644352474854488 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3343 c22240R_116_11 (by norm_num)

theorem c22240R_116_9 : rowsJ2 116 117 61 340 ≤ 1648868343258292 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3342 c22240R_116_10 (by norm_num)

theorem c22240R_116_8 : rowsJ2 116 117 53 340 ≤ 1651354478342527 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3341 c22240R_116_9 (by norm_num)

theorem c22240R_116_7 : rowsJ2 116 117 44 340 ≤ 1652469260992235 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3340 c22240R_116_8 (by norm_num)

theorem c22240R_116_6 : rowsJ2 116 117 40 340 ≤ 1660965201435050 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3339 c22240R_116_7 (by norm_num)

theorem c22240R_116_5 : rowsJ2 116 117 37 340 ≤ 1678991035302725 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3338 c22240R_116_6 (by norm_num)

theorem c22240R_116_4 : rowsJ2 116 117 35 340 ≤ 1697060296880190 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3337 c22240R_116_5 (by norm_num)

theorem c22240R_116_3 : rowsJ2 116 117 33 340 ≤ 1719489594217760 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3336 c22240R_116_4 (by norm_num)

theorem c22240R_116_2 : rowsJ2 116 117 31 340 ≤ 1735943798738896 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3335 c22240R_116_3 (by norm_num)

theorem c22240R_116_1 : rowsJ2 116 117 27 340 ≤ 1748856628368740 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3334 c22240R_116_2 (by norm_num)

theorem c22240R_116_0 : rowsJ2 116 117 0 340 ≤ 1749916925997280 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22240R_3333 c22240R_116_1 (by norm_num)

theorem hr22240R_116 : rows2 116 117 ≤ 1749916925997280 := rows2_le_of_rowsJ2 116 117 c22240R_116_0

theorem c22240R_117_24 : rowsJ2 117 118 95 340 ≤ 1457452682016271 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3382 rows22240R_3383 (by norm_num)

theorem c22240R_117_23 : rowsJ2 117 118 94 340 ≤ 1469214201054317 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3381 c22240R_117_24 (by norm_num)

theorem c22240R_117_22 : rowsJ2 117 118 92 340 ≤ 1488367592071689 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3380 c22240R_117_23 (by norm_num)

theorem c22240R_117_21 : rowsJ2 117 118 90 340 ≤ 1502451606082767 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3379 c22240R_117_22 (by norm_num)

theorem c22240R_117_20 : rowsJ2 117 118 88 340 ≤ 1512298045232596 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3378 c22240R_117_21 (by norm_num)

theorem c22240R_117_19 : rowsJ2 117 118 85 340 ≤ 1520805910123658 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3377 c22240R_117_20 (by norm_num)

theorem c22240R_117_18 : rowsJ2 117 118 82 340 ≤ 1523972397696418 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3376 c22240R_117_19 (by norm_num)

theorem c22240R_117_17 : rowsJ2 117 118 79 340 ≤ 1524223958768267 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3375 c22240R_117_18 (by norm_num)

theorem c22240R_117_16 : rowsJ2 117 118 76 340 ≤ 1524223958768267 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3374 c22240R_117_17 (by norm_num)

theorem c22240R_117_15 : rowsJ2 117 118 73 340 ≤ 1524754102908970 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3373 c22240R_117_16 (by norm_num)

theorem c22240R_117_14 : rowsJ2 117 118 71 340 ≤ 1527121451648923 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3372 c22240R_117_15 (by norm_num)

theorem c22240R_117_13 : rowsJ2 117 118 69 340 ≤ 1530733074191373 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3371 c22240R_117_14 (by norm_num)

theorem c22240R_117_12 : rowsJ2 117 118 67 340 ≤ 1535028530758714 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3370 c22240R_117_13 (by norm_num)

theorem c22240R_117_11 : rowsJ2 117 118 65 340 ≤ 1539473471071414 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3369 c22240R_117_12 (by norm_num)

theorem c22240R_117_10 : rowsJ2 117 118 63 340 ≤ 1543553254074635 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3368 c22240R_117_11 (by norm_num)

theorem c22240R_117_9 : rowsJ2 117 118 61 340 ≤ 1546768249155544 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3367 c22240R_117_10 (by norm_num)

theorem c22240R_117_8 : rowsJ2 117 118 52 340 ≤ 1549848302367664 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3366 c22240R_117_9 (by norm_num)

theorem c22240R_117_7 : rowsJ2 117 118 43 340 ≤ 1550968564643803 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3365 c22240R_117_8 (by norm_num)

theorem c22240R_117_6 : rowsJ2 117 118 39 340 ≤ 1560220980344101 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3364 c22240R_117_7 (by norm_num)

theorem c22240R_117_5 : rowsJ2 117 118 36 340 ≤ 1579337839212936 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3363 c22240R_117_6 (by norm_num)

theorem c22240R_117_4 : rowsJ2 117 118 34 340 ≤ 1597518108129045 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3362 c22240R_117_5 (by norm_num)

theorem c22240R_117_3 : rowsJ2 117 118 32 340 ≤ 1618316168932690 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3361 c22240R_117_4 (by norm_num)

theorem c22240R_117_2 : rowsJ2 117 118 30 340 ≤ 1631947060920698 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3360 c22240R_117_3 (by norm_num)

theorem c22240R_117_1 : rowsJ2 117 118 27 340 ≤ 1640582191133587 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3359 c22240R_117_2 (by norm_num)

theorem c22240R_117_0 : rowsJ2 117 118 0 340 ≤ 1641759598293693 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22240R_3358 c22240R_117_1 (by norm_num)

theorem hr22240R_117 : rows2 117 118 ≤ 1641759598293693 := rows2_le_of_rowsJ2 117 118 c22240R_117_0

theorem c22240R_118_23 : rowsJ2 118 119 93 340 ≤ 1458808086428049 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3407 rows22240R_3408 (by norm_num)

theorem c22240R_118_22 : rowsJ2 118 119 91 340 ≤ 1476303599967027 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3406 c22240R_118_23 (by norm_num)

theorem c22240R_118_21 : rowsJ2 118 119 89 340 ≤ 1488935392904180 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3405 c22240R_118_22 (by norm_num)

theorem c22240R_118_20 : rowsJ2 118 119 87 340 ≤ 1497532136113469 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3404 c22240R_118_21 (by norm_num)

theorem c22240R_118_19 : rowsJ2 118 119 84 340 ≤ 1504540560369396 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3403 c22240R_118_20 (by norm_num)

theorem c22240R_118_18 : rowsJ2 118 119 81 340 ≤ 1506654625587842 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3402 c22240R_118_19 (by norm_num)

theorem c22240R_118_17 : rowsJ2 118 119 78 340 ≤ 1506654625587842 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3401 c22240R_118_18 (by norm_num)

theorem c22240R_118_16 : rowsJ2 118 119 75 340 ≤ 1506654625587842 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3400 c22240R_118_17 (by norm_num)

theorem c22240R_118_15 : rowsJ2 118 119 73 340 ≤ 1508336833195256 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3399 c22240R_118_16 (by norm_num)

theorem c22240R_118_14 : rowsJ2 118 119 71 340 ≤ 1511734754358236 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3398 c22240R_118_15 (by norm_num)

theorem c22240R_118_13 : rowsJ2 118 119 69 340 ≤ 1516259365577893 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3397 c22240R_118_14 (by norm_num)

theorem c22240R_118_12 : rowsJ2 118 119 67 340 ≤ 1521353643938878 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3396 c22240R_118_13 (by norm_num)

theorem c22240R_118_11 : rowsJ2 118 119 65 340 ≤ 1526486165789129 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3395 c22240R_118_12 (by norm_num)

theorem c22240R_118_10 : rowsJ2 118 119 63 340 ≤ 1531144734221890 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3394 c22240R_118_11 (by norm_num)

theorem c22240R_118_9 : rowsJ2 118 119 61 340 ≤ 1534831867230039 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3393 c22240R_118_10 (by norm_num)

theorem c22240R_118_8 : rowsJ2 118 119 57 340 ≤ 1538307113911496 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3392 c22240R_118_9 (by norm_num)

theorem c22240R_118_7 : rowsJ2 118 119 44 340 ≤ 1538827851137104 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3391 c22240R_118_8 (by norm_num)

theorem c22240R_118_6 : rowsJ2 118 119 39 340 ≤ 1546096469623014 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3390 c22240R_118_7 (by norm_num)

theorem c22240R_118_5 : rowsJ2 118 119 36 340 ≤ 1562500717205776 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3389 c22240R_118_6 (by norm_num)

theorem c22240R_118_4 : rowsJ2 118 119 34 340 ≤ 1578680162019286 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3388 c22240R_118_5 (by norm_num)

theorem c22240R_118_3 : rowsJ2 118 119 32 340 ≤ 1599157711568235 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3387 c22240R_118_4 (by norm_num)

theorem c22240R_118_2 : rowsJ2 118 119 30 340 ≤ 1613937482316049 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3386 c22240R_118_3 (by norm_num)

theorem c22240R_118_1 : rowsJ2 118 119 27 340 ≤ 1623863959646797 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3385 c22240R_118_2 (by norm_num)

theorem c22240R_118_0 : rowsJ2 118 119 0 340 ≤ 1625153742518353 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22240R_3384 c22240R_118_1 (by norm_num)

theorem hr22240R_118 : rows2 118 119 ≤ 1625153742518353 := rows2_le_of_rowsJ2 118 119 c22240R_118_0

theorem c22240R_119_26 : rowsJ2 119 120 93 340 ≤ 1351556607388352 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3435 rows22240R_3436 (by norm_num)

theorem c22240R_119_25 : rowsJ2 119 120 91 340 ≤ 1370028690458692 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3434 c22240R_119_26 (by norm_num)

theorem c22240R_119_24 : rowsJ2 119 120 89 340 ≤ 1383409961924339 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3433 c22240R_119_25 (by norm_num)

theorem c22240R_119_23 : rowsJ2 119 120 87 340 ≤ 1392554918325745 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3432 c22240R_119_24 (by norm_num)

theorem c22240R_119_22 : rowsJ2 119 120 84 340 ≤ 1400070174022214 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3431 c22240R_119_23 (by norm_num)

theorem c22240R_119_21 : rowsJ2 119 120 81 340 ≤ 1402329192677665 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3430 c22240R_119_22 (by norm_num)

theorem c22240R_119_20 : rowsJ2 119 120 78 340 ≤ 1402329192677665 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3429 c22240R_119_21 (by norm_num)

theorem c22240R_119_19 : rowsJ2 119 120 75 340 ≤ 1402860615353315 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3428 c22240R_119_20 (by norm_num)

theorem c22240R_119_18 : rowsJ2 119 120 73 340 ≤ 1405641736814051 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3427 c22240R_119_19 (by norm_num)

theorem c22240R_119_17 : rowsJ2 119 120 71 340 ≤ 1410080829028410 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3426 c22240R_119_18 (by norm_num)

theorem c22240R_119_16 : rowsJ2 119 120 70 340 ≤ 1412716559017312 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3425 c22240R_119_17 (by norm_num)

theorem c22240R_119_15 : rowsJ2 119 120 69 340 ≤ 1415527757003480 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3424 c22240R_119_16 (by norm_num)

theorem c22240R_119_14 : rowsJ2 119 120 68 340 ≤ 1418458065086994 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3423 c22240R_119_15 (by norm_num)

theorem c22240R_119_13 : rowsJ2 119 120 67 340 ≤ 1421428947820016 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3422 c22240R_119_14 (by norm_num)

theorem c22240R_119_12 : rowsJ2 119 120 66 340 ≤ 1424386866632521 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3421 c22240R_119_13 (by norm_num)

theorem c22240R_119_11 : rowsJ2 119 120 65 340 ≤ 1427255926685619 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3420 c22240R_119_12 (by norm_num)

theorem c22240R_119_10 : rowsJ2 119 120 64 340 ≤ 1429984582085070 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3419 c22240R_119_11 (by norm_num)

theorem c22240R_119_9 : rowsJ2 119 120 62 340 ≤ 1434749110253950 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3418 c22240R_119_10 (by norm_num)

theorem c22240R_119_8 : rowsJ2 119 120 60 340 ≤ 1438191072704820 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3417 c22240R_119_9 (by norm_num)

theorem c22240R_119_7 : rowsJ2 119 120 50 340 ≤ 1441353736758442 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3416 c22240R_119_8 (by norm_num)

theorem c22240R_119_6 : rowsJ2 119 120 41 340 ≤ 1442602883658485 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3415 c22240R_119_7 (by norm_num)

theorem c22240R_119_5 : rowsJ2 119 120 37 340 ≤ 1454785164839299 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3414 c22240R_119_6 (by norm_num)

theorem c22240R_119_4 : rowsJ2 119 120 34 340 ≤ 1474637769572460 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3413 c22240R_119_5 (by norm_num)

theorem c22240R_119_3 : rowsJ2 119 120 32 340 ≤ 1493052625702214 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3412 c22240R_119_4 (by norm_num)

theorem c22240R_119_2 : rowsJ2 119 120 30 340 ≤ 1509114044776726 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3411 c22240R_119_3 (by norm_num)

theorem c22240R_119_1 : rowsJ2 119 120 27 340 ≤ 1520340615635642 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3410 c22240R_119_2 (by norm_num)

theorem c22240R_119_0 : rowsJ2 119 120 0 340 ≤ 1521865368136331 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22240R_3409 c22240R_119_1 (by norm_num)

theorem hr22240R_119 : rows2 119 120 ≤ 1521865368136331 := rows2_le_of_rowsJ2 119 120 c22240R_119_0

theorem c22240R_120_26 : rowsJ2 120 121 92 340 ≤ 1341939209957719 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3463 rows22240R_3464 (by norm_num)

theorem c22240R_120_25 : rowsJ2 120 121 90 340 ≤ 1358694483354715 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3462 c22240R_120_26 (by norm_num)

theorem c22240R_120_24 : rowsJ2 120 121 88 340 ≤ 1370571792611817 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3461 c22240R_120_25 (by norm_num)

theorem c22240R_120_23 : rowsJ2 120 121 85 340 ≤ 1381095128223935 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3460 c22240R_120_24 (by norm_num)

theorem c22240R_120_22 : rowsJ2 120 121 82 340 ≤ 1385183000059460 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3459 c22240R_120_23 (by norm_num)

theorem c22240R_120_21 : rowsJ2 120 121 78 340 ≤ 1385552429436715 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3458 c22240R_120_22 (by norm_num)

theorem c22240R_120_20 : rowsJ2 120 121 75 340 ≤ 1387079716412924 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3457 c22240R_120_21 (by norm_num)

theorem c22240R_120_19 : rowsJ2 120 121 73 340 ≤ 1390958610991064 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3456 c22240R_120_20 (by norm_num)

theorem c22240R_120_18 : rowsJ2 120 121 72 340 ≤ 1393586704107587 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3455 c22240R_120_19 (by norm_num)

theorem c22240R_120_17 : rowsJ2 120 121 71 340 ≤ 1396501939951091 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3454 c22240R_120_18 (by norm_num)

theorem c22240R_120_16 : rowsJ2 120 121 70 340 ≤ 1399644792524232 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3453 c22240R_120_17 (by norm_num)

theorem c22240R_120_15 : rowsJ2 120 121 69 340 ≤ 1402933779472038 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3452 c22240R_120_16 (by norm_num)

theorem c22240R_120_14 : rowsJ2 120 121 68 340 ≤ 1406312895552221 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3451 c22240R_120_15 (by norm_num)

theorem c22240R_120_13 : rowsJ2 120 121 67 340 ≤ 1409704072134402 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3450 c22240R_120_14 (by norm_num)

theorem c22240R_120_12 : rowsJ2 120 121 66 340 ≤ 1413054055643959 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3449 c22240R_120_13 (by norm_num)

theorem c22240R_120_11 : rowsJ2 120 121 65 340 ≤ 1416287341287575 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3448 c22240R_120_12 (by norm_num)

theorem c22240R_120_10 : rowsJ2 120 121 64 340 ≤ 1419352623427427 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3447 c22240R_120_11 (by norm_num)

theorem c22240R_120_9 : rowsJ2 120 121 62 340 ≤ 1424708878077772 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3446 c22240R_120_10 (by norm_num)

theorem c22240R_120_8 : rowsJ2 120 121 60 340 ≤ 1428635519922776 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3445 c22240R_120_9 (by norm_num)

theorem c22240R_120_7 : rowsJ2 120 121 56 340 ≤ 1432204765815126 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3444 c22240R_120_8 (by norm_num)

theorem c22240R_120_6 : rowsJ2 120 121 42 340 ≤ 1432737948508113 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3443 c22240R_120_7 (by norm_num)

theorem c22240R_120_5 : rowsJ2 120 121 37 340 ≤ 1443056465281965 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3442 c22240R_120_6 (by norm_num)

theorem c22240R_120_4 : rowsJ2 120 121 34 340 ≤ 1460168828174538 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3441 c22240R_120_5 (by norm_num)

theorem c22240R_120_3 : rowsJ2 120 121 32 340 ≤ 1476558249973051 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3440 c22240R_120_4 (by norm_num)

theorem c22240R_120_2 : rowsJ2 120 121 30 340 ≤ 1493908182244297 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3439 c22240R_120_3 (by norm_num)

theorem c22240R_120_1 : rowsJ2 120 121 27 340 ≤ 1506439419700454 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3438 c22240R_120_2 (by norm_num)

theorem c22240R_120_0 : rowsJ2 120 121 0 340 ≤ 1508446305561340 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22240R_3437 c22240R_120_1 (by norm_num)

theorem hr22240R_120 : rows2 120 121 ≤ 1508446305561340 := rows2_le_of_rowsJ2 120 121 c22240R_120_0

theorem c22240R_121_27 : rowsJ2 121 122 93 340 ≤ 1226337774465427 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3492 rows22240R_3493 (by norm_num)

theorem c22240R_121_26 : rowsJ2 121 122 91 340 ≤ 1246926332688315 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3491 c22240R_121_27 (by norm_num)

theorem c22240R_121_25 : rowsJ2 121 122 89 340 ≤ 1261941457062041 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3490 c22240R_121_26 (by norm_num)

theorem c22240R_121_24 : rowsJ2 121 122 86 340 ≤ 1275995100212845 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3489 c22240R_121_25 (by norm_num)

theorem c22240R_121_23 : rowsJ2 121 122 83 340 ≤ 1282347842968307 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3488 c22240R_121_24 (by norm_num)

theorem c22240R_121_22 : rowsJ2 121 122 79 340 ≤ 1283592979989163 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3487 c22240R_121_23 (by norm_num)

theorem c22240R_121_21 : rowsJ2 121 122 76 340 ≤ 1284969872375555 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3486 c22240R_121_22 (by norm_num)

theorem c22240R_121_20 : rowsJ2 121 122 74 340 ≤ 1288506860361206 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3485 c22240R_121_21 (by norm_num)

theorem c22240R_121_19 : rowsJ2 121 122 73 340 ≤ 1291205385669669 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3484 c22240R_121_20 (by norm_num)

theorem c22240R_121_18 : rowsJ2 121 122 72 340 ≤ 1294407038212987 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3483 c22240R_121_19 (by norm_num)

theorem c22240R_121_17 : rowsJ2 121 122 71 340 ≤ 1297865200222943 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3482 c22240R_121_18 (by norm_num)

theorem c22240R_121_16 : rowsJ2 121 122 70 340 ≤ 1301520765728546 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3481 c22240R_121_17 (by norm_num)

theorem c22240R_121_15 : rowsJ2 121 122 69 340 ≤ 1305292783278900 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3480 c22240R_121_16 (by norm_num)

theorem c22240R_121_14 : rowsJ2 121 122 68 340 ≤ 1309125606395737 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3479 c22240R_121_15 (by norm_num)

theorem c22240R_121_13 : rowsJ2 121 122 67 340 ≤ 1312941637113343 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3478 c22240R_121_14 (by norm_num)

theorem c22240R_121_12 : rowsJ2 121 122 66 340 ≤ 1316687903340717 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3477 c22240R_121_13 (by norm_num)

theorem c22240R_121_11 : rowsJ2 121 122 65 340 ≤ 1320289304310925 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3476 c22240R_121_12 (by norm_num)

theorem c22240R_121_10 : rowsJ2 121 122 64 340 ≤ 1323694771192748 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3475 c22240R_121_11 (by norm_num)

theorem c22240R_121_9 : rowsJ2 121 122 63 340 ≤ 1326831159225051 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3474 c22240R_121_10 (by norm_num)

theorem c22240R_121_8 : rowsJ2 121 122 61 340 ≤ 1332076387030764 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3473 c22240R_121_9 (by norm_num)

theorem c22240R_121_7 : rowsJ2 121 122 59 340 ≤ 1335634928695484 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3472 c22240R_121_8 (by norm_num)

theorem c22240R_121_6 : rowsJ2 121 122 48 340 ≤ 1338884540182290 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3471 c22240R_121_7 (by norm_num)

theorem c22240R_121_5 : rowsJ2 121 122 39 340 ≤ 1341244346401098 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3470 c22240R_121_6 (by norm_num)

theorem c22240R_121_4 : rowsJ2 121 122 35 340 ≤ 1355980251279618 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3469 c22240R_121_5 (by norm_num)

theorem c22240R_121_3 : rowsJ2 121 122 32 340 ≤ 1376089306787300 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3468 c22240R_121_4 (by norm_num)

theorem c22240R_121_2 : rowsJ2 121 122 30 340 ≤ 1393093006800881 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3467 c22240R_121_3 (by norm_num)

theorem c22240R_121_1 : rowsJ2 121 122 26 340 ≤ 1408715692302411 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3466 c22240R_121_2 (by norm_num)

theorem c22240R_121_0 : rowsJ2 121 122 0 340 ≤ 1409553943049767 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22240R_3465 c22240R_121_1 (by norm_num)

theorem hr22240R_121 : rows2 121 122 ≤ 1409553943049767 := rows2_le_of_rowsJ2 121 122 c22240R_121_0

theorem c22240R_122_27 : rowsJ2 122 123 92 340 ≤ 1218431934977924 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3521 rows22240R_3522 (by norm_num)

theorem c22240R_122_26 : rowsJ2 122 123 90 340 ≤ 1237129003420744 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3520 c22240R_122_27 (by norm_num)

theorem c22240R_122_25 : rowsJ2 122 123 88 340 ≤ 1250475263943910 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3519 c22240R_122_26 (by norm_num)

theorem c22240R_122_24 : rowsJ2 122 123 85 340 ≤ 1262434681318610 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3518 c22240R_122_25 (by norm_num)

theorem c22240R_122_23 : rowsJ2 122 123 82 340 ≤ 1267176444742495 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3517 c22240R_122_24 (by norm_num)

theorem c22240R_122_22 : rowsJ2 122 123 78 340 ≤ 1268021066248004 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3516 c22240R_122_23 (by norm_num)

theorem c22240R_122_21 : rowsJ2 122 123 76 340 ≤ 1270215177219668 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3515 c22240R_122_22 (by norm_num)

theorem c22240R_122_20 : rowsJ2 122 123 74 340 ≤ 1274573420065260 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3514 c22240R_122_21 (by norm_num)

theorem c22240R_122_19 : rowsJ2 122 123 73 340 ≤ 1277684213926132 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3513 c22240R_122_20 (by norm_num)

theorem c22240R_122_18 : rowsJ2 122 123 72 340 ≤ 1281492363253409 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3512 c22240R_122_19 (by norm_num)

theorem c22240R_122_17 : rowsJ2 122 123 71 340 ≤ 1285526225281316 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3511 c22240R_122_18 (by norm_num)

theorem c22240R_122_16 : rowsJ2 122 123 70 340 ≤ 1289727124838753 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3510 c22240R_122_17 (by norm_num)

theorem c22240R_122_15 : rowsJ2 122 123 69 340 ≤ 1294014650253642 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3509 c22240R_122_16 (by norm_num)

theorem c22240R_122_14 : rowsJ2 122 123 68 340 ≤ 1298333523950638 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3508 c22240R_122_15 (by norm_num)

theorem c22240R_122_13 : rowsJ2 122 123 67 340 ≤ 1302606627258688 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3507 c22240R_122_14 (by norm_num)

theorem c22240R_122_12 : rowsJ2 122 123 66 340 ≤ 1306781275100934 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3506 c22240R_122_13 (by norm_num)

theorem c22240R_122_11 : rowsJ2 122 123 65 340 ≤ 1310782779716734 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3505 c22240R_122_12 (by norm_num)

theorem c22240R_122_10 : rowsJ2 122 123 64 340 ≤ 1314560318834022 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3504 c22240R_122_11 (by norm_num)

theorem c22240R_122_9 : rowsJ2 122 123 63 340 ≤ 1318041125253327 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3503 c22240R_122_10 (by norm_num)

theorem c22240R_122_8 : rowsJ2 122 123 61 340 ≤ 1323893180520652 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3502 c22240R_122_9 (by norm_num)

theorem c22240R_122_7 : rowsJ2 122 123 58 340 ≤ 1329353560068349 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3501 c22240R_122_8 (by norm_num)

theorem c22240R_122_6 : rowsJ2 122 123 47 340 ≤ 1332048313400258 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3500 c22240R_122_7 (by norm_num)

theorem c22240R_122_5 : rowsJ2 122 123 38 340 ≤ 1335674836861596 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3499 c22240R_122_6 (by norm_num)

theorem c22240R_122_4 : rowsJ2 122 123 34 340 ≤ 1351019675012614 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3498 c22240R_122_5 (by norm_num)

theorem c22240R_122_3 : rowsJ2 122 123 31 340 ≤ 1371264042952363 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3497 c22240R_122_4 (by norm_num)

theorem c22240R_122_2 : rowsJ2 122 123 29 340 ≤ 1386777053205479 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3496 c22240R_122_3 (by norm_num)

theorem c22240R_122_1 : rowsJ2 122 123 26 340 ≤ 1397404636445963 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3495 c22240R_122_2 (by norm_num)

theorem c22240R_122_0 : rowsJ2 122 123 0 340 ≤ 1398737142542262 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22240R_3494 c22240R_122_1 (by norm_num)

theorem hr22240R_122 : rows2 122 123 ≤ 1398737142542262 := rows2_le_of_rowsJ2 122 123 c22240R_122_0

theorem c22240R_123_27 : rowsJ2 123 124 91 340 ≤ 1126591175876209 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3550 rows22240R_3551 (by norm_num)

theorem c22240R_123_26 : rowsJ2 123 124 89 340 ≤ 1143370624781460 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3549 c22240R_123_27 (by norm_num)

theorem c22240R_123_25 : rowsJ2 123 124 87 340 ≤ 1155024130548411 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3548 c22240R_123_26 (by norm_num)

theorem c22240R_123_24 : rowsJ2 123 124 84 340 ≤ 1164858028237609 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3547 c22240R_123_25 (by norm_num)

theorem c22240R_123_23 : rowsJ2 123 124 80 340 ≤ 1167963487761565 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3546 c22240R_123_24 (by norm_num)

theorem c22240R_123_22 : rowsJ2 123 124 77 340 ≤ 1170273140788822 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3545 c22240R_123_23 (by norm_num)

theorem c22240R_123_21 : rowsJ2 123 124 75 340 ≤ 1174208326617225 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3544 c22240R_123_22 (by norm_num)

theorem c22240R_123_20 : rowsJ2 123 124 74 340 ≤ 1177040237813532 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3543 c22240R_123_21 (by norm_num)

theorem c22240R_123_19 : rowsJ2 123 124 73 340 ≤ 1180506941130367 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3542 c22240R_123_20 (by norm_num)

theorem c22240R_123_18 : rowsJ2 123 124 72 340 ≤ 1184671937400587 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3541 c22240R_123_19 (by norm_num)

theorem c22240R_123_17 : rowsJ2 123 124 71 340 ≤ 1189288331467433 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3540 c22240R_123_18 (by norm_num)

theorem c22240R_123_16 : rowsJ2 123 124 70 340 ≤ 1194041004039267 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3539 c22240R_123_17 (by norm_num)

theorem c22240R_123_15 : rowsJ2 123 124 69 340 ≤ 1198850089287364 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3538 c22240R_123_16 (by norm_num)

theorem c22240R_123_14 : rowsJ2 123 124 68 340 ≤ 1203660685562288 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3537 c22240R_123_15 (by norm_num)

theorem c22240R_123_13 : rowsJ2 123 124 67 340 ≤ 1208396154354575 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3536 c22240R_123_14 (by norm_num)

theorem c22240R_123_12 : rowsJ2 123 124 66 340 ≤ 1213004110256496 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3535 c22240R_123_13 (by norm_num)

theorem c22240R_123_11 : rowsJ2 123 124 65 340 ≤ 1217410274900619 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3534 c22240R_123_12 (by norm_num)

theorem c22240R_123_10 : rowsJ2 123 124 64 340 ≤ 1221564088262417 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3533 c22240R_123_11 (by norm_num)

theorem c22240R_123_9 : rowsJ2 123 124 63 340 ≤ 1225393149437719 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3532 c22240R_123_10 (by norm_num)

theorem c22240R_123_8 : rowsJ2 123 124 62 340 ≤ 1228848318569569 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3531 c22240R_123_9 (by norm_num)

theorem c22240R_123_7 : rowsJ2 123 124 60 340 ≤ 1234375962763071 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3530 c22240R_123_8 (by norm_num)

theorem c22240R_123_6 : rowsJ2 123 124 57 340 ≤ 1239261498188021 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3529 c22240R_123_7 (by norm_num)

theorem c22240R_123_5 : rowsJ2 123 124 43 340 ≤ 1241374112316959 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3528 c22240R_123_6 (by norm_num)

theorem c22240R_123_4 : rowsJ2 123 124 36 340 ≤ 1249105345653571 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3527 c22240R_123_5 (by norm_num)

theorem c22240R_123_3 : rowsJ2 123 124 32 340 ≤ 1267412019474459 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3526 c22240R_123_4 (by norm_num)

theorem c22240R_123_2 : rowsJ2 123 124 29 340 ≤ 1289304375253243 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3525 c22240R_123_3 (by norm_num)

theorem c22240R_123_1 : rowsJ2 123 124 26 340 ≤ 1301024788153033 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3524 c22240R_123_2 (by norm_num)

theorem c22240R_123_0 : rowsJ2 123 124 0 340 ≤ 1302984882449890 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22240R_3523 c22240R_123_1 (by norm_num)

theorem hr22240R_123 : rows2 123 124 ≤ 1302984882449890 := rows2_le_of_rowsJ2 123 124 c22240R_123_0

theorem c22240R_124_27 : rowsJ2 124 125 90 340 ≤ 1118429392570492 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3579 rows22240R_3580 (by norm_num)

theorem c22240R_124_26 : rowsJ2 124 125 88 340 ≤ 1133362247760903 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3578 c22240R_124_27 (by norm_num)

theorem c22240R_124_25 : rowsJ2 124 125 85 340 ≤ 1146869580773839 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3577 c22240R_124_26 (by norm_num)

theorem c22240R_124_24 : rowsJ2 124 125 82 340 ≤ 1152314552068694 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3576 c22240R_124_25 (by norm_num)

theorem c22240R_124_23 : rowsJ2 124 125 79 340 ≤ 1153817717000021 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3575 c22240R_124_24 (by norm_num)

theorem c22240R_124_22 : rowsJ2 124 125 77 340 ≤ 1156421304413128 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3574 c22240R_124_23 (by norm_num)

theorem c22240R_124_21 : rowsJ2 124 125 75 340 ≤ 1161004808314194 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3573 c22240R_124_22 (by norm_num)

theorem c22240R_124_20 : rowsJ2 124 125 74 340 ≤ 1164162259828329 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3572 c22240R_124_21 (by norm_num)

theorem c22240R_124_19 : rowsJ2 124 125 73 340 ≤ 1167955525651049 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3571 c22240R_124_20 (by norm_num)

theorem c22240R_124_18 : rowsJ2 124 125 72 340 ≤ 1172448076319834 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3570 c22240R_124_19 (by norm_num)

theorem c22240R_124_17 : rowsJ2 124 125 71 340 ≤ 1177681191750961 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3569 c22240R_124_18 (by norm_num)

theorem c22240R_124_16 : rowsJ2 124 125 70 340 ≤ 1183019635601964 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3568 c22240R_124_17 (by norm_num)

theorem c22240R_124_15 : rowsJ2 124 125 69 340 ≤ 1188384098479677 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3567 c22240R_124_16 (by norm_num)

theorem c22240R_124_14 : rowsJ2 124 125 68 340 ≤ 1193720065596991 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3566 c22240R_124_15 (by norm_num)

theorem c22240R_124_13 : rowsJ2 124 125 67 340 ≤ 1198951384353449 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3565 c22240R_124_14 (by norm_num)

theorem c22240R_124_12 : rowsJ2 124 125 66 340 ≤ 1204025980494069 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3564 c22240R_124_13 (by norm_num)

theorem c22240R_124_11 : rowsJ2 124 125 65 340 ≤ 1208869996268549 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3563 c22240R_124_12 (by norm_num)

theorem c22240R_124_10 : rowsJ2 124 125 64 340 ≤ 1213433144984415 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3562 c22240R_124_11 (by norm_num)

theorem c22240R_124_9 : rowsJ2 124 125 63 340 ≤ 1217643406494521 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3561 c22240R_124_10 (by norm_num)

theorem c22240R_124_8 : rowsJ2 124 125 62 340 ≤ 1221451864418323 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3560 c22240R_124_9 (by norm_num)

theorem c22240R_124_7 : rowsJ2 124 125 60 340 ≤ 1227603555135427 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3559 c22240R_124_8 (by norm_num)

theorem c22240R_124_6 : rowsJ2 124 125 57 340 ≤ 1233216691754108 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3558 c22240R_124_7 (by norm_num)

theorem c22240R_124_5 : rowsJ2 124 125 45 340 ≤ 1235988409225732 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3557 c22240R_124_6 (by norm_num)

theorem c22240R_124_4 : rowsJ2 124 125 36 340 ≤ 1242005059763381 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3556 c22240R_124_5 (by norm_num)

theorem c22240R_124_3 : rowsJ2 124 125 32 340 ≤ 1257549608690959 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3555 c22240R_124_4 (by norm_num)

theorem c22240R_124_2 : rowsJ2 124 125 29 340 ≤ 1278079570404031 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3554 c22240R_124_3 (by norm_num)

theorem c22240R_124_1 : rowsJ2 124 125 26 340 ≤ 1290896559894545 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3553 c22240R_124_2 (by norm_num)

theorem c22240R_124_0 : rowsJ2 124 125 0 340 ≤ 1293615223658231 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22240R_3552 c22240R_124_1 (by norm_num)

theorem hr22240R_124 : rows2 124 125 ≤ 1293615223658231 := rows2_le_of_rowsJ2 124 125 c22240R_124_0

theorem c22240R_125_28 : rowsJ2 125 126 89 340 ≤ 1027648453644910 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3609 rows22240R_3610 (by norm_num)

theorem c22240R_125_27 : rowsJ2 125 126 87 340 ≤ 1040707876208162 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3608 c22240R_125_28 (by norm_num)

theorem c22240R_125_26 : rowsJ2 125 126 84 340 ≤ 1051837434506601 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3607 c22240R_125_27 (by norm_num)

theorem c22240R_125_25 : rowsJ2 125 126 81 340 ≤ 1055680182813568 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3606 c22240R_125_26 (by norm_num)

theorem c22240R_125_24 : rowsJ2 125 126 78 340 ≤ 1058554455360672 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3605 c22240R_125_25 (by norm_num)

theorem c22240R_125_23 : rowsJ2 125 126 76 340 ≤ 1062637831971232 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3604 c22240R_125_24 (by norm_num)

theorem c22240R_125_22 : rowsJ2 125 126 75 340 ≤ 1065467490953625 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3603 c22240R_125_23 (by norm_num)

theorem c22240R_125_21 : rowsJ2 125 126 74 340 ≤ 1068895375170887 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3602 c22240R_125_22 (by norm_num)

theorem c22240R_125_20 : rowsJ2 125 126 73 340 ≤ 1072959939218086 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3601 c22240R_125_21 (by norm_num)

theorem c22240R_125_19 : rowsJ2 125 126 72 340 ≤ 1077724621457801 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3600 c22240R_125_20 (by norm_num)

theorem c22240R_125_18 : rowsJ2 125 126 71 340 ≤ 1083230806114122 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3599 c22240R_125_19 (by norm_num)

theorem c22240R_125_17 : rowsJ2 125 126 70 340 ≤ 1089162399059647 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3598 c22240R_125_18 (by norm_num)

theorem c22240R_125_16 : rowsJ2 125 126 69 340 ≤ 1095089189304612 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3597 c22240R_125_17 (by norm_num)

theorem c22240R_125_15 : rowsJ2 125 126 68 340 ≤ 1100957057396969 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3596 c22240R_125_16 (by norm_num)

theorem c22240R_125_14 : rowsJ2 125 126 67 340 ≤ 1106690343600173 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3595 c22240R_125_15 (by norm_num)

theorem c22240R_125_13 : rowsJ2 125 126 66 340 ≤ 1112237278435612 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3594 c22240R_125_14 (by norm_num)

theorem c22240R_125_12 : rowsJ2 125 126 65 340 ≤ 1117524437270290 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3593 c22240R_125_13 (by norm_num)

theorem c22240R_125_11 : rowsJ2 125 126 64 340 ≤ 1122501805130423 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3592 c22240R_125_12 (by norm_num)

theorem c22240R_125_10 : rowsJ2 125 126 63 340 ≤ 1127097755974585 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3591 c22240R_125_11 (by norm_num)

theorem c22240R_125_9 : rowsJ2 125 126 62 340 ≤ 1131263599727425 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3590 c22240R_125_10 (by norm_num)

theorem c22240R_125_8 : rowsJ2 125 126 61 340 ≤ 1134929057910017 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3589 c22240R_125_9 (by norm_num)

theorem c22240R_125_7 : rowsJ2 125 126 60 340 ≤ 1138046382230135 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3588 c22240R_125_8 (by norm_num)

theorem c22240R_125_6 : rowsJ2 125 126 58 340 ≤ 1142735765659784 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3587 c22240R_125_7 (by norm_num)

theorem c22240R_125_5 : rowsJ2 125 126 53 340 ≤ 1147574523163511 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3586 c22240R_125_6 (by norm_num)

theorem c22240R_125_4 : rowsJ2 125 126 37 340 ≤ 1150279340257872 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3585 c22240R_125_5 (by norm_num)

theorem c22240R_125_3 : rowsJ2 125 126 32 340 ≤ 1165227479632780 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3584 c22240R_125_4 (by norm_num)

theorem c22240R_125_2 : rowsJ2 125 126 29 340 ≤ 1182926890407270 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3583 c22240R_125_3 (by norm_num)

theorem c22240R_125_1 : rowsJ2 125 126 26 340 ≤ 1196977343034563 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3582 c22240R_125_2 (by norm_num)

theorem c22240R_125_0 : rowsJ2 125 126 0 340 ≤ 1200462595090712 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22240R_3581 c22240R_125_1 (by norm_num)

theorem hr22240R_125 : rows2 125 126 ≤ 1200462595090712 := rows2_le_of_rowsJ2 125 126 c22240R_125_0

theorem c22240R_126_27 : rowsJ2 126 127 89 340 ≤ 1011497967729778 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3638 rows22240R_3639 (by norm_num)

theorem c22240R_126_26 : rowsJ2 126 127 86 340 ≤ 1030339568268877 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3637 c22240R_126_27 (by norm_num)

theorem c22240R_126_25 : rowsJ2 126 127 83 340 ≤ 1039211166117592 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3636 c22240R_126_26 (by norm_num)

theorem c22240R_126_24 : rowsJ2 126 127 80 340 ≤ 1042615044169666 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3635 c22240R_126_25 (by norm_num)

theorem c22240R_126_23 : rowsJ2 126 127 78 340 ≤ 1045380542595960 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3634 c22240R_126_24 (by norm_num)

theorem c22240R_126_22 : rowsJ2 126 127 76 340 ≤ 1049944881851604 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3633 c22240R_126_23 (by norm_num)

theorem c22240R_126_21 : rowsJ2 126 127 75 340 ≤ 1053016241032223 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3632 c22240R_126_22 (by norm_num)

theorem c22240R_126_20 : rowsJ2 126 127 74 340 ≤ 1056686646090416 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3631 c22240R_126_21 (by norm_num)

theorem c22240R_126_19 : rowsJ2 126 127 73 340 ≤ 1060994659005136 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3630 c22240R_126_20 (by norm_num)

theorem c22240R_126_18 : rowsJ2 126 127 72 340 ≤ 1066003687414969 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3629 c22240R_126_19 (by norm_num)

theorem c22240R_126_17 : rowsJ2 126 127 71 340 ≤ 1071755219688811 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3628 c22240R_126_18 (by norm_num)

theorem c22240R_126_16 : rowsJ2 126 127 70 340 ≤ 1078315446473546 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3627 c22240R_126_17 (by norm_num)

theorem c22240R_126_15 : rowsJ2 126 127 69 340 ≤ 1084839827647444 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3626 c22240R_126_16 (by norm_num)

theorem c22240R_126_14 : rowsJ2 126 127 68 340 ≤ 1091274652469158 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3625 c22240R_126_15 (by norm_num)

theorem c22240R_126_13 : rowsJ2 126 127 67 340 ≤ 1097544760770247 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3624 c22240R_126_14 (by norm_num)

theorem c22240R_126_12 : rowsJ2 126 127 66 340 ≤ 1103598708012027 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3623 c22240R_126_13 (by norm_num)

theorem c22240R_126_11 : rowsJ2 126 127 65 340 ≤ 1109363511944663 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3622 c22240R_126_12 (by norm_num)

theorem c22240R_126_10 : rowsJ2 126 127 64 340 ≤ 1114789438452846 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3621 c22240R_126_11 (by norm_num)

theorem c22240R_126_9 : rowsJ2 126 127 63 340 ≤ 1119805265946330 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3620 c22240R_126_10 (by norm_num)

theorem c22240R_126_8 : rowsJ2 126 127 62 340 ≤ 1124362541824795 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3619 c22240R_126_9 (by norm_num)

theorem c22240R_126_7 : rowsJ2 126 127 61 340 ≤ 1128391351647171 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3618 c22240R_126_8 (by norm_num)

theorem c22240R_126_6 : rowsJ2 126 127 59 340 ≤ 1134739554905854 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3617 c22240R_126_7 (by norm_num)

theorem c22240R_126_5 : rowsJ2 126 127 56 340 ≤ 1140513076887381 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3616 c22240R_126_6 (by norm_num)

theorem c22240R_126_4 : rowsJ2 126 127 40 340 ≤ 1143365721925992 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3615 c22240R_126_5 (by norm_num)

theorem c22240R_126_3 : rowsJ2 126 127 33 340 ≤ 1153781313877077 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3614 c22240R_126_4 (by norm_num)

theorem c22240R_126_2 : rowsJ2 126 127 29 340 ≤ 1172471525733022 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3613 c22240R_126_3 (by norm_num)

theorem c22240R_126_1 : rowsJ2 126 127 26 340 ≤ 1187755125062091 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3612 c22240R_126_2 (by norm_num)

theorem c22240R_126_0 : rowsJ2 126 127 0 340 ≤ 1192011334497499 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22240R_3611 c22240R_126_1 (by norm_num)

theorem hr22240R_126 : rows2 126 127 ≤ 1192011334497499 := rows2_le_of_rowsJ2 126 127 c22240R_126_0

theorem c22240R_127_28 : rowsJ2 127 128 89 340 ≤ 914495899231773 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3668 rows22240R_3669 (by norm_num)

theorem c22240R_127_27 : rowsJ2 127 128 86 340 ≤ 934384322027851 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3667 c22240R_127_28 (by norm_num)

theorem c22240R_127_26 : rowsJ2 127 128 83 340 ≤ 943937196616546 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3666 c22240R_127_27 (by norm_num)

theorem c22240R_127_25 : rowsJ2 127 128 80 340 ≤ 947993561099857 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3665 c22240R_127_26 (by norm_num)

theorem c22240R_127_24 : rowsJ2 127 128 78 340 ≤ 951130016539660 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3664 c22240R_127_25 (by norm_num)

theorem c22240R_127_23 : rowsJ2 127 128 76 340 ≤ 956067674998143 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3663 c22240R_127_24 (by norm_num)

theorem c22240R_127_22 : rowsJ2 127 128 75 340 ≤ 959326696162358 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3662 c22240R_127_23 (by norm_num)

theorem c22240R_127_21 : rowsJ2 127 128 74 340 ≤ 963185436642803 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3661 c22240R_127_22 (by norm_num)

theorem c22240R_127_20 : rowsJ2 127 128 73 340 ≤ 967682562704432 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3660 c22240R_127_21 (by norm_num)

theorem c22240R_127_19 : rowsJ2 127 128 72 340 ≤ 972881449495772 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3659 c22240R_127_20 (by norm_num)

theorem c22240R_127_18 : rowsJ2 127 128 71 340 ≤ 978823686240147 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3658 c22240R_127_19 (by norm_num)

theorem c22240R_127_17 : rowsJ2 127 128 70 340 ≤ 985575428143907 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3657 c22240R_127_18 (by norm_num)

theorem c22240R_127_16 : rowsJ2 127 128 69 340 ≤ 992705344533085 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3656 c22240R_127_17 (by norm_num)

theorem c22240R_127_15 : rowsJ2 127 128 68 340 ≤ 999714596620630 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3655 c22240R_127_16 (by norm_num)

theorem c22240R_127_14 : rowsJ2 127 128 67 340 ≤ 1006528523878218 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3654 c22240R_127_15 (by norm_num)

theorem c22240R_127_13 : rowsJ2 127 128 66 340 ≤ 1013096025611196 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3653 c22240R_127_14 (by norm_num)

theorem c22240R_127_12 : rowsJ2 127 128 65 340 ≤ 1019344566836879 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3652 c22240R_127_13 (by norm_num)

theorem c22240R_127_11 : rowsJ2 127 128 64 340 ≤ 1025224709559389 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3651 c22240R_127_12 (by norm_num)

theorem c22240R_127_10 : rowsJ2 127 128 63 340 ≤ 1030665629798738 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3650 c22240R_127_11 (by norm_num)

theorem c22240R_127_9 : rowsJ2 127 128 62 340 ≤ 1035619129228380 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3649 c22240R_127_10 (by norm_num)

theorem c22240R_127_8 : rowsJ2 127 128 61 340 ≤ 1040015654003450 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3648 c22240R_127_9 (by norm_num)

theorem c22240R_127_7 : rowsJ2 127 128 60 340 ≤ 1043807870281295 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3647 c22240R_127_8 (by norm_num)

theorem c22240R_127_6 : rowsJ2 127 128 58 340 ≤ 1049676448225793 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3646 c22240R_127_7 (by norm_num)

theorem c22240R_127_5 : rowsJ2 127 128 56 340 ≤ 1053545542044167 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3645 c22240R_127_6 (by norm_num)

theorem c22240R_127_4 : rowsJ2 127 128 42 340 ≤ 1057083966839616 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3644 c22240R_127_5 (by norm_num)

theorem c22240R_127_3 : rowsJ2 127 128 33 340 ≤ 1064847754038896 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3643 c22240R_127_4 (by norm_num)

theorem c22240R_127_2 : rowsJ2 127 128 29 340 ≤ 1080719626872372 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3642 c22240R_127_3 (by norm_num)

theorem c22240R_127_1 : rowsJ2 127 128 26 340 ≤ 1095924222398866 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3641 c22240R_127_2 (by norm_num)

theorem c22240R_127_0 : rowsJ2 127 128 0 340 ≤ 1100955964603437 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22240R_3640 c22240R_127_1 (by norm_num)

theorem hr22240R_127 : rows2 127 128 ≤ 1100955964603437 := rows2_le_of_rowsJ2 127 128 c22240R_127_0

theorem c22240R_128_28 : rowsJ2 128 129 87 340 ≤ 914380493499994 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3698 rows22240R_3699 (by norm_num)

theorem c22240R_128_27 : rowsJ2 128 129 84 340 ≤ 927834147997504 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3697 c22240R_128_28 (by norm_num)

theorem c22240R_128_26 : rowsJ2 128 129 81 340 ≤ 934006340026241 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3696 c22240R_128_27 (by norm_num)

theorem c22240R_128_25 : rowsJ2 128 129 79 340 ≤ 936694884054136 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3695 c22240R_128_26 (by norm_num)

theorem c22240R_128_24 : rowsJ2 128 129 77 340 ≤ 941004195949022 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3694 c22240R_128_25 (by norm_num)

theorem c22240R_128_23 : rowsJ2 128 129 76 340 ≤ 943884653237590 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3693 c22240R_128_24 (by norm_num)

theorem c22240R_128_22 : rowsJ2 128 129 75 340 ≤ 947304691692979 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3692 c22240R_128_23 (by norm_num)

theorem c22240R_128_21 : rowsJ2 128 129 74 340 ≤ 951325194369433 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3691 c22240R_128_22 (by norm_num)

theorem c22240R_128_20 : rowsJ2 128 129 73 340 ≤ 955984931736053 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3690 c22240R_128_21 (by norm_num)

theorem c22240R_128_19 : rowsJ2 128 129 72 340 ≤ 961347247726318 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3689 c22240R_128_20 (by norm_num)

theorem c22240R_128_18 : rowsJ2 128 129 71 340 ≤ 967453832899583 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3688 c22240R_128_19 (by norm_num)

theorem c22240R_128_17 : rowsJ2 128 129 70 340 ≤ 974370808283590 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3687 c22240R_128_18 (by norm_num)

theorem c22240R_128_16 : rowsJ2 128 129 69 340 ≤ 982143095694409 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3686 c22240R_128_17 (by norm_num)

theorem c22240R_128_15 : rowsJ2 128 129 68 340 ≤ 989763364108515 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3685 c22240R_128_16 (by norm_num)

theorem c22240R_128_14 : rowsJ2 128 129 67 340 ≤ 997157459581897 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3684 c22240R_128_15 (by norm_num)

theorem c22240R_128_13 : rowsJ2 128 129 66 340 ≤ 1004274639581533 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3683 c22240R_128_14 (by norm_num)

theorem c22240R_128_12 : rowsJ2 128 129 65 340 ≤ 1011042830587723 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3682 c22240R_128_13 (by norm_num)

theorem c22240R_128_11 : rowsJ2 128 129 64 340 ≤ 1017412909735996 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3681 c22240R_128_12 (by norm_num)

theorem c22240R_128_10 : rowsJ2 128 129 63 340 ≤ 1023314460030099 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3680 c22240R_128_11 (by norm_num)

theorem c22240R_128_9 : rowsJ2 128 129 62 340 ≤ 1028699547121846 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3679 c22240R_128_10 (by norm_num)

theorem c22240R_128_8 : rowsJ2 128 129 61 340 ≤ 1033498989728544 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3678 c22240R_128_9 (by norm_num)

theorem c22240R_128_7 : rowsJ2 128 129 60 340 ≤ 1037665684291491 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3677 c22240R_128_8 (by norm_num)

theorem c22240R_128_6 : rowsJ2 128 129 58 340 ≤ 1044196946044224 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3676 c22240R_128_7 (by norm_num)

theorem c22240R_128_5 : rowsJ2 128 129 56 340 ≤ 1048611156529206 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3675 c22240R_128_6 (by norm_num)

theorem c22240R_128_4 : rowsJ2 128 129 51 340 ≤ 1052906771867331 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3674 c22240R_128_5 (by norm_num)

theorem c22240R_128_3 : rowsJ2 128 129 34 340 ≤ 1056810314818253 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3673 c22240R_128_4 (by norm_num)

theorem c22240R_128_2 : rowsJ2 128 129 29 340 ≤ 1072072359745589 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3672 c22240R_128_3 (by norm_num)

theorem c22240R_128_1 : rowsJ2 128 129 25 340 ≤ 1090018293260966 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3671 c22240R_128_2 (by norm_num)

theorem c22240R_128_0 : rowsJ2 128 129 0 340 ≤ 1093101498978048 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22240R_3670 c22240R_128_1 (by norm_num)

theorem hr22240R_128 : rows2 128 129 ≤ 1093101498978048 := rows2_le_of_rowsJ2 128 129 c22240R_128_0

theorem c22240R_129_28 : rowsJ2 129 130 87 340 ≤ 820069469530420 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3728 rows22240R_3729 (by norm_num)

theorem c22240R_129_27 : rowsJ2 129 130 84 340 ≤ 834478169652292 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3727 c22240R_129_28 (by norm_num)

theorem c22240R_129_26 : rowsJ2 129 130 81 340 ≤ 841187392293582 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3726 c22240R_129_27 (by norm_num)

theorem c22240R_129_25 : rowsJ2 129 130 79 340 ≤ 844086561791349 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3725 c22240R_129_26 (by norm_num)

theorem c22240R_129_24 : rowsJ2 129 130 77 340 ≤ 848608442220323 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3724 c22240R_129_25 (by norm_num)

theorem c22240R_129_23 : rowsJ2 129 130 76 340 ≤ 851595994727478 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3723 c22240R_129_24 (by norm_num)

theorem c22240R_129_22 : rowsJ2 129 130 75 340 ≤ 855123763759348 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3722 c22240R_129_23 (by norm_num)

theorem c22240R_129_21 : rowsJ2 129 130 74 340 ≤ 859252601265991 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3721 c22240R_129_22 (by norm_num)

theorem c22240R_129_20 : rowsJ2 129 130 73 340 ≤ 864021378398509 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3720 c22240R_129_21 (by norm_num)

theorem c22240R_129_19 : rowsJ2 129 130 72 340 ≤ 869493400012909 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3719 c22240R_129_20 (by norm_num)

theorem c22240R_129_18 : rowsJ2 129 130 71 340 ≤ 875710450250389 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3718 c22240R_129_19 (by norm_num)

theorem c22240R_129_17 : rowsJ2 129 130 70 340 ≤ 882738613540544 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3717 c22240R_129_18 (by norm_num)

theorem c22240R_129_16 : rowsJ2 129 130 69 340 ≤ 890622906177354 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3716 c22240R_129_17 (by norm_num)

theorem c22240R_129_15 : rowsJ2 129 130 68 340 ≤ 898862686445416 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3715 c22240R_129_16 (by norm_num)

theorem c22240R_129_14 : rowsJ2 129 130 67 340 ≤ 906844937679846 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3714 c22240R_129_15 (by norm_num)

theorem c22240R_129_13 : rowsJ2 129 130 66 340 ≤ 914519274266893 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3713 c22240R_129_14 (by norm_num)

theorem c22240R_129_12 : rowsJ2 129 130 65 340 ≤ 921814103712910 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3712 c22240R_129_13 (by norm_num)

theorem c22240R_129_11 : rowsJ2 129 130 64 340 ≤ 928680617996021 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3711 c22240R_129_12 (by norm_num)

theorem c22240R_129_10 : rowsJ2 129 130 63 340 ≤ 935048829903440 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3710 c22240R_129_11 (by norm_num)

theorem c22240R_129_9 : rowsJ2 129 130 62 340 ≤ 940871066327363 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3709 c22240R_129_10 (by norm_num)

theorem c22240R_129_8 : rowsJ2 129 130 61 340 ≤ 946078531693037 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3708 c22240R_129_9 (by norm_num)

theorem c22240R_129_7 : rowsJ2 129 130 60 340 ≤ 950624351338680 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3707 c22240R_129_8 (by norm_num)

theorem c22240R_129_6 : rowsJ2 129 130 59 340 ≤ 954526563890080 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3706 c22240R_129_7 (by norm_num)

theorem c22240R_129_5 : rowsJ2 129 130 57 340 ≤ 960566439027494 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3705 c22240R_129_6 (by norm_num)

theorem c22240R_129_4 : rowsJ2 129 130 53 340 ≤ 966860557450972 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3704 c22240R_129_5 (by norm_num)

theorem c22240R_129_3 : rowsJ2 129 130 35 340 ≤ 969428054929056 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3703 c22240R_129_4 (by norm_num)

theorem c22240R_129_2 : rowsJ2 129 130 29 340 ≤ 983007544314043 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3702 c22240R_129_3 (by norm_num)

theorem c22240R_129_1 : rowsJ2 129 130 25 340 ≤ 1000080001954664 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3701 c22240R_129_2 (by norm_num)

theorem c22240R_129_0 : rowsJ2 129 130 0 340 ≤ 1003691875395412 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22240R_3700 c22240R_129_1 (by norm_num)

theorem hr22240R_129 : rows2 129 130 ≤ 1003691875395412 := rows2_le_of_rowsJ2 129 130 c22240R_129_0

theorem c22240R_130_28 : rowsJ2 130 131 87 340 ≤ 806773293522811 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3758 rows22240R_3759 (by norm_num)

theorem c22240R_130_27 : rowsJ2 130 131 84 340 ≤ 822245975476459 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3757 c22240R_130_28 (by norm_num)

theorem c22240R_130_26 : rowsJ2 130 131 81 340 ≤ 829539144501209 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3756 c22240R_130_27 (by norm_num)

theorem c22240R_130_25 : rowsJ2 130 131 79 340 ≤ 832597309710018 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3755 c22240R_130_26 (by norm_num)

theorem c22240R_130_24 : rowsJ2 130 131 77 340 ≤ 837280439248495 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3754 c22240R_130_25 (by norm_num)

theorem c22240R_130_23 : rowsJ2 130 131 76 340 ≤ 840349545112112 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3753 c22240R_130_24 (by norm_num)

theorem c22240R_130_22 : rowsJ2 130 131 75 340 ≤ 843959581883615 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3752 c22240R_130_23 (by norm_num)

theorem c22240R_130_21 : rowsJ2 130 131 74 340 ≤ 848171371872854 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3751 c22240R_130_22 (by norm_num)

theorem c22240R_130_20 : rowsJ2 130 131 73 340 ≤ 853023887262021 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3750 c22240R_130_21 (by norm_num)

theorem c22240R_130_19 : rowsJ2 130 131 72 340 ≤ 858580400145242 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3749 c22240R_130_20 (by norm_num)

theorem c22240R_130_18 : rowsJ2 130 131 71 340 ≤ 864882787546423 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3748 c22240R_130_19 (by norm_num)

theorem c22240R_130_17 : rowsJ2 130 131 70 340 ≤ 871997094633722 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3747 c22240R_130_18 (by norm_num)

theorem c22240R_130_16 : rowsJ2 130 131 69 340 ≤ 879968432937933 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3746 c22240R_130_17 (by norm_num)

theorem c22240R_130_15 : rowsJ2 130 131 68 340 ≤ 888865970495149 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3745 c22240R_130_16 (by norm_num)

theorem c22240R_130_14 : rowsJ2 130 131 67 340 ≤ 897474343227448 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3744 c22240R_130_15 (by norm_num)

theorem c22240R_130_13 : rowsJ2 130 131 66 340 ≤ 905743539151812 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3743 c22240R_130_14 (by norm_num)

theorem c22240R_130_12 : rowsJ2 130 131 65 340 ≤ 913602457467063 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3742 c22240R_130_13 (by norm_num)

theorem c22240R_130_11 : rowsJ2 130 131 64 340 ≤ 921002620845790 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3741 c22240R_130_12 (by norm_num)

theorem c22240R_130_10 : rowsJ2 130 131 63 340 ≤ 927874484691965 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3740 c22240R_130_11 (by norm_num)

theorem c22240R_130_9 : rowsJ2 130 131 62 340 ≤ 934170658172435 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3739 c22240R_130_10 (by norm_num)

theorem c22240R_130_8 : rowsJ2 130 131 61 340 ≤ 939822741903822 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3738 c22240R_130_9 (by norm_num)

theorem c22240R_130_7 : rowsJ2 130 131 60 340 ≤ 944784100810789 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3737 c22240R_130_8 (by norm_num)

theorem c22240R_130_6 : rowsJ2 130 131 59 340 ≤ 949072609471139 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3736 c22240R_130_7 (by norm_num)

theorem c22240R_130_5 : rowsJ2 130 131 57 340 ≤ 955795995708613 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3735 c22240R_130_6 (by norm_num)

theorem c22240R_130_4 : rowsJ2 130 131 54 340 ≤ 961914939427187 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3734 c22240R_130_5 (by norm_num)

theorem c22240R_130_3 : rowsJ2 130 131 36 340 ≤ 965082396048859 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3733 c22240R_130_4 (by norm_num)

theorem c22240R_130_2 : rowsJ2 130 131 29 340 ≤ 976212075622093 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3732 c22240R_130_3 (by norm_num)

theorem c22240R_130_1 : rowsJ2 130 131 25 340 ≤ 992747875899447 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3731 c22240R_130_2 (by norm_num)

theorem c22240R_130_0 : rowsJ2 130 131 0 340 ≤ 996884702600961 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22240R_3730 c22240R_130_1 (by norm_num)

theorem hr22240R_130 : rows2 130 131 ≤ 996884702600961 := rows2_le_of_rowsJ2 130 131 c22240R_130_0

theorem c22240R_131_28 : rowsJ2 131 132 84 340 ≤ 731380828282281 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3788 rows22240R_3789 (by norm_num)

theorem c22240R_131_27 : rowsJ2 131 132 81 340 ≤ 738999050244464 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3787 c22240R_131_28 (by norm_num)

theorem c22240R_131_26 : rowsJ2 131 132 79 340 ≤ 742111880634630 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3786 c22240R_131_27 (by norm_num)

theorem c22240R_131_25 : rowsJ2 131 132 77 340 ≤ 746851426827344 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3785 c22240R_131_26 (by norm_num)

theorem c22240R_131_24 : rowsJ2 131 132 76 340 ≤ 749949475920675 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3784 c22240R_131_25 (by norm_num)

theorem c22240R_131_23 : rowsJ2 131 132 75 340 ≤ 753589032018708 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3783 c22240R_131_24 (by norm_num)

theorem c22240R_131_22 : rowsJ2 131 132 74 340 ≤ 757830880639940 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3782 c22240R_131_23 (by norm_num)

theorem c22240R_131_21 : rowsJ2 131 132 73 340 ≤ 762714091599359 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3781 c22240R_131_22 (by norm_num)

theorem c22240R_131_20 : rowsJ2 131 132 72 340 ≤ 768301901738414 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3780 c22240R_131_21 (by norm_num)

theorem c22240R_131_19 : rowsJ2 131 132 71 340 ≤ 774636282336756 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3779 c22240R_131_20 (by norm_num)

theorem c22240R_131_18 : rowsJ2 131 132 70 340 ≤ 781783235541385 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3778 c22240R_131_19 (by norm_num)

theorem c22240R_131_17 : rowsJ2 131 132 69 340 ≤ 789787960314953 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3777 c22240R_131_18 (by norm_num)

theorem c22240R_131_16 : rowsJ2 131 132 68 340 ≤ 798719584307952 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3776 c22240R_131_17 (by norm_num)

theorem c22240R_131_15 : rowsJ2 131 132 67 340 ≤ 807963145213278 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3775 c22240R_131_16 (by norm_num)

theorem c22240R_131_14 : rowsJ2 131 132 66 340 ≤ 816835723521485 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3774 c22240R_131_15 (by norm_num)

theorem c22240R_131_13 : rowsJ2 131 132 65 340 ≤ 825266710628701 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3773 c22240R_131_14 (by norm_num)

theorem c22240R_131_12 : rowsJ2 131 132 64 340 ≤ 833207975721563 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3772 c22240R_131_13 (by norm_num)

theorem c22240R_131_11 : rowsJ2 131 132 63 340 ≤ 840590418153510 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3771 c22240R_131_12 (by norm_num)

theorem c22240R_131_10 : rowsJ2 131 132 62 340 ≤ 847366948401033 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3770 c22240R_131_11 (by norm_num)

theorem c22240R_131_9 : rowsJ2 131 132 61 340 ≤ 853469569050233 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3769 c22240R_131_10 (by norm_num)

theorem c22240R_131_8 : rowsJ2 131 132 60 340 ≤ 858851900152569 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3768 c22240R_131_9 (by norm_num)

theorem c22240R_131_7 : rowsJ2 131 132 59 340 ≤ 863531650720539 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3767 c22240R_131_8 (by norm_num)

theorem c22240R_131_6 : rowsJ2 131 132 58 340 ≤ 867549287177533 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3766 c22240R_131_7 (by norm_num)

theorem c22240R_131_5 : rowsJ2 131 132 57 340 ≤ 870947042881594 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3765 c22240R_131_6 (by norm_num)

theorem c22240R_131_4 : rowsJ2 131 132 54 340 ≤ 877872099333758 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3764 c22240R_131_5 (by norm_num)

theorem c22240R_131_3 : rowsJ2 131 132 38 340 ≤ 881628501730833 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3763 c22240R_131_4 (by norm_num)

theorem c22240R_131_2 : rowsJ2 131 132 29 340 ≤ 889895204525978 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3762 c22240R_131_3 (by norm_num)

theorem c22240R_131_1 : rowsJ2 131 132 25 340 ≤ 904942515889956 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3761 c22240R_131_2 (by norm_num)

theorem c22240R_131_0 : rowsJ2 131 132 0 340 ≤ 909604849711913 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22240R_3760 c22240R_131_1 (by norm_num)

theorem hr22240R_131 : rows2 131 132 ≤ 909604849711913 := rows2_le_of_rowsJ2 131 132 c22240R_131_0

theorem c22240R_132_28 : rowsJ2 132 133 84 340 ≤ 721806813971262 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3818 rows22240R_3819 (by norm_num)

theorem c22240R_132_27 : rowsJ2 132 133 81 340 ≤ 729804545968723 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3817 c22240R_132_28 (by norm_num)

theorem c22240R_132_26 : rowsJ2 132 133 79 340 ≤ 732922311061334 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3816 c22240R_132_27 (by norm_num)

theorem c22240R_132_25 : rowsJ2 132 133 77 340 ≤ 737668889157292 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3815 c22240R_132_26 (by norm_num)

theorem c22240R_132_24 : rowsJ2 132 133 76 340 ≤ 740771320936175 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3814 c22240R_132_25 (by norm_num)

theorem c22240R_132_23 : rowsJ2 132 133 75 340 ≤ 744415929209417 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3813 c22240R_132_24 (by norm_num)

theorem c22240R_132_22 : rowsJ2 132 133 74 340 ≤ 748663463466372 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3812 c22240R_132_23 (by norm_num)

theorem c22240R_132_21 : rowsJ2 132 133 73 340 ≤ 753553086972933 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3811 c22240R_132_22 (by norm_num)

theorem c22240R_132_20 : rowsJ2 132 133 72 340 ≤ 759148002849284 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3810 c22240R_132_21 (by norm_num)

theorem c22240R_132_19 : rowsJ2 132 133 71 340 ≤ 765490277212939 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3809 c22240R_132_20 (by norm_num)

theorem c22240R_132_18 : rowsJ2 132 133 70 340 ≤ 772645875781099 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3808 c22240R_132_19 (by norm_num)

theorem c22240R_132_17 : rowsJ2 132 133 69 340 ≤ 780660084412331 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3807 c22240R_132_18 (by norm_num)

theorem c22240R_132_16 : rowsJ2 132 133 68 340 ≤ 789601987888513 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3806 c22240R_132_17 (by norm_num)

theorem c22240R_132_15 : rowsJ2 132 133 67 340 ≤ 799520458002293 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3805 c22240R_132_16 (by norm_num)

theorem c22240R_132_14 : rowsJ2 132 133 66 340 ≤ 809035824769549 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3804 c22240R_132_15 (by norm_num)

theorem c22240R_132_13 : rowsJ2 132 133 65 340 ≤ 818077996458806 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3803 c22240R_132_14 (by norm_num)

theorem c22240R_132_12 : rowsJ2 132 133 64 340 ≤ 826599202350956 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3802 c22240R_132_13 (by norm_num)

theorem c22240R_132_11 : rowsJ2 132 133 63 340 ≤ 834530798645975 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3801 c22240R_132_12 (by norm_num)

theorem c22240R_132_10 : rowsJ2 132 133 62 340 ≤ 841826013531110 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3800 c22240R_132_11 (by norm_num)

theorem c22240R_132_9 : rowsJ2 132 133 61 340 ≤ 848417266450498 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3799 c22240R_132_10 (by norm_num)

theorem c22240R_132_8 : rowsJ2 132 133 60 340 ≤ 854258453609392 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3798 c22240R_132_9 (by norm_num)

theorem c22240R_132_7 : rowsJ2 132 133 59 340 ≤ 859367133699487 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3797 c22240R_132_8 (by norm_num)

theorem c22240R_132_6 : rowsJ2 132 133 58 340 ≤ 863783475369428 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3796 c22240R_132_7 (by norm_num)

theorem c22240R_132_5 : rowsJ2 132 133 57 340 ≤ 867549378179347 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3795 c22240R_132_6 (by norm_num)

theorem c22240R_132_4 : rowsJ2 132 133 55 340 ≤ 873306794421239 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3794 c22240R_132_5 (by norm_num)

theorem c22240R_132_3 : rowsJ2 132 133 49 340 ≤ 879953871312136 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3793 c22240R_132_4 (by norm_num)

theorem c22240R_132_2 : rowsJ2 132 133 30 340 ≤ 883972393140686 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3792 c22240R_132_3 (by norm_num)

theorem c22240R_132_1 : rowsJ2 132 133 25 340 ≤ 899707712993316 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3791 c22240R_132_2 (by norm_num)

theorem c22240R_132_0 : rowsJ2 132 133 0 340 ≤ 905031251002210 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22240R_3790 c22240R_132_1 (by norm_num)

theorem hr22240R_132 : rows2 132 133 ≤ 905031251002210 := rows2_le_of_rowsJ2 132 133 c22240R_132_0

theorem c22240R_133_27 : rowsJ2 133 134 83 340 ≤ 637476206206594 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3847 rows22240R_3848 (by norm_num)

theorem c22240R_133_26 : rowsJ2 133 134 80 340 ≤ 643364129504744 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3846 c22240R_133_27 (by norm_num)

theorem c22240R_133_25 : rowsJ2 133 134 78 340 ≤ 647152968469441 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3845 c22240R_133_26 (by norm_num)

theorem c22240R_133_24 : rowsJ2 133 134 76 340 ≤ 652756054918819 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3844 c22240R_133_25 (by norm_num)

theorem c22240R_133_23 : rowsJ2 133 134 75 340 ≤ 656353336262623 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3843 c22240R_133_24 (by norm_num)

theorem c22240R_133_22 : rowsJ2 133 134 74 340 ≤ 660554041218728 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3842 c22240R_133_23 (by norm_num)

theorem c22240R_133_21 : rowsJ2 133 134 73 340 ≤ 665397422447877 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3841 c22240R_133_22 (by norm_num)

theorem c22240R_133_20 : rowsJ2 133 134 72 340 ≤ 670946642170021 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3840 c22240R_133_21 (by norm_num)

theorem c22240R_133_19 : rowsJ2 133 134 71 340 ≤ 677243857891248 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3839 c22240R_133_20 (by norm_num)

theorem c22240R_133_18 : rowsJ2 133 134 70 340 ≤ 684354996148567 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3838 c22240R_133_19 (by norm_num)

theorem c22240R_133_17 : rowsJ2 133 134 69 340 ≤ 692325431270465 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3837 c22240R_133_18 (by norm_num)

theorem c22240R_133_16 : rowsJ2 133 134 68 340 ≤ 701224201208315 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3836 c22240R_133_17 (by norm_num)

theorem c22240R_133_15 : rowsJ2 133 134 67 340 ≤ 711100259556567 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3835 c22240R_133_16 (by norm_num)

theorem c22240R_133_14 : rowsJ2 133 134 66 340 ≤ 721268086575917 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3834 c22240R_133_15 (by norm_num)

theorem c22240R_133_13 : rowsJ2 133 134 65 340 ≤ 730930524081600 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3833 c22240R_133_14 (by norm_num)

theorem c22240R_133_12 : rowsJ2 133 134 64 340 ≤ 740040170887795 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3832 c22240R_133_13 (by norm_num)

theorem c22240R_133_11 : rowsJ2 133 134 63 340 ≤ 748528859060978 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3831 c22240R_133_12 (by norm_num)

theorem c22240R_133_10 : rowsJ2 133 134 62 340 ≤ 756350133680295 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3830 c22240R_133_11 (by norm_num)

theorem c22240R_133_9 : rowsJ2 133 134 61 340 ≤ 763436851192033 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3829 c22240R_133_10 (by norm_num)

theorem c22240R_133_8 : rowsJ2 133 134 60 340 ≤ 769743185050538 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3828 c22240R_133_9 (by norm_num)

theorem c22240R_133_7 : rowsJ2 133 134 59 340 ≤ 775286570967747 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3827 c22240R_133_8 (by norm_num)

theorem c22240R_133_6 : rowsJ2 133 134 58 340 ≤ 780106880942028 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3826 c22240R_133_7 (by norm_num)

theorem c22240R_133_5 : rowsJ2 133 134 56 340 ≤ 787746418192362 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3825 c22240R_133_6 (by norm_num)

theorem c22240R_133_4 : rowsJ2 133 134 54 340 ≤ 793016845133672 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3824 c22240R_133_5 (by norm_num)

theorem c22240R_133_3 : rowsJ2 133 134 49 340 ≤ 798466182790781 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3823 c22240R_133_4 (by norm_num)

theorem c22240R_133_2 : rowsJ2 133 134 29 340 ≤ 802623442446934 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3822 c22240R_133_3 (by norm_num)

theorem c22240R_133_1 : rowsJ2 133 134 24 340 ≤ 817252184276887 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3821 c22240R_133_2 (by norm_num)

theorem c22240R_133_0 : rowsJ2 133 134 0 340 ≤ 820294332872797 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22240R_3820 c22240R_133_1 (by norm_num)

theorem hr22240R_133 : rows2 133 134 ≤ 820294332872797 := rows2_le_of_rowsJ2 133 134 c22240R_133_0

theorem c22240R_134_28 : rowsJ2 134 135 83 340 ≤ 632979104983610 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3877 rows22240R_3878 (by norm_num)

theorem c22240R_134_27 : rowsJ2 134 135 80 340 ≤ 638842821479664 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3876 c22240R_134_28 (by norm_num)

theorem c22240R_134_26 : rowsJ2 134 135 78 340 ≤ 642485979862190 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3875 c22240R_134_27 (by norm_num)

theorem c22240R_134_25 : rowsJ2 134 135 76 340 ≤ 647945516197804 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3874 c22240R_134_26 (by norm_num)

theorem c22240R_134_24 : rowsJ2 134 135 75 340 ≤ 651471917319998 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3873 c22240R_134_25 (by norm_num)

theorem c22240R_134_23 : rowsJ2 134 135 74 340 ≤ 655602339023359 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3872 c22240R_134_24 (by norm_num)

theorem c22240R_134_22 : rowsJ2 134 135 73 340 ≤ 660376128595363 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3871 c22240R_134_23 (by norm_num)

theorem c22240R_134_21 : rowsJ2 134 135 72 340 ≤ 665856408371877 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3870 c22240R_134_22 (by norm_num)

theorem c22240R_134_20 : rowsJ2 134 135 71 340 ≤ 672085423144760 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3869 c22240R_134_21 (by norm_num)

theorem c22240R_134_19 : rowsJ2 134 135 70 340 ≤ 679129061978928 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3868 c22240R_134_20 (by norm_num)

theorem c22240R_134_18 : rowsJ2 134 135 69 340 ≤ 687032788365611 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3867 c22240R_134_19 (by norm_num)

theorem c22240R_134_17 : rowsJ2 134 135 68 340 ≤ 695865600378184 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3866 c22240R_134_18 (by norm_num)

theorem c22240R_134_16 : rowsJ2 134 135 67 340 ≤ 705676533154305 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3865 c22240R_134_17 (by norm_num)

theorem c22240R_134_15 : rowsJ2 134 135 66 340 ≤ 716538088887398 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3864 c22240R_134_16 (by norm_num)

theorem c22240R_134_14 : rowsJ2 134 135 65 340 ≤ 726861713977183 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3863 c22240R_134_15 (by norm_num)

theorem c22240R_134_13 : rowsJ2 134 135 64 340 ≤ 736600396497715 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3862 c22240R_134_14 (by norm_num)

theorem c22240R_134_12 : rowsJ2 134 135 63 340 ≤ 745686467749525 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3861 c22240R_134_13 (by norm_num)

theorem c22240R_134_11 : rowsJ2 134 135 62 340 ≤ 754073807089171 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3860 c22240R_134_12 (by norm_num)

theorem c22240R_134_10 : rowsJ2 134 135 61 340 ≤ 761695720158020 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3859 c22240R_134_11 (by norm_num)

theorem c22240R_134_9 : rowsJ2 134 135 60 340 ≤ 768506675542999 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3858 c22240R_134_10 (by norm_num)

theorem c22240R_134_8 : rowsJ2 134 135 59 340 ≤ 774524004232842 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3857 c22240R_134_9 (by norm_num)

theorem c22240R_134_7 : rowsJ2 134 135 58 340 ≤ 779787306917856 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3856 c22240R_134_8 (by norm_num)

theorem c22240R_134_6 : rowsJ2 134 135 57 340 ≤ 784337867799035 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3855 c22240R_134_7 (by norm_num)

theorem c22240R_134_5 : rowsJ2 134 135 56 340 ≤ 788218742784228 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3854 c22240R_134_6 (by norm_num)

theorem c22240R_134_4 : rowsJ2 134 135 54 340 ≤ 794153237599779 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3853 c22240R_134_5 (by norm_num)

theorem c22240R_134_3 : rowsJ2 134 135 51 340 ≤ 799224196485303 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3852 c22240R_134_4 (by norm_num)

theorem c22240R_134_2 : rowsJ2 134 135 30 340 ≤ 802472230649478 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3851 c22240R_134_3 (by norm_num)

theorem c22240R_134_1 : rowsJ2 134 135 24 340 ≤ 816587200815310 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3850 c22240R_134_2 (by norm_num)

theorem c22240R_134_0 : rowsJ2 134 135 0 340 ≤ 820168709637735 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22240R_3849 c22240R_134_1 (by norm_num)

theorem hr22240R_134 : rows2 134 135 ≤ 820168709637735 := rows2_le_of_rowsJ2 134 135 c22240R_134_0

theorem c22240R_135_28 : rowsJ2 135 136 83 340 ≤ 548410984113934 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3907 rows22240R_3908 (by norm_num)

theorem c22240R_135_27 : rowsJ2 135 136 80 340 ≤ 554043227851814 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3906 c22240R_135_28 (by norm_num)

theorem c22240R_135_26 : rowsJ2 135 136 78 340 ≤ 557437382596763 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3905 c22240R_135_27 (by norm_num)

theorem c22240R_135_25 : rowsJ2 135 136 76 340 ≤ 562649550627645 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3904 c22240R_135_26 (by norm_num)

theorem c22240R_135_24 : rowsJ2 135 136 75 340 ≤ 566052966052666 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3903 c22240R_135_25 (by norm_num)

theorem c22240R_135_23 : rowsJ2 135 136 74 340 ≤ 570060862695474 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3902 c22240R_135_24 (by norm_num)

theorem c22240R_135_22 : rowsJ2 135 136 73 340 ≤ 574712679156187 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3901 c22240R_135_23 (by norm_num)

theorem c22240R_135_21 : rowsJ2 135 136 72 340 ≤ 580071499824437 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3900 c22240R_135_22 (by norm_num)

theorem c22240R_135_20 : rowsJ2 135 136 71 340 ≤ 586179652957955 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3899 c22240R_135_21 (by norm_num)

theorem c22240R_135_19 : rowsJ2 135 136 70 340 ≤ 593102982694442 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3898 c22240R_135_20 (by norm_num)

theorem c22240R_135_18 : rowsJ2 135 136 69 340 ≤ 600887038184690 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3897 c22240R_135_19 (by norm_num)

theorem c22240R_135_17 : rowsJ2 135 136 68 340 ≤ 609600774882833 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3896 c22240R_135_18 (by norm_num)

theorem c22240R_135_16 : rowsJ2 135 136 67 340 ≤ 619293310885678 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3895 c22240R_135_17 (by norm_num)

theorem c22240R_135_15 : rowsJ2 135 136 66 340 ≤ 630037098137412 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3894 c22240R_135_16 (by norm_num)

theorem c22240R_135_14 : rowsJ2 135 136 65 340 ≤ 641032216126277 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3893 c22240R_135_15 (by norm_num)

theorem c22240R_135_13 : rowsJ2 135 136 64 340 ≤ 651409606530522 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3892 c22240R_135_14 (by norm_num)

theorem c22240R_135_12 : rowsJ2 135 136 63 340 ≤ 661102104812386 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3891 c22240R_135_13 (by norm_num)

theorem c22240R_135_11 : rowsJ2 135 136 62 340 ≤ 670063953113418 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3890 c22240R_135_12 (by norm_num)

theorem c22240R_135_10 : rowsJ2 135 136 61 340 ≤ 678228908220590 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3889 c22240R_135_11 (by norm_num)

theorem c22240R_135_9 : rowsJ2 135 136 60 340 ≤ 685551751239059 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3888 c22240R_135_10 (by norm_num)

theorem c22240R_135_8 : rowsJ2 135 136 59 340 ≤ 692049713826344 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3887 c22240R_135_9 (by norm_num)

theorem c22240R_135_7 : rowsJ2 135 136 58 340 ≤ 697762147825397 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3886 c22240R_135_8 (by norm_num)

theorem c22240R_135_6 : rowsJ2 135 136 57 340 ≤ 702730048090629 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3885 c22240R_135_7 (by norm_num)

theorem c22240R_135_5 : rowsJ2 135 136 56 340 ≤ 706996152048763 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3884 c22240R_135_6 (by norm_num)

theorem c22240R_135_4 : rowsJ2 135 136 54 340 ≤ 713603314816301 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3883 c22240R_135_5 (by norm_num)

theorem c22240R_135_3 : rowsJ2 135 136 51 340 ≤ 719432438701831 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3882 c22240R_135_4 (by norm_num)

theorem c22240R_135_2 : rowsJ2 135 136 31 340 ≤ 722107262858877 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3881 c22240R_135_3 (by norm_num)

theorem c22240R_135_1 : rowsJ2 135 136 24 340 ≤ 733677159211574 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3880 c22240R_135_2 (by norm_num)

theorem c22240R_135_0 : rowsJ2 135 136 0 340 ≤ 738086793573659 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22240R_3879 c22240R_135_1 (by norm_num)

theorem hr22240R_135 : rows2 135 136 ≤ 738086793573659 := rows2_le_of_rowsJ2 135 136 c22240R_135_0

theorem c22240R_136_27 : rowsJ2 136 137 82 340 ≤ 551291959407410 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3936 rows22240R_3937 (by norm_num)

theorem c22240R_136_26 : rowsJ2 136 137 79 340 ≤ 555389165243821 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3935 c22240R_136_27 (by norm_num)

theorem c22240R_136_25 : rowsJ2 136 137 77 340 ≤ 559351622164057 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3934 c22240R_136_26 (by norm_num)

theorem c22240R_136_24 : rowsJ2 136 137 75 340 ≤ 565322602582301 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3933 c22240R_136_25 (by norm_num)

theorem c22240R_136_23 : rowsJ2 136 137 74 340 ≤ 569185363744654 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3932 c22240R_136_24 (by norm_num)

theorem c22240R_136_22 : rowsJ2 136 137 73 340 ≤ 573692705949192 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3931 c22240R_136_23 (by norm_num)

theorem c22240R_136_21 : rowsJ2 136 137 72 340 ≤ 578907677315128 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3930 c22240R_136_22 (by norm_num)

theorem c22240R_136_20 : rowsJ2 136 137 71 340 ≤ 584872694855382 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3929 c22240R_136_21 (by norm_num)

theorem c22240R_136_19 : rowsJ2 136 137 70 340 ≤ 591653559144326 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3928 c22240R_136_20 (by norm_num)

theorem c22240R_136_18 : rowsJ2 136 137 69 340 ≤ 599295901114305 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3927 c22240R_136_19 (by norm_num)

theorem c22240R_136_17 : rowsJ2 136 137 68 340 ≤ 607868635290919 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3926 c22240R_136_18 (by norm_num)

theorem c22240R_136_16 : rowsJ2 136 137 67 340 ≤ 617420964050139 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3925 c22240R_136_17 (by norm_num)

theorem c22240R_136_15 : rowsJ2 136 137 66 340 ≤ 628025296161881 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3924 c22240R_136_16 (by norm_num)

theorem c22240R_136_14 : rowsJ2 136 137 65 340 ≤ 639734799988141 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3923 c22240R_136_15 (by norm_num)

theorem c22240R_136_13 : rowsJ2 136 137 64 340 ≤ 650793410524446 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3922 c22240R_136_14 (by norm_num)

theorem c22240R_136_12 : rowsJ2 136 137 63 340 ≤ 661134490017990 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3921 c22240R_136_13 (by norm_num)

theorem c22240R_136_11 : rowsJ2 136 137 62 340 ≤ 670712663118021 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3920 c22240R_136_12 (by norm_num)

theorem c22240R_136_10 : rowsJ2 136 137 61 340 ≤ 679462162916652 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3919 c22240R_136_11 (by norm_num)

theorem c22240R_136_9 : rowsJ2 136 137 60 340 ≤ 687338100022807 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3918 c22240R_136_10 (by norm_num)

theorem c22240R_136_8 : rowsJ2 136 137 59 340 ≤ 694357623423357 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3917 c22240R_136_9 (by norm_num)

theorem c22240R_136_7 : rowsJ2 136 137 58 340 ≤ 700559857415633 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3916 c22240R_136_8 (by norm_num)

theorem c22240R_136_6 : rowsJ2 136 137 57 340 ≤ 705985527337345 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3915 c22240R_136_7 (by norm_num)

theorem c22240R_136_5 : rowsJ2 136 137 56 340 ≤ 710677078069658 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3914 c22240R_136_6 (by norm_num)

theorem c22240R_136_4 : rowsJ2 136 137 54 340 ≤ 718036774112917 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3913 c22240R_136_5 (by norm_num)

theorem c22240R_136_3 : rowsJ2 136 137 52 340 ≤ 723017090020844 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3912 c22240R_136_4 (by norm_num)

theorem c22240R_136_2 : rowsJ2 136 137 33 340 ≤ 728066076600317 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3911 c22240R_136_3 (by norm_num)

theorem c22240R_136_1 : rowsJ2 136 137 24 340 ≤ 736662638434134 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3910 c22240R_136_2 (by norm_num)

theorem c22240R_136_0 : rowsJ2 136 137 0 340 ≤ 742188259905695 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22240R_3909 c22240R_136_1 (by norm_num)

theorem hr22240R_136 : rows2 136 137 ≤ 742188259905695 := rows2_le_of_rowsJ2 136 137 c22240R_136_0

theorem c22240R_137_26 : rowsJ2 137 138 80 340 ≤ 627678181748489 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3964 rows22240R_3965 (by norm_num)

theorem c22240R_137_25 : rowsJ2 137 138 77 340 ≤ 632409127506000 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3963 c22240R_137_26 (by norm_num)

theorem c22240R_137_24 : rowsJ2 137 138 75 340 ≤ 637984289924712 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3962 c22240R_137_25 (by norm_num)

theorem c22240R_137_23 : rowsJ2 137 138 74 340 ≤ 641649826571952 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3961 c22240R_137_24 (by norm_num)

theorem c22240R_137_22 : rowsJ2 137 138 73 340 ≤ 645960470195045 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3960 c22240R_137_23 (by norm_num)

theorem c22240R_137_21 : rowsJ2 137 138 72 340 ≤ 650979229831561 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3959 c22240R_137_22 (by norm_num)

theorem c22240R_137_20 : rowsJ2 137 138 71 340 ≤ 656748607858709 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3958 c22240R_137_21 (by norm_num)

theorem c22240R_137_19 : rowsJ2 137 138 70 340 ≤ 663334363095446 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3957 c22240R_137_20 (by norm_num)

theorem c22240R_137_18 : rowsJ2 137 138 69 340 ≤ 670782204365927 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3956 c22240R_137_19 (by norm_num)

theorem c22240R_137_17 : rowsJ2 137 138 68 340 ≤ 679160997655642 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3955 c22240R_137_18 (by norm_num)

theorem c22240R_137_16 : rowsJ2 137 138 67 340 ≤ 688520025834978 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3954 c22240R_137_17 (by norm_num)

theorem c22240R_137_15 : rowsJ2 137 138 66 340 ≤ 698931651842162 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3953 c22240R_137_16 (by norm_num)

theorem c22240R_137_14 : rowsJ2 137 138 65 340 ≤ 710449122235135 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3952 c22240R_137_15 (by norm_num)

theorem c22240R_137_13 : rowsJ2 137 138 64 340 ≤ 722199925434042 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3951 c22240R_137_14 (by norm_num)

theorem c22240R_137_12 : rowsJ2 137 138 63 340 ≤ 733199880191869 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3950 c22240R_137_13 (by norm_num)

theorem c22240R_137_11 : rowsJ2 137 138 62 340 ≤ 743404001684920 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3949 c22240R_137_12 (by norm_num)

theorem c22240R_137_10 : rowsJ2 137 138 61 340 ≤ 752747022419888 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3948 c22240R_137_11 (by norm_num)

theorem c22240R_137_9 : rowsJ2 137 138 60 340 ≤ 761184393706082 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3947 c22240R_137_10 (by norm_num)

theorem c22240R_137_8 : rowsJ2 137 138 59 340 ≤ 768733204906902 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3946 c22240R_137_9 (by norm_num)

theorem c22240R_137_7 : rowsJ2 137 138 58 340 ≤ 775432355140302 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3945 c22240R_137_8 (by norm_num)

theorem c22240R_137_6 : rowsJ2 137 138 57 340 ≤ 781322324706790 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3944 c22240R_137_7 (by norm_num)

theorem c22240R_137_5 : rowsJ2 137 138 56 340 ≤ 786445270177829 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3943 c22240R_137_6 (by norm_num)

theorem c22240R_137_4 : rowsJ2 137 138 54 340 ≤ 794567738256366 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3942 c22240R_137_5 (by norm_num)

theorem c22240R_137_3 : rowsJ2 137 138 52 340 ≤ 800174884864264 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3941 c22240R_137_4 (by norm_num)

theorem c22240R_137_2 : rowsJ2 137 138 36 340 ≤ 806288561828511 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3940 c22240R_137_3 (by norm_num)

theorem c22240R_137_1 : rowsJ2 137 138 24 340 ≤ 812358407998256 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3939 c22240R_137_2 (by norm_num)

theorem c22240R_137_0 : rowsJ2 137 138 0 340 ≤ 818117537236869 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22240R_3938 c22240R_137_1 (by norm_num)

theorem hr22240R_137 : rows2 137 138 ≤ 818117537236869 := rows2_le_of_rowsJ2 137 138 c22240R_137_0

theorem c22240R_138_26 : rowsJ2 138 139 78 340 ≤ 784440376293900 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3992 rows22240R_3993 (by norm_num)

theorem c22240R_138_25 : rowsJ2 138 139 76 340 ≤ 788544271215058 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3991 c22240R_138_26 (by norm_num)

theorem c22240R_138_24 : rowsJ2 138 139 74 340 ≤ 794831096185737 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3990 c22240R_138_25 (by norm_num)

theorem c22240R_138_23 : rowsJ2 138 139 73 340 ≤ 798923295569102 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3989 c22240R_138_24 (by norm_num)

theorem c22240R_138_22 : rowsJ2 138 139 72 340 ≤ 803724218610647 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3988 c22240R_138_23 (by norm_num)

theorem c22240R_138_21 : rowsJ2 138 139 71 340 ≤ 809276453723638 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3987 c22240R_138_22 (by norm_num)

theorem c22240R_138_20 : rowsJ2 138 139 70 340 ≤ 815645719917409 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3986 c22240R_138_21 (by norm_num)

theorem c22240R_138_19 : rowsJ2 138 139 69 340 ≤ 822877809351520 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3985 c22240R_138_20 (by norm_num)

theorem c22240R_138_18 : rowsJ2 138 139 68 340 ≤ 831041541033213 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3984 c22240R_138_19 (by norm_num)

theorem c22240R_138_17 : rowsJ2 138 139 67 340 ≤ 840186274696193 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3983 c22240R_138_18 (by norm_num)

theorem c22240R_138_16 : rowsJ2 138 139 66 340 ≤ 850384329346816 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3982 c22240R_138_17 (by norm_num)

theorem c22240R_138_15 : rowsJ2 138 139 65 340 ≤ 861689031369916 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3981 c22240R_138_16 (by norm_num)

theorem c22240R_138_14 : rowsJ2 138 139 64 340 ≤ 874176624565046 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3980 c22240R_138_15 (by norm_num)

theorem c22240R_138_13 : rowsJ2 138 139 63 340 ≤ 885879640858622 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3979 c22240R_138_14 (by norm_num)

theorem c22240R_138_12 : rowsJ2 138 139 62 340 ≤ 896753505899970 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3978 c22240R_138_13 (by norm_num)

theorem c22240R_138_11 : rowsJ2 138 139 61 340 ≤ 906733473422423 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3977 c22240R_138_12 (by norm_num)

theorem c22240R_138_10 : rowsJ2 138 139 60 340 ≤ 915775356520808 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3976 c22240R_138_11 (by norm_num)

theorem c22240R_138_9 : rowsJ2 138 139 59 340 ≤ 923896213126807 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3975 c22240R_138_10 (by norm_num)

theorem c22240R_138_8 : rowsJ2 138 139 58 340 ≤ 931134738147911 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3974 c22240R_138_9 (by norm_num)

theorem c22240R_138_7 : rowsJ2 138 139 57 340 ≤ 937531184843091 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3973 c22240R_138_8 (by norm_num)

theorem c22240R_138_6 : rowsJ2 138 139 56 340 ≤ 943127443132255 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3972 c22240R_138_7 (by norm_num)

theorem c22240R_138_5 : rowsJ2 138 139 55 340 ≤ 947967159418886 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3971 c22240R_138_6 (by norm_num)

theorem c22240R_138_4 : rowsJ2 138 139 54 340 ≤ 952095830317082 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3970 c22240R_138_5 (by norm_num)

theorem c22240R_138_3 : rowsJ2 138 139 52 340 ≤ 958412178124526 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3969 c22240R_138_4 (by norm_num)

theorem c22240R_138_2 : rowsJ2 138 139 46 340 ≤ 965716391643828 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3968 c22240R_138_3 (by norm_num)

theorem c22240R_138_1 : rowsJ2 138 139 24 340 ≤ 969939077493596 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3967 c22240R_138_2 (by norm_num)

theorem c22240R_138_0 : rowsJ2 138 139 0 340 ≤ 976198480074982 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22240R_3966 c22240R_138_1 (by norm_num)

theorem hr22240R_138 : rows2 138 139 ≤ 976198480074982 := rows2_le_of_rowsJ2 138 139 c22240R_138_0

theorem c22240R_139_26 : rowsJ2 139 140 79 340 ≤ 846041917566094 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_4020 rows22240R_4021 (by norm_num)

theorem c22240R_139_25 : rowsJ2 139 140 76 340 ≤ 850915179102853 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_4019 c22240R_139_26 (by norm_num)

theorem c22240R_139_24 : rowsJ2 139 140 74 340 ≤ 856681416633529 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_4018 c22240R_139_25 (by norm_num)

theorem c22240R_139_23 : rowsJ2 139 140 73 340 ≤ 860502989096842 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_4017 c22240R_139_24 (by norm_num)

theorem c22240R_139_22 : rowsJ2 139 140 72 340 ≤ 865033764240055 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_4016 c22240R_139_23 (by norm_num)

theorem c22240R_139_21 : rowsJ2 139 140 71 340 ≤ 870316407926543 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_4015 c22240R_139_22 (by norm_num)

theorem c22240R_139_20 : rowsJ2 139 140 70 340 ≤ 876416596204974 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_4014 c22240R_139_21 (by norm_num)

theorem c22240R_139_19 : rowsJ2 139 140 69 340 ≤ 883380201388980 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_4013 c22240R_139_20 (by norm_num)

theorem c22240R_139_18 : rowsJ2 139 140 68 340 ≤ 891275997084466 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_4012 c22240R_139_19 (by norm_num)

theorem c22240R_139_17 : rowsJ2 139 140 67 340 ≤ 900153415925257 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_4011 c22240R_139_18 (by norm_num)

theorem c22240R_139_16 : rowsJ2 139 140 66 340 ≤ 910084725346252 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_4010 c22240R_139_17 (by norm_num)

theorem c22240R_139_15 : rowsJ2 139 140 65 340 ≤ 921123327557571 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_4009 c22240R_139_16 (by norm_num)

theorem c22240R_139_14 : rowsJ2 139 140 64 340 ≤ 933345417657712 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_4008 c22240R_139_15 (by norm_num)

theorem c22240R_139_13 : rowsJ2 139 140 63 340 ≤ 945763168177546 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_4007 c22240R_139_14 (by norm_num)

theorem c22240R_139_12 : rowsJ2 139 140 62 340 ≤ 957317729165754 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_4006 c22240R_139_13 (by norm_num)

theorem c22240R_139_11 : rowsJ2 139 140 61 340 ≤ 967944879047158 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_4005 c22240R_139_12 (by norm_num)

theorem c22240R_139_10 : rowsJ2 139 140 60 340 ≤ 977600819211549 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_4004 c22240R_139_11 (by norm_num)

theorem c22240R_139_9 : rowsJ2 139 140 59 340 ≤ 986302584317832 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_4003 c22240R_139_10 (by norm_num)

theorem c22240R_139_8 : rowsJ2 139 140 58 340 ≤ 994088697624580 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_4002 c22240R_139_9 (by norm_num)

theorem c22240R_139_7 : rowsJ2 139 140 57 340 ≤ 1000999190423790 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_4001 c22240R_139_8 (by norm_num)

theorem c22240R_139_6 : rowsJ2 139 140 56 340 ≤ 1007075707442698 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_4000 c22240R_139_7 (by norm_num)

theorem c22240R_139_5 : rowsJ2 139 140 55 340 ≤ 1012361608712867 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_3999 c22240R_139_6 (by norm_num)

theorem c22240R_139_4 : rowsJ2 139 140 54 340 ≤ 1016902076890518 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_3998 c22240R_139_5 (by norm_num)

theorem c22240R_139_3 : rowsJ2 139 140 52 340 ≤ 1023937367007154 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_3997 c22240R_139_4 (by norm_num)

theorem c22240R_139_2 : rowsJ2 139 140 47 340 ≤ 1032056429996332 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_3996 c22240R_139_3 (by norm_num)

theorem c22240R_139_1 : rowsJ2 139 140 24 340 ≤ 1035335320931981 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_3995 c22240R_139_2 (by norm_num)

theorem c22240R_139_0 : rowsJ2 139 140 0 340 ≤ 1041289191102006 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22240R_3994 c22240R_139_1 (by norm_num)

theorem hr22240R_139 : rows2 139 140 ≤ 1041289191102006 := rows2_le_of_rowsJ2 139 140 c22240R_139_0

theorem c22240R_140_25 : rowsJ2 140 141 77 340 ≤ 995282373418944 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4047 rows22240R_4048 (by norm_num)

theorem c22240R_140_24 : rowsJ2 140 141 75 340 ≤ 999511088312648 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4046 c22240R_140_25 (by norm_num)

theorem c22240R_140_23 : rowsJ2 140 141 73 340 ≤ 1005989606596858 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4045 c22240R_140_24 (by norm_num)

theorem c22240R_140_22 : rowsJ2 140 141 72 340 ≤ 1010229298975105 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4044 c22240R_140_23 (by norm_num)

theorem c22240R_140_21 : rowsJ2 140 141 71 340 ≤ 1015221553207737 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4043 c22240R_140_22 (by norm_num)

theorem c22240R_140_20 : rowsJ2 140 141 70 340 ≤ 1021031999056424 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4042 c22240R_140_21 (by norm_num)

theorem c22240R_140_19 : rowsJ2 140 141 69 340 ≤ 1027706589713431 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4041 c22240R_140_20 (by norm_num)

theorem c22240R_140_18 : rowsJ2 140 141 68 340 ≤ 1035314055699194 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4040 c22240R_140_19 (by norm_num)

theorem c22240R_140_17 : rowsJ2 140 141 67 340 ≤ 1043903908296575 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4039 c22240R_140_18 (by norm_num)

theorem c22240R_140_16 : rowsJ2 140 141 66 340 ≤ 1053548364926523 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4038 c22240R_140_17 (by norm_num)

theorem c22240R_140_15 : rowsJ2 140 141 65 340 ≤ 1064300900637754 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4037 c22240R_140_16 (by norm_num)

theorem c22240R_140_14 : rowsJ2 140 141 64 340 ≤ 1076237663839918 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4036 c22240R_140_15 (by norm_num)

theorem c22240R_140_13 : rowsJ2 140 141 63 340 ≤ 1089416540487307 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4035 c22240R_140_14 (by norm_num)

theorem c22240R_140_12 : rowsJ2 140 141 62 340 ≤ 1101697743237013 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4034 c22240R_140_13 (by norm_num)

theorem c22240R_140_11 : rowsJ2 140 141 61 340 ≤ 1113017599833072 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4033 c22240R_140_12 (by norm_num)

theorem c22240R_140_10 : rowsJ2 140 141 60 340 ≤ 1123332719117584 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4032 c22240R_140_11 (by norm_num)

theorem c22240R_140_9 : rowsJ2 140 141 59 340 ≤ 1132660138121470 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4031 c22240R_140_10 (by norm_num)

theorem c22240R_140_8 : rowsJ2 140 141 58 340 ≤ 1141038232448967 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4030 c22240R_140_9 (by norm_num)

theorem c22240R_140_7 : rowsJ2 140 141 57 340 ≤ 1148506841904293 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4029 c22240R_140_8 (by norm_num)

theorem c22240R_140_6 : rowsJ2 140 141 56 340 ≤ 1155107386915300 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4028 c22240R_140_7 (by norm_num)

theorem c22240R_140_5 : rowsJ2 140 141 55 340 ≤ 1160882960028439 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4027 c22240R_140_6 (by norm_num)

theorem c22240R_140_4 : rowsJ2 140 141 54 340 ≤ 1165878452997060 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4026 c22240R_140_5 (by norm_num)

theorem c22240R_140_3 : rowsJ2 140 141 52 340 ≤ 1173718453614651 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4025 c22240R_140_4 (by norm_num)

theorem c22240R_140_2 : rowsJ2 140 141 48 340 ≤ 1182242814481972 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4024 c22240R_140_3 (by norm_num)

theorem c22240R_140_1 : rowsJ2 140 141 24 340 ≤ 1185755241033342 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4023 c22240R_140_2 (by norm_num)

theorem c22240R_140_0 : rowsJ2 140 141 0 340 ≤ 1191656163540230 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22240R_4022 c22240R_140_1 (by norm_num)

theorem hr22240R_140 : rows2 140 141 ≤ 1191656163540230 := rows2_le_of_rowsJ2 140 141 c22240R_140_0

theorem c22240R_141_26 : rowsJ2 141 142 78 340 ≤ 1047002099832235 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4075 rows22240R_4076 (by norm_num)

theorem c22240R_141_25 : rowsJ2 141 142 75 340 ≤ 1052024944689263 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4074 c22240R_141_26 (by norm_num)

theorem c22240R_141_24 : rowsJ2 141 142 73 340 ≤ 1057968564569419 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4073 c22240R_141_25 (by norm_num)

theorem c22240R_141_23 : rowsJ2 141 142 72 340 ≤ 1061907937316448 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4072 c22240R_141_24 (by norm_num)

theorem c22240R_141_22 : rowsJ2 141 142 71 340 ≤ 1066578615633984 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4071 c22240R_141_23 (by norm_num)

theorem c22240R_141_21 : rowsJ2 141 142 70 340 ≤ 1072046692059744 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4070 c22240R_141_22 (by norm_num)

theorem c22240R_141_20 : rowsJ2 141 142 69 340 ≤ 1078379501743651 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4069 c22240R_141_21 (by norm_num)

theorem c22240R_141_19 : rowsJ2 141 142 68 340 ≤ 1085645728796957 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4068 c22240R_141_20 (by norm_num)

theorem c22240R_141_18 : rowsJ2 141 142 67 340 ≤ 1093894959889831 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4067 c22240R_141_19 (by norm_num)

theorem c22240R_141_17 : rowsJ2 141 142 66 340 ≤ 1103199363898635 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4066 c22240R_141_18 (by norm_num)

theorem c22240R_141_16 : rowsJ2 141 142 65 340 ≤ 1113612484437011 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4065 c22240R_141_17 (by norm_num)

theorem c22240R_141_15 : rowsJ2 141 142 64 340 ≤ 1125210415640603 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4064 c22240R_141_16 (by norm_num)

theorem c22240R_141_14 : rowsJ2 141 142 63 340 ≤ 1138051115487854 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4063 c22240R_141_15 (by norm_num)

theorem c22240R_141_13 : rowsJ2 141 142 62 340 ≤ 1151071374337503 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4062 c22240R_141_14 (by norm_num)

theorem c22240R_141_12 : rowsJ2 141 142 61 340 ≤ 1163095583078900 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4061 c22240R_141_13 (by norm_num)

theorem c22240R_141_11 : rowsJ2 141 142 60 340 ≤ 1174080766929251 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4060 c22240R_141_12 (by norm_num)

theorem c22240R_141_10 : rowsJ2 141 142 59 340 ≤ 1184043990311622 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4059 c22240R_141_11 (by norm_num)

theorem c22240R_141_9 : rowsJ2 141 142 58 340 ≤ 1193023492108213 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4058 c22240R_141_10 (by norm_num)

theorem c22240R_141_8 : rowsJ2 141 142 57 340 ≤ 1201058948027589 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4057 c22240R_141_9 (by norm_num)

theorem c22240R_141_7 : rowsJ2 141 142 56 340 ≤ 1208191568415312 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4056 c22240R_141_8 (by norm_num)

theorem c22240R_141_6 : rowsJ2 141 142 55 340 ≤ 1214464202446301 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4055 c22240R_141_7 (by norm_num)

theorem c22240R_141_5 : rowsJ2 141 142 54 340 ≤ 1219921453625650 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4054 c22240R_141_6 (by norm_num)

theorem c22240R_141_4 : rowsJ2 141 142 53 340 ≤ 1224609801369937 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4053 c22240R_141_5 (by norm_num)

theorem c22240R_141_3 : rowsJ2 141 142 51 340 ≤ 1231875941260981 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4052 c22240R_141_4 (by norm_num)

theorem c22240R_141_2 : rowsJ2 141 142 48 340 ≤ 1238294154370191 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4051 c22240R_141_3 (by norm_num)

theorem c22240R_141_1 : rowsJ2 141 142 24 340 ≤ 1241690392490710 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4050 c22240R_141_2 (by norm_num)

theorem c22240R_141_0 : rowsJ2 141 142 0 340 ≤ 1246823702982472 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22240R_4049 c22240R_141_1 (by norm_num)

theorem hr22240R_141 : rows2 141 142 ≤ 1246823702982472 := rows2_le_of_rowsJ2 141 142 c22240R_141_0

theorem c22240R_142_25 : rowsJ2 142 143 76 340 ≤ 1188948638837184 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4102 rows22240R_4103 (by norm_num)

theorem c22240R_142_24 : rowsJ2 142 143 74 340 ≤ 1193308530296001 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4101 c22240R_142_25 (by norm_num)

theorem c22240R_142_23 : rowsJ2 142 143 72 340 ≤ 1199988400685857 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4100 c22240R_142_24 (by norm_num)

theorem c22240R_142_22 : rowsJ2 142 143 71 340 ≤ 1204360130661732 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4099 c22240R_142_23 (by norm_num)

theorem c22240R_142_21 : rowsJ2 142 143 70 340 ≤ 1209508129014978 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4098 c22240R_142_22 (by norm_num)

theorem c22240R_142_20 : rowsJ2 142 143 69 340 ≤ 1215500196057672 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4097 c22240R_142_21 (by norm_num)

theorem c22240R_142_19 : rowsJ2 142 143 68 340 ≤ 1222405461688023 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4096 c22240R_142_20 (by norm_num)

theorem c22240R_142_18 : rowsJ2 142 143 67 340 ≤ 1230294496828119 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4095 c22240R_142_19 (by norm_num)

theorem c22240R_142_17 : rowsJ2 142 143 66 340 ≤ 1239239424361460 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4094 c22240R_142_18 (by norm_num)

theorem c22240R_142_16 : rowsJ2 142 143 65 340 ≤ 1249293862557024 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4093 c22240R_142_17 (by norm_num)

theorem c22240R_142_15 : rowsJ2 142 143 64 340 ≤ 1260533853077822 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4092 c22240R_142_16 (by norm_num)

theorem c22240R_142_14 : rowsJ2 142 143 63 340 ≤ 1273017423255359 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4091 c22240R_142_15 (by norm_num)

theorem c22240R_142_13 : rowsJ2 142 143 62 340 ≤ 1286825029315890 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4090 c22240R_142_14 (by norm_num)

theorem c22240R_142_12 : rowsJ2 142 143 61 340 ≤ 1299601391356354 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4089 c22240R_142_13 (by norm_num)

theorem c22240R_142_11 : rowsJ2 142 143 60 340 ≤ 1311303984194854 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4088 c22240R_142_12 (by norm_num)

theorem c22240R_142_10 : rowsJ2 142 143 59 340 ≤ 1321949926081515 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4087 c22240R_142_11 (by norm_num)

theorem c22240R_142_9 : rowsJ2 142 143 58 340 ≤ 1331577342068219 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4086 c22240R_142_10 (by norm_num)

theorem c22240R_142_8 : rowsJ2 142 143 57 340 ≤ 1340225770261290 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4085 c22240R_142_9 (by norm_num)

theorem c22240R_142_7 : rowsJ2 142 143 56 340 ≤ 1347936236481898 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4084 c22240R_142_8 (by norm_num)

theorem c22240R_142_6 : rowsJ2 142 143 55 340 ≤ 1354751377039743 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4083 c22240R_142_7 (by norm_num)

theorem c22240R_142_5 : rowsJ2 142 143 54 340 ≤ 1360715529194715 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4082 c22240R_142_6 (by norm_num)

theorem c22240R_142_4 : rowsJ2 142 143 53 340 ≤ 1365874876392264 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4081 c22240R_142_5 (by norm_num)

theorem c22240R_142_3 : rowsJ2 142 143 51 340 ≤ 1373973903093914 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4080 c22240R_142_4 (by norm_num)

theorem c22240R_142_2 : rowsJ2 142 143 48 340 ≤ 1381362308595488 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4079 c22240R_142_3 (by norm_num)

theorem c22240R_142_1 : rowsJ2 142 143 24 340 ≤ 1385183883862569 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4078 c22240R_142_2 (by norm_num)

theorem c22240R_142_0 : rowsJ2 142 143 0 340 ≤ 1389796701216074 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22240R_4077 c22240R_142_1 (by norm_num)

theorem hr22240R_142 : rows2 142 143 ≤ 1389796701216074 := rows2_le_of_rowsJ2 142 143 c22240R_142_0

theorem c22240R_143_24 : rowsJ2 143 144 75 340 ≤ 1233089852982728 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4128 rows22240R_4129 (by norm_num)

theorem c22240R_143_23 : rowsJ2 143 144 73 340 ≤ 1238042047562237 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4127 c22240R_143_24 (by norm_num)

theorem c22240R_143_22 : rowsJ2 143 144 71 340 ≤ 1245480874786166 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4126 c22240R_143_23 (by norm_num)

theorem c22240R_143_21 : rowsJ2 143 144 70 340 ≤ 1250298492145441 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4125 c22240R_143_22 (by norm_num)

theorem c22240R_143_20 : rowsJ2 143 144 69 340 ≤ 1255938897073732 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4124 c22240R_143_21 (by norm_num)

theorem c22240R_143_19 : rowsJ2 143 144 68 340 ≤ 1262471682312131 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4123 c22240R_143_20 (by norm_num)

theorem c22240R_143_18 : rowsJ2 143 144 67 340 ≤ 1269967862255869 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4122 c22240R_143_19 (by norm_num)

theorem c22240R_143_17 : rowsJ2 143 144 66 340 ≤ 1278499989849859 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4121 c22240R_143_18 (by norm_num)

theorem c22240R_143_16 : rowsJ2 143 144 65 340 ≤ 1288142273364619 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4120 c22240R_143_17 (by norm_num)

theorem c22240R_143_15 : rowsJ2 143 144 64 340 ≤ 1298970703505748 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4119 c22240R_143_16 (by norm_num)

theorem c22240R_143_14 : rowsJ2 143 144 63 340 ≤ 1311043372435677 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4118 c22240R_143_15 (by norm_num)

theorem c22240R_143_13 : rowsJ2 143 144 62 340 ≤ 1324440679877671 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4117 c22240R_143_14 (by norm_num)

theorem c22240R_143_12 : rowsJ2 143 144 61 340 ≤ 1337982402248140 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4116 c22240R_143_13 (by norm_num)

theorem c22240R_143_11 : rowsJ2 143 144 60 340 ≤ 1350414785385248 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4115 c22240R_143_12 (by norm_num)

theorem c22240R_143_10 : rowsJ2 143 144 59 340 ≤ 1361755019350805 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4114 c22240R_143_11 (by norm_num)

theorem c22240R_143_9 : rowsJ2 143 144 58 340 ≤ 1372041146205034 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4113 c22240R_143_10 (by norm_num)

theorem c22240R_143_8 : rowsJ2 143 144 57 340 ≤ 1381312573558525 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4112 c22240R_143_9 (by norm_num)

theorem c22240R_143_7 : rowsJ2 143 144 56 340 ≤ 1389610172355002 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4111 c22240R_143_8 (by norm_num)

theorem c22240R_143_6 : rowsJ2 143 144 55 340 ≤ 1396976374991174 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4110 c22240R_143_7 (by norm_num)

theorem c22240R_143_5 : rowsJ2 143 144 54 340 ≤ 1403455285589630 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4109 c22240R_143_6 (by norm_num)

theorem c22240R_143_4 : rowsJ2 143 144 53 340 ≤ 1409092797886711 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4108 c22240R_143_5 (by norm_num)

theorem c22240R_143_3 : rowsJ2 143 144 51 340 ≤ 1418037038035224 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4107 c22240R_143_4 (by norm_num)

theorem c22240R_143_2 : rowsJ2 143 144 48 340 ≤ 1426409339507364 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4106 c22240R_143_3 (by norm_num)

theorem c22240R_143_1 : rowsJ2 143 144 25 340 ≤ 1430966814776638 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4105 c22240R_143_2 (by norm_num)

theorem c22240R_143_0 : rowsJ2 143 144 0 340 ≤ 1434602513100520 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22240R_4104 c22240R_143_1 (by norm_num)

theorem hr22240R_143 : rows2 143 144 ≤ 1434602513100520 := rows2_le_of_rowsJ2 143 144 c22240R_143_0

theorem c22240R_144_24 : rowsJ2 144 145 76 340 ≤ 1363473768027338 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4154 rows22240R_4155 (by norm_num)

theorem c22240R_144_23 : rowsJ2 144 145 73 340 ≤ 1369486296361449 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4153 c22240R_144_24 (by norm_num)

theorem c22240R_144_22 : rowsJ2 144 145 71 340 ≤ 1376377774154200 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4152 c22240R_144_23 (by norm_num)

theorem c22240R_144_21 : rowsJ2 144 145 70 340 ≤ 1380888232335900 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4151 c22240R_144_22 (by norm_num)

theorem c22240R_144_20 : rowsJ2 144 145 69 340 ≤ 1386199844362394 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4150 c22240R_144_21 (by norm_num)

theorem c22240R_144_19 : rowsJ2 144 145 68 340 ≤ 1392382693351926 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4149 c22240R_144_20 (by norm_num)

theorem c22240R_144_18 : rowsJ2 144 145 67 340 ≤ 1399508259379751 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4148 c22240R_144_19 (by norm_num)

theorem c22240R_144_17 : rowsJ2 144 145 66 340 ≤ 1407649541846880 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4147 c22240R_144_18 (by norm_num)

theorem c22240R_144_16 : rowsJ2 144 145 65 340 ≤ 1416881182238889 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4146 c22240R_144_17 (by norm_num)

theorem c22240R_144_15 : rowsJ2 144 145 64 340 ≤ 1427279587179722 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4145 c22240R_144_16 (by norm_num)

theorem c22240R_144_14 : rowsJ2 144 145 63 340 ≤ 1438923062306581 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4144 c22240R_144_15 (by norm_num)

theorem c22240R_144_13 : rowsJ2 144 145 62 340 ≤ 1451891952776952 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4143 c22240R_144_14 (by norm_num)

theorem c22240R_144_12 : rowsJ2 144 145 61 340 ≤ 1466249333753970 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4142 c22240R_144_13 (by norm_num)

theorem c22240R_144_11 : rowsJ2 144 145 60 340 ≤ 1479461273918501 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4141 c22240R_144_12 (by norm_num)

theorem c22240R_144_10 : rowsJ2 144 145 59 340 ≤ 1491545068130674 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4140 c22240R_144_11 (by norm_num)

theorem c22240R_144_9 : rowsJ2 144 145 58 340 ≤ 1502538710319516 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4139 c22240R_144_10 (by norm_num)

theorem c22240R_144_8 : rowsJ2 144 145 57 340 ≤ 1512481505969437 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4138 c22240R_144_9 (by norm_num)

theorem c22240R_144_7 : rowsJ2 144 145 56 340 ≤ 1521414194339990 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4137 c22240R_144_8 (by norm_num)

theorem c22240R_144_6 : rowsJ2 144 145 55 340 ≤ 1529379031646859 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4136 c22240R_144_7 (by norm_num)

theorem c22240R_144_5 : rowsJ2 144 145 54 340 ≤ 1536419914995468 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4135 c22240R_144_6 (by norm_num)

theorem c22240R_144_4 : rowsJ2 144 145 53 340 ≤ 1542582480066561 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4134 c22240R_144_5 (by norm_num)

theorem c22240R_144_3 : rowsJ2 144 145 51 340 ≤ 1552464819919016 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4133 c22240R_144_4 (by norm_num)

theorem c22240R_144_2 : rowsJ2 144 145 48 340 ≤ 1561958473110813 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4132 c22240R_144_3 (by norm_num)

theorem c22240R_144_1 : rowsJ2 144 145 26 340 ≤ 1567720896353504 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4131 c22240R_144_2 (by norm_num)

theorem c22240R_144_0 : rowsJ2 144 145 0 340 ≤ 1570632859073540 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22240R_4130 c22240R_144_1 (by norm_num)

theorem hr22240R_144 : rows2 144 145 ≤ 1570632859073540 := rows2_le_of_rowsJ2 144 145 c22240R_144_0

theorem c22240R_145_24 : rowsJ2 145 146 74 340 ≤ 1399216493175615 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4180 rows22240R_4181 (by norm_num)

theorem c22240R_145_23 : rowsJ2 145 146 72 340 ≤ 1404326870372429 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4179 c22240R_145_24 (by norm_num)

theorem c22240R_145_22 : rowsJ2 145 146 70 340 ≤ 1412003700154882 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4178 c22240R_145_23 (by norm_num)

theorem c22240R_145_21 : rowsJ2 145 146 69 340 ≤ 1416975734892036 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4177 c22240R_145_22 (by norm_num)

theorem c22240R_145_20 : rowsJ2 145 146 68 340 ≤ 1422797218686874 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4176 c22240R_145_21 (by norm_num)

theorem c22240R_145_19 : rowsJ2 145 146 67 340 ≤ 1429540119771904 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4175 c22240R_145_20 (by norm_num)

theorem c22240R_145_18 : rowsJ2 145 146 66 340 ≤ 1437277901006862 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4174 c22240R_145_19 (by norm_num)

theorem c22240R_145_17 : rowsJ2 145 146 65 340 ≤ 1446085648127947 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4173 c22240R_145_18 (by norm_num)

theorem c22240R_145_16 : rowsJ2 145 146 64 340 ≤ 1456040198805633 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4172 c22240R_145_17 (by norm_num)

theorem c22240R_145_15 : rowsJ2 145 146 63 340 ≤ 1467220272449227 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4171 c22240R_145_16 (by norm_num)

theorem c22240R_145_14 : rowsJ2 145 146 62 340 ≤ 1479706611361922 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4170 c22240R_145_15 (by norm_num)

theorem c22240R_145_13 : rowsJ2 145 146 61 340 ≤ 1493582129086334 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4169 c22240R_145_14 (by norm_num)

theorem c22240R_145_12 : rowsJ2 145 146 60 340 ≤ 1507587678583749 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4168 c22240R_145_13 (by norm_num)

theorem c22240R_145_11 : rowsJ2 145 146 59 340 ≤ 1520428205182003 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4167 c22240R_145_12 (by norm_num)

theorem c22240R_145_10 : rowsJ2 145 146 58 340 ≤ 1532141670594696 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4166 c22240R_145_11 (by norm_num)

theorem c22240R_145_9 : rowsJ2 145 146 57 340 ≤ 1542767316748088 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4165 c22240R_145_10 (by norm_num)

theorem c22240R_145_8 : rowsJ2 145 146 56 340 ≤ 1552345762998617 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4164 c22240R_145_9 (by norm_num)

theorem c22240R_145_7 : rowsJ2 145 146 55 340 ≤ 1560919115895775 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4163 c22240R_145_8 (by norm_num)

theorem c22240R_145_6 : rowsJ2 145 146 54 340 ≤ 1568531076024696 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4162 c22240R_145_7 (by norm_num)

theorem c22240R_145_5 : rowsJ2 145 146 53 340 ≤ 1575227049903525 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4161 c22240R_145_6 (by norm_num)

theorem c22240R_145_4 : rowsJ2 145 146 52 340 ≤ 1581054286688475 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4160 c22240R_145_5 (by norm_num)

theorem c22240R_145_3 : rowsJ2 145 146 50 340 ≤ 1590301646012032 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4159 c22240R_145_4 (by norm_num)

theorem c22240R_145_2 : rowsJ2 145 146 48 340 ≤ 1596693624461844 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4158 c22240R_145_3 (by norm_num)

theorem c22240R_145_1 : rowsJ2 145 146 28 340 ≤ 1603677496244273 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4157 c22240R_145_2 (by norm_num)

theorem c22240R_145_0 : rowsJ2 145 146 0 340 ≤ 1605705324727865 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22240R_4156 c22240R_145_1 (by norm_num)

theorem hr22240R_145 : rows2 145 146 ≤ 1605705324727865 := rows2_le_of_rowsJ2 145 146 c22240R_145_0

theorem c22240R_146_24 : rowsJ2 146 147 75 340 ≤ 1522743405956992 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4206 rows22240R_4207 (by norm_num)

theorem c22240R_146_23 : rowsJ2 146 147 72 340 ≤ 1528949816004795 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4205 c22240R_146_24 (by norm_num)

theorem c22240R_146_22 : rowsJ2 146 147 70 340 ≤ 1536063779930675 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4204 c22240R_146_23 (by norm_num)

theorem c22240R_146_21 : rowsJ2 146 147 69 340 ≤ 1540720075222646 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4203 c22240R_146_22 (by norm_num)

theorem c22240R_146_20 : rowsJ2 146 147 68 340 ≤ 1546203666808368 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4202 c22240R_146_21 (by norm_num)

theorem c22240R_146_19 : rowsJ2 146 147 67 340 ≤ 1552587035084746 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4201 c22240R_146_20 (by norm_num)

theorem c22240R_146_18 : rowsJ2 146 147 66 340 ≤ 1559944134280213 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4200 c22240R_146_19 (by norm_num)

theorem c22240R_146_17 : rowsJ2 146 147 65 340 ≤ 1568350516948814 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4199 c22240R_146_18 (by norm_num)

theorem c22240R_146_16 : rowsJ2 146 147 64 340 ≤ 1577883468541895 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4198 c22240R_146_17 (by norm_num)

theorem c22240R_146_15 : rowsJ2 146 147 63 340 ≤ 1588622143244551 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4197 c22240R_146_16 (by norm_num)

theorem c22240R_146_14 : rowsJ2 146 147 62 340 ≤ 1600647701051314 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4196 c22240R_146_15 (by norm_num)

theorem c22240R_146_13 : rowsJ2 146 147 61 340 ≤ 1614043456768780 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4195 c22240R_146_14 (by norm_num)

theorem c22240R_146_12 : rowsJ2 146 147 60 340 ≤ 1628895036817634 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4194 c22240R_146_13 (by norm_num)

theorem c22240R_146_11 : rowsJ2 146 147 59 340 ≤ 1642544143959231 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4193 c22240R_146_12 (by norm_num)

theorem c22240R_146_10 : rowsJ2 146 147 58 340 ≤ 1655028742528816 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4192 c22240R_146_11 (by norm_num)

theorem c22240R_146_9 : rowsJ2 146 147 57 340 ≤ 1666388043090070 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4191 c22240R_146_10 (by norm_num)

theorem c22240R_146_8 : rowsJ2 146 147 56 340 ≤ 1676662582017956 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4190 c22240R_146_9 (by norm_num)

theorem c22240R_146_7 : rowsJ2 146 147 55 340 ≤ 1685894344350008 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4189 c22240R_146_8 (by norm_num)

theorem c22240R_146_6 : rowsJ2 146 147 54 340 ≤ 1694126859045971 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4188 c22240R_146_7 (by norm_num)

theorem c22240R_146_5 : rowsJ2 146 147 53 340 ≤ 1701405332123205 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4187 c22240R_146_6 (by norm_num)

theorem c22240R_146_4 : rowsJ2 146 147 52 340 ≤ 1707776755287974 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4186 c22240R_146_5 (by norm_num)

theorem c22240R_146_3 : rowsJ2 146 147 50 340 ≤ 1717996323761484 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4185 c22240R_146_4 (by norm_num)

theorem c22240R_146_2 : rowsJ2 146 147 48 340 ≤ 1725203094024065 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4184 c22240R_146_3 (by norm_num)

theorem c22240R_146_1 : rowsJ2 146 147 41 340 ≤ 1733736271270770 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4183 c22240R_146_2 (by norm_num)

theorem c22240R_146_0 : rowsJ2 146 147 0 340 ≤ 1735360195070389 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22240R_4182 c22240R_146_1 (by norm_num)

theorem hr22240R_146 : rows2 146 147 ≤ 1735360195070389 := rows2_le_of_rowsJ2 146 147 c22240R_146_0

theorem c22240R_147_23 : rowsJ2 147 148 73 340 ≤ 1549002657017107 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4231 rows22240R_4232 (by norm_num)

theorem c22240R_147_22 : rowsJ2 147 148 71 340 ≤ 1554279414172921 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4230 c22240R_147_23 (by norm_num)

theorem c22240R_147_21 : rowsJ2 147 148 69 340 ≤ 1562206526929170 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4229 c22240R_147_22 (by norm_num)

theorem c22240R_147_20 : rowsJ2 147 148 68 340 ≤ 1567340926829821 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4228 c22240R_147_21 (by norm_num)

theorem c22240R_147_19 : rowsJ2 147 148 67 340 ≤ 1573352793722034 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4227 c22240R_147_20 (by norm_num)

theorem c22240R_147_18 : rowsJ2 147 148 66 340 ≤ 1580316591878686 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4226 c22240R_147_19 (by norm_num)

theorem c22240R_147_17 : rowsJ2 147 148 65 340 ≤ 1588308363127884 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4225 c22240R_147_18 (by norm_num)

theorem c22240R_147_16 : rowsJ2 147 148 64 340 ≤ 1597405857654245 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4224 c22240R_147_17 (by norm_num)

theorem c22240R_147_15 : rowsJ2 147 148 63 340 ≤ 1607688675368582 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4223 c22240R_147_16 (by norm_num)

theorem c22240R_147_14 : rowsJ2 147 148 62 340 ≤ 1619238409039430 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4222 c22240R_147_15 (by norm_num)

theorem c22240R_147_13 : rowsJ2 147 148 61 340 ≤ 1632138789201763 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4221 c22240R_147_14 (by norm_num)

theorem c22240R_147_12 : rowsJ2 147 148 60 340 ≤ 1646475841620104 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4220 c22240R_147_13 (by norm_num)

theorem c22240R_147_11 : rowsJ2 147 148 59 340 ≤ 1660948484823205 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4219 c22240R_147_12 (by norm_num)

theorem c22240R_147_10 : rowsJ2 147 148 58 340 ≤ 1674218234960754 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4218 c22240R_147_11 (by norm_num)

theorem c22240R_147_9 : rowsJ2 147 148 57 340 ≤ 1686324288439033 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4217 c22240R_147_10 (by norm_num)

theorem c22240R_147_8 : rowsJ2 147 148 56 340 ≤ 1697307134054450 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4216 c22240R_147_9 (by norm_num)

theorem c22240R_147_7 : rowsJ2 147 148 55 340 ≤ 1707208655246585 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4215 c22240R_147_8 (by norm_num)

theorem c22240R_147_6 : rowsJ2 147 148 54 340 ≤ 1716072240556684 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4214 c22240R_147_7 (by norm_num)

theorem c22240R_147_5 : rowsJ2 147 148 53 340 ≤ 1723942903006419 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4213 c22240R_147_6 (by norm_num)

theorem c22240R_147_4 : rowsJ2 147 148 52 340 ≤ 1730867407781150 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4212 c22240R_147_5 (by norm_num)

theorem c22240R_147_3 : rowsJ2 147 148 50 340 ≤ 1742074650945778 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4211 c22240R_147_4 (by norm_num)

theorem c22240R_147_2 : rowsJ2 147 148 48 340 ≤ 1750108707588330 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4210 c22240R_147_3 (by norm_num)

theorem c22240R_147_1 : rowsJ2 147 148 42 340 ≤ 1759938409849825 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4209 c22240R_147_2 (by norm_num)

theorem c22240R_147_0 : rowsJ2 147 148 0 340 ≤ 1761271040712225 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22240R_4208 c22240R_147_1 (by norm_num)

theorem hr22240R_147 : rows2 147 148 ≤ 1761271040712225 := rows2_le_of_rowsJ2 147 148 c22240R_147_0

theorem c22240R_148_23 : rowsJ2 148 149 72 340 ≤ 1672067129458692 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4256 rows22240R_4257 (by norm_num)

theorem c22240R_148_22 : rowsJ2 148 149 70 340 ≤ 1678068287620634 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4255 c22240R_148_23 (by norm_num)

theorem c22240R_148_21 : rowsJ2 148 149 68 340 ≤ 1686906444331007 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4254 c22240R_148_22 (by norm_num)

theorem c22240R_148_20 : rowsJ2 148 149 67 340 ≤ 1692570908902566 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4253 c22240R_148_21 (by norm_num)

theorem c22240R_148_19 : rowsJ2 148 149 66 340 ≤ 1699165152656254 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4252 c22240R_148_20 (by norm_num)

theorem c22240R_148_18 : rowsJ2 148 149 65 340 ≤ 1706765731069729 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4251 c22240R_148_19 (by norm_num)

theorem c22240R_148_17 : rowsJ2 148 149 64 340 ≤ 1715450887391712 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4250 c22240R_148_18 (by norm_num)

theorem c22240R_148_16 : rowsJ2 148 149 63 340 ≤ 1725300690231603 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4249 c22240R_148_17 (by norm_num)

theorem c22240R_148_15 : rowsJ2 148 149 62 340 ≤ 1736397182250799 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4248 c22240R_148_16 (by norm_num)

theorem c22240R_148_14 : rowsJ2 148 149 61 340 ≤ 1748824531158631 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4247 c22240R_148_15 (by norm_num)

theorem c22240R_148_13 : rowsJ2 148 149 60 340 ≤ 1762669183073768 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4246 c22240R_148_14 (by norm_num)

theorem c22240R_148_12 : rowsJ2 148 149 59 340 ≤ 1778020029124220 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4245 c22240R_148_13 (by norm_num)

theorem c22240R_148_11 : rowsJ2 148 149 58 340 ≤ 1792128984371382 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4244 c22240R_148_12 (by norm_num)

theorem c22240R_148_10 : rowsJ2 148 149 57 340 ≤ 1805035264047719 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4243 c22240R_148_11 (by norm_num)

theorem c22240R_148_9 : rowsJ2 148 149 56 340 ≤ 1816779343324187 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4242 c22240R_148_10 (by norm_num)

theorem c22240R_148_8 : rowsJ2 148 149 55 340 ≤ 1827403038099286 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4241 c22240R_148_9 (by norm_num)

theorem c22240R_148_7 : rowsJ2 148 149 54 340 ≤ 1836949633307468 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4240 c22240R_148_8 (by norm_num)

theorem c22240R_148_6 : rowsJ2 148 149 53 340 ≤ 1845463979033114 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4239 c22240R_148_7 (by norm_num)

theorem c22240R_148_5 : rowsJ2 148 149 52 340 ≤ 1852992640401605 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4238 c22240R_148_6 (by norm_num)

theorem c22240R_148_4 : rowsJ2 148 149 51 340 ≤ 1859584029110057 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4237 c22240R_148_5 (by norm_num)

theorem c22240R_148_3 : rowsJ2 148 149 50 340 ≤ 1865288564540298 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4236 c22240R_148_4 (by norm_num)

theorem c22240R_148_2 : rowsJ2 148 149 48 340 ≤ 1874249587264860 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4235 c22240R_148_3 (by norm_num)

theorem c22240R_148_1 : rowsJ2 148 149 43 340 ≤ 1885124593465237 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4234 c22240R_148_2 (by norm_num)

theorem c22240R_148_0 : rowsJ2 148 149 0 340 ≤ 1887152647493218 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22240R_4233 c22240R_148_1 (by norm_num)

theorem hr22240R_148 : rows2 148 149 ≤ 1887152647493218 := rows2_le_of_rowsJ2 148 149 c22240R_148_0

theorem c22240R_149_23 : rowsJ2 149 150 73 340 ≤ 1791283968282967 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4281 rows22240R_4282 (by norm_num)

theorem c22240R_149_22 : rowsJ2 149 150 70 340 ≤ 1798613445771759 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4280 c22240R_149_23 (by norm_num)

theorem c22240R_149_21 : rowsJ2 149 150 68 340 ≤ 1806803872399205 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4279 c22240R_149_22 (by norm_num)

theorem c22240R_149_20 : rowsJ2 149 150 67 340 ≤ 1812109084450392 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4278 c22240R_149_21 (by norm_num)

theorem c22240R_149_19 : rowsJ2 149 150 66 340 ≤ 1818321228303434 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4277 c22240R_149_20 (by norm_num)

theorem c22240R_149_18 : rowsJ2 149 150 65 340 ≤ 1825517393098446 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4276 c22240R_149_19 (by norm_num)

theorem c22240R_149_17 : rowsJ2 149 150 64 340 ≤ 1833776333768757 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4275 c22240R_149_18 (by norm_num)

theorem c22240R_149_16 : rowsJ2 149 150 63 340 ≤ 1843178610063342 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4274 c22240R_149_17 (by norm_num)

theorem c22240R_149_15 : rowsJ2 149 150 62 340 ≤ 1853806731442913 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4273 c22240R_149_16 (by norm_num)

theorem c22240R_149_14 : rowsJ2 149 150 61 340 ≤ 1865745313657849 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4272 c22240R_149_15 (by norm_num)

theorem c22240R_149_13 : rowsJ2 149 150 60 340 ≤ 1879081238223636 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4271 c22240R_149_14 (by norm_num)

theorem c22240R_149_12 : rowsJ2 149 150 59 340 ≤ 1893903814905522 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4270 c22240R_149_13 (by norm_num)

theorem c22240R_149_11 : rowsJ2 149 150 58 340 ≤ 1908867893515830 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4269 c22240R_149_12 (by norm_num)

theorem c22240R_149_10 : rowsJ2 149 150 57 340 ≤ 1922589323609604 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4268 c22240R_149_11 (by norm_num)

theorem c22240R_149_9 : rowsJ2 149 150 56 340 ≤ 1935108581613211 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4267 c22240R_149_10 (by norm_num)

theorem c22240R_149_8 : rowsJ2 149 150 55 340 ≤ 1946467452914452 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4266 c22240R_149_9 (by norm_num)

theorem c22240R_149_7 : rowsJ2 149 150 54 340 ≤ 1956709135180261 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4265 c22240R_149_8 (by norm_num)

theorem c22240R_149_6 : rowsJ2 149 150 53 340 ≤ 1965878354962549 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4264 c22240R_149_7 (by norm_num)

theorem c22240R_149_5 : rowsJ2 149 150 52 340 ≤ 1974021490402301 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4263 c22240R_149_6 (by norm_num)

theorem c22240R_149_4 : rowsJ2 149 150 51 340 ≤ 1981186725969951 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4262 c22240R_149_5 (by norm_num)

theorem c22240R_149_3 : rowsJ2 149 150 49 340 ≤ 1992786152462095 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4261 c22240R_149_4 (by norm_num)

theorem c22240R_149_2 : rowsJ2 149 150 47 340 ≤ 2001103899492405 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4260 c22240R_149_3 (by norm_num)

theorem c22240R_149_1 : rowsJ2 149 150 43 340 ≤ 2009811131089489 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4259 c22240R_149_2 (by norm_num)

theorem c22240R_149_0 : rowsJ2 149 150 0 340 ≤ 2011999832994041 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22240R_4258 c22240R_149_1 (by norm_num)

theorem hr22240R_149 : rows2 149 150 ≤ 2011999832994041 := rows2_le_of_rowsJ2 149 150 c22240R_149_0

theorem c22240R_150_23 : rowsJ2 150 151 71 340 ≤ 1915209870967275 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4306 rows22240R_4307 (by norm_num)

theorem c22240R_150_22 : rowsJ2 150 151 69 340 ≤ 1921412057826225 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4305 c22240R_150_23 (by norm_num)

theorem c22240R_150_21 : rowsJ2 150 151 67 340 ≤ 1930546682504052 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4304 c22240R_150_22 (by norm_num)

theorem c22240R_150_20 : rowsJ2 150 151 66 340 ≤ 1936401475392596 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4303 c22240R_150_21 (by norm_num)

theorem c22240R_150_19 : rowsJ2 150 151 65 340 ≤ 1943217610619400 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4302 c22240R_150_20 (by norm_num)

theorem c22240R_150_18 : rowsJ2 150 151 64 340 ≤ 1951074380819813 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4301 c22240R_150_19 (by norm_num)

theorem c22240R_150_17 : rowsJ2 150 151 63 340 ≤ 1960052861672604 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4300 c22240R_150_18 (by norm_num)

theorem c22240R_150_16 : rowsJ2 150 151 62 340 ≤ 1970236058240827 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4299 c22240R_150_17 (by norm_num)

theorem c22240R_150_15 : rowsJ2 150 151 61 340 ≤ 1981709057745964 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4298 c22240R_150_16 (by norm_num)

theorem c22240R_150_14 : rowsJ2 150 151 60 340 ≤ 1994559194655485 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4297 c22240R_150_15 (by norm_num)

theorem c22240R_150_13 : rowsJ2 150 151 59 340 ≤ 2008876219317019 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4296 c22240R_150_14 (by norm_num)

theorem c22240R_150_12 : rowsJ2 150 151 58 340 ≤ 2024752470307261 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4295 c22240R_150_13 (by norm_num)

theorem c22240R_150_11 : rowsJ2 150 151 57 340 ≤ 2039345438892714 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4294 c22240R_150_12 (by norm_num)

theorem c22240R_150_10 : rowsJ2 150 151 56 340 ≤ 2052695642484661 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4293 c22240R_150_11 (by norm_num)

theorem c22240R_150_9 : rowsJ2 150 151 55 340 ≤ 2064844867538606 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4292 c22240R_150_10 (by norm_num)

theorem c22240R_150_8 : rowsJ2 150 151 54 340 ≤ 2075836260935344 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4291 c22240R_150_9 (by norm_num)

theorem c22240R_150_7 : rowsJ2 150 151 53 340 ≤ 2085714459510614 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4290 c22240R_150_8 (by norm_num)

theorem c22240R_150_6 : rowsJ2 150 151 52 340 ≤ 2094525693423403 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4289 c22240R_150_7 (by norm_num)

theorem c22240R_150_5 : rowsJ2 150 151 51 340 ≤ 2102317951514031 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4288 c22240R_150_6 (by norm_num)

theorem c22240R_150_4 : rowsJ2 150 151 50 340 ≤ 2109141120406710 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4287 c22240R_150_5 (by norm_num)

theorem c22240R_150_3 : rowsJ2 150 151 49 340 ≤ 2115047148052935 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4286 c22240R_150_4 (by norm_num)

theorem c22240R_150_2 : rowsJ2 150 151 47 340 ≤ 2124326751051252 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4285 c22240R_150_3 (by norm_num)

theorem c22240R_150_1 : rowsJ2 150 151 43 340 ≤ 2134438902893361 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4284 c22240R_150_2 (by norm_num)

theorem c22240R_150_0 : rowsJ2 150 151 0 340 ≤ 2137190575488558 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22240R_4283 c22240R_150_1 (by norm_num)

theorem hr22240R_150 : rows2 150 151 ≤ 2137190575488558 := rows2_le_of_rowsJ2 150 151 c22240R_150_0

theorem c22240R_151_22 : rowsJ2 151 152 69 340 ≤ 2039077761682024 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4330 rows22240R_4331 (by norm_num)

theorem c22240R_151_21 : rowsJ2 151 152 67 340 ≤ 2047545345034579 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4329 c22240R_151_22 (by norm_num)

theorem c22240R_151_20 : rowsJ2 151 152 66 340 ≤ 2053030341635298 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4328 c22240R_151_21 (by norm_num)

theorem c22240R_151_19 : rowsJ2 151 152 65 340 ≤ 2059453285288140 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4327 c22240R_151_20 (by norm_num)

theorem c22240R_151_18 : rowsJ2 151 152 64 340 ≤ 2066894021189942 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4326 c22240R_151_19 (by norm_num)

theorem c22240R_151_17 : rowsJ2 151 152 63 340 ≤ 2075434160910278 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4325 c22240R_151_18 (by norm_num)

theorem c22240R_151_16 : rowsJ2 151 152 62 340 ≤ 2085157223683828 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4324 c22240R_151_17 (by norm_num)

theorem c22240R_151_15 : rowsJ2 151 152 61 340 ≤ 2096148790636072 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4323 c22240R_151_16 (by norm_num)

theorem c22240R_151_14 : rowsJ2 151 152 60 340 ≤ 2108496666052728 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4322 c22240R_151_15 (by norm_num)

theorem c22240R_151_13 : rowsJ2 151 152 59 340 ≤ 2122291051651321 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4321 c22240R_151_14 (by norm_num)

theorem c22240R_151_12 : rowsJ2 151 152 58 340 ≤ 2137624725110136 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4320 c22240R_151_13 (by norm_num)

theorem c22240R_151_11 : rowsJ2 151 152 57 340 ≤ 2153106182326111 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4319 c22240R_151_12 (by norm_num)

theorem c22240R_151_10 : rowsJ2 151 152 56 340 ≤ 2167303221690980 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4318 c22240R_151_11 (by norm_num)

theorem c22240R_151_9 : rowsJ2 151 152 55 340 ≤ 2180257652539887 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4317 c22240R_151_10 (by norm_num)

theorem c22240R_151_8 : rowsJ2 151 152 54 340 ≤ 2192012605053773 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4316 c22240R_151_9 (by norm_num)

theorem c22240R_151_7 : rowsJ2 151 152 53 340 ≤ 2202612644606902 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4315 c22240R_151_8 (by norm_num)

theorem c22240R_151_6 : rowsJ2 151 152 52 340 ≤ 2212103889936569 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4314 c22240R_151_7 (by norm_num)

theorem c22240R_151_5 : rowsJ2 151 152 51 340 ≤ 2220534154725207 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4313 c22240R_151_6 (by norm_num)

theorem c22240R_151_4 : rowsJ2 151 152 50 340 ≤ 2227953104402714 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4312 c22240R_151_5 (by norm_num)

theorem c22240R_151_3 : rowsJ2 151 152 49 340 ≤ 2234412407259778 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4311 c22240R_151_4 (by norm_num)

theorem c22240R_151_2 : rowsJ2 151 152 47 340 ≤ 2244669705174873 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4310 c22240R_151_3 (by norm_num)

theorem c22240R_151_1 : rowsJ2 151 152 43 340 ≤ 2256208751023014 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4309 c22240R_151_2 (by norm_num)

theorem c22240R_151_0 : rowsJ2 151 152 0 340 ≤ 2259533049400742 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22240R_4308 c22240R_151_1 (by norm_num)

theorem hr22240R_151 : rows2 151 152 ≤ 2259533049400742 := rows2_le_of_rowsJ2 151 152 c22240R_151_0

theorem c22240R_152_23 : rowsJ2 152 153 70 340 ≤ 2152930481072720 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4355 rows22240R_4356 (by norm_num)

theorem c22240R_152_22 : rowsJ2 152 153 68 340 ≤ 2159344322877334 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4354 c22240R_152_23 (by norm_num)

theorem c22240R_152_21 : rowsJ2 152 153 66 340 ≤ 2168791072943499 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4353 c22240R_152_22 (by norm_num)

theorem c22240R_152_20 : rowsJ2 152 153 65 340 ≤ 2174846242608383 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4352 c22240R_152_21 (by norm_num)

theorem c22240R_152_19 : rowsJ2 152 153 64 340 ≤ 2181895990124084 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4351 c22240R_152_20 (by norm_num)

theorem c22240R_152_18 : rowsJ2 152 153 63 340 ≤ 2190022484115333 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4350 c22240R_152_19 (by norm_num)

theorem c22240R_152_17 : rowsJ2 152 153 62 340 ≤ 2199309784455693 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4349 c22240R_152_18 (by norm_num)

theorem c22240R_152_16 : rowsJ2 152 153 61 340 ≤ 2209843991432819 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4348 c22240R_152_17 (by norm_num)

theorem c22240R_152_15 : rowsJ2 152 153 60 340 ≤ 2221713408484171 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4347 c22240R_152_16 (by norm_num)

theorem c22240R_152_14 : rowsJ2 152 153 59 340 ≤ 2235008712643505 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4346 c22240R_152_15 (by norm_num)

theorem c22240R_152_13 : rowsJ2 152 153 58 340 ≤ 2249823138741619 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4345 c22240R_152_14 (by norm_num)

theorem c22240R_152_12 : rowsJ2 152 153 57 340 ≤ 2266252668644244 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4344 c22240R_152_13 (by norm_num)

theorem c22240R_152_11 : rowsJ2 152 153 56 340 ≤ 2281355409763421 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4343 c22240R_152_12 (by norm_num)

theorem c22240R_152_10 : rowsJ2 152 153 55 340 ≤ 2295173242004518 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4342 c22240R_152_11 (by norm_num)

theorem c22240R_152_9 : rowsJ2 152 153 54 340 ≤ 2307749317911789 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4341 c22240R_152_10 (by norm_num)

theorem c22240R_152_8 : rowsJ2 152 153 53 340 ≤ 2319128165291929 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4340 c22240R_152_9 (by norm_num)

theorem c22240R_152_7 : rowsJ2 152 153 52 340 ≤ 2329355828270418 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4339 c22240R_152_8 (by norm_num)

theorem c22240R_152_6 : rowsJ2 152 153 51 340 ≤ 2338479981132571 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4338 c22240R_152_7 (by norm_num)

theorem c22240R_152_5 : rowsJ2 152 153 50 340 ≤ 2346550107843416 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4337 c22240R_152_6 (by norm_num)

theorem c22240R_152_4 : rowsJ2 152 153 49 340 ≤ 2353617628280662 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4336 c22240R_152_5 (by norm_num)

theorem c22240R_152_3 : rowsJ2 152 153 48 340 ≤ 2359736075478138 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4335 c22240R_152_4 (by norm_num)

theorem c22240R_152_2 : rowsJ2 152 153 46 340 ≤ 2369351570964948 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4334 c22240R_152_3 (by norm_num)

theorem c22240R_152_1 : rowsJ2 152 153 43 340 ≤ 2378140404067377 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4333 c22240R_152_2 (by norm_num)

theorem c22240R_152_0 : rowsJ2 152 153 0 340 ≤ 2382516664820082 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22240R_4332 c22240R_152_1 (by norm_num)

theorem hr22240R_152 : rows2 152 153 ≤ 2382516664820082 := rows2_le_of_rowsJ2 152 153 c22240R_152_0

theorem c22240R_153_22 : rowsJ2 153 154 69 340 ≤ 2271041650230542 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4379 rows22240R_4380 (by norm_num)

theorem c22240R_153_21 : rowsJ2 153 154 67 340 ≤ 2278259044789284 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4378 c22240R_153_22 (by norm_num)

theorem c22240R_153_20 : rowsJ2 153 154 65 340 ≤ 2288718125441261 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4377 c22240R_153_21 (by norm_num)

theorem c22240R_153_19 : rowsJ2 153 154 64 340 ≤ 2295363057350265 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4376 c22240R_153_20 (by norm_num)

theorem c22240R_153_18 : rowsJ2 153 154 63 340 ≤ 2303061354875903 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4375 c22240R_153_19 (by norm_num)

theorem c22240R_153_17 : rowsJ2 153 154 62 340 ≤ 2311897633290239 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4374 c22240R_153_18 (by norm_num)

theorem c22240R_153_16 : rowsJ2 153 154 61 340 ≤ 2321958531957103 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4373 c22240R_153_17 (by norm_num)

theorem c22240R_153_15 : rowsJ2 153 154 60 340 ≤ 2333332871989378 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4372 c22240R_153_16 (by norm_num)

theorem c22240R_153_14 : rowsJ2 153 154 59 340 ≤ 2346111828170885 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4371 c22240R_153_15 (by norm_num)

theorem c22240R_153_13 : rowsJ2 153 154 58 340 ≤ 2360389109318813 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4370 c22240R_153_14 (by norm_num)

theorem c22240R_153_12 : rowsJ2 153 154 57 340 ≤ 2376261153222503 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4369 c22240R_153_13 (by norm_num)

theorem c22240R_153_11 : rowsJ2 153 154 56 340 ≤ 2392287658759878 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4368 c22240R_153_12 (by norm_num)

theorem c22240R_153_10 : rowsJ2 153 154 55 340 ≤ 2406985818979825 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4367 c22240R_153_11 (by norm_num)

theorem c22240R_153_9 : rowsJ2 153 154 54 340 ≤ 2420398838082141 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4366 c22240R_153_10 (by norm_num)

theorem c22240R_153_8 : rowsJ2 153 154 53 340 ≤ 2432571247573385 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4365 c22240R_153_9 (by norm_num)

theorem c22240R_153_7 : rowsJ2 153 154 52 340 ≤ 2443549032318635 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4364 c22240R_153_8 (by norm_num)

theorem c22240R_153_6 : rowsJ2 153 154 51 340 ≤ 2453379766424361 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4363 c22240R_153_7 (by norm_num)

theorem c22240R_153_5 : rowsJ2 153 154 50 340 ≤ 2462112768032058 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4362 c22240R_153_6 (by norm_num)

theorem c22240R_153_4 : rowsJ2 153 154 49 340 ≤ 2469799249624377 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4361 c22240R_153_5 (by norm_num)

theorem c22240R_153_3 : rowsJ2 153 154 48 340 ≤ 2476492468484024 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4360 c22240R_153_4 (by norm_num)

theorem c22240R_153_2 : rowsJ2 153 154 46 340 ≤ 2487123550067916 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4359 c22240R_153_3 (by norm_num)

theorem c22240R_153_1 : rowsJ2 153 154 43 340 ≤ 2497093954809647 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4358 c22240R_153_2 (by norm_num)

theorem c22240R_153_0 : rowsJ2 153 154 0 340 ≤ 2502538079691135 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22240R_4357 c22240R_153_1 (by norm_num)

theorem hr22240R_153 : rows2 153 154 ≤ 2502538079691135 := rows2_le_of_rowsJ2 153 154 c22240R_153_0

theorem c22240R_154_21 : rowsJ2 154 155 67 340 ≤ 2391833461574124 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4402 rows22240R_4403 (by norm_num)

theorem c22240R_154_20 : rowsJ2 154 155 65 340 ≤ 2401608988411335 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4401 c22240R_154_21 (by norm_num)

theorem c22240R_154_19 : rowsJ2 154 155 64 340 ≤ 2407875223229676 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4400 c22240R_154_20 (by norm_num)

theorem c22240R_154_18 : rowsJ2 154 155 63 340 ≤ 2415171051491585 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4399 c22240R_154_19 (by norm_num)

theorem c22240R_154_17 : rowsJ2 154 155 62 340 ≤ 2423581678819053 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4398 c22240R_154_18 (by norm_num)

theorem c22240R_154_16 : rowsJ2 154 155 61 340 ≤ 2433194305251126 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4397 c22240R_154_17 (by norm_num)

theorem c22240R_154_15 : rowsJ2 154 155 60 340 ≤ 2444098296551204 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4396 c22240R_154_16 (by norm_num)

theorem c22240R_154_14 : rowsJ2 154 155 59 340 ≤ 2456385351040188 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4395 c22240R_154_15 (by norm_num)

theorem c22240R_154_13 : rowsJ2 154 155 58 340 ≤ 2470149681452300 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4394 c22240R_154_14 (by norm_num)

theorem c22240R_154_12 : rowsJ2 154 155 57 340 ≤ 2485488206030930 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4393 c22240R_154_13 (by norm_num)

theorem c22240R_154_11 : rowsJ2 154 155 56 340 ≤ 2502500755101108 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4392 c22240R_154_12 (by norm_num)

theorem c22240R_154_10 : rowsJ2 154 155 55 340 ≤ 2518140746978180 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4391 c22240R_154_11 (by norm_num)

theorem c22240R_154_9 : rowsJ2 154 155 54 340 ≤ 2532451484193991 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4390 c22240R_154_10 (by norm_num)

theorem c22240R_154_8 : rowsJ2 154 155 53 340 ≤ 2545477549226965 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4389 c22240R_154_9 (by norm_num)

theorem c22240R_154_7 : rowsJ2 154 155 52 340 ≤ 2557264909013450 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4388 c22240R_154_8 (by norm_num)

theorem c22240R_154_6 : rowsJ2 154 155 51 340 ≤ 2567861072446607 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4387 c22240R_154_7 (by norm_num)

theorem c22240R_154_5 : rowsJ2 154 155 50 340 ≤ 2577315229727064 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4386 c22240R_154_6 (by norm_num)

theorem c22240R_154_4 : rowsJ2 154 155 49 340 ≤ 2585678421992057 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4385 c22240R_154_5 (by norm_num)

theorem c22240R_154_3 : rowsJ2 154 155 47 340 ≤ 2599346164931428 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4384 c22240R_154_4 (by norm_num)

theorem c22240R_154_2 : rowsJ2 154 155 45 340 ≤ 2609316018542006 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4383 c22240R_154_3 (by norm_num)

theorem c22240R_154_1 : rowsJ2 154 155 42 340 ≤ 2618432445516540 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4382 c22240R_154_2 (by norm_num)

theorem c22240R_154_0 : rowsJ2 154 155 0 340 ≤ 2622920938873578 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22240R_4381 c22240R_154_1 (by norm_num)

theorem hr22240R_154 : rows2 154 155 ≤ 2622920938873578 := rows2_le_of_rowsJ2 154 155 c22240R_154_0

theorem c22240R_155_22 : rowsJ2 155 156 68 340 ≤ 2500813085096070 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4426 rows22240R_4427 (by norm_num)

theorem c22240R_155_21 : rowsJ2 155 156 66 340 ≤ 2508283671658117 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4425 c22240R_155_22 (by norm_num)

theorem c22240R_155_20 : rowsJ2 155 156 64 340 ≤ 2519110264253363 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4424 c22240R_155_21 (by norm_num)

theorem c22240R_155_19 : rowsJ2 155 156 63 340 ≤ 2525989091260405 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4423 c22240R_155_20 (by norm_num)

theorem c22240R_155_18 : rowsJ2 155 156 62 340 ≤ 2533958776486262 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4422 c22240R_155_19 (by norm_num)

theorem c22240R_155_17 : rowsJ2 155 156 61 340 ≤ 2543107108896723 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4421 c22240R_155_18 (by norm_num)

theorem c22240R_155_16 : rowsJ2 155 156 60 340 ≤ 2553524013568120 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4420 c22240R_155_17 (by norm_num)

theorem c22240R_155_15 : rowsJ2 155 156 59 340 ≤ 2565301732232063 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4419 c22240R_155_16 (by norm_num)

theorem c22240R_155_14 : rowsJ2 155 156 58 340 ≤ 2578535000025555 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4418 c22240R_155_15 (by norm_num)

theorem c22240R_155_13 : rowsJ2 155 156 57 340 ≤ 2593321238092297 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4417 c22240R_155_14 (by norm_num)

theorem c22240R_155_12 : rowsJ2 155 156 56 340 ≤ 2609760756300648 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4416 c22240R_155_13 (by norm_num)

theorem c22240R_155_11 : rowsJ2 155 156 55 340 ≤ 2626361838320477 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4415 c22240R_155_12 (by norm_num)

theorem c22240R_155_10 : rowsJ2 155 156 54 340 ≤ 2641588338624134 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4414 c22240R_155_11 (by norm_num)

theorem c22240R_155_9 : rowsJ2 155 156 53 340 ≤ 2655484917935282 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4413 c22240R_155_10 (by norm_num)

theorem c22240R_155_8 : rowsJ2 155 156 52 340 ≤ 2668097574788414 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4412 c22240R_155_9 (by norm_num)

theorem c22240R_155_7 : rowsJ2 155 156 51 340 ≤ 2679473775703076 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4411 c22240R_155_8 (by norm_num)

theorem c22240R_155_6 : rowsJ2 155 156 50 340 ≤ 2689662618705524 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4410 c22240R_155_7 (by norm_num)

theorem c22240R_155_5 : rowsJ2 155 156 49 340 ≤ 2698714991261896 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4409 c22240R_155_6 (by norm_num)

theorem c22240R_155_4 : rowsJ2 155 156 48 340 ≤ 2706683716526255 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4408 c22240R_155_5 (by norm_num)

theorem c22240R_155_3 : rowsJ2 155 156 47 340 ≤ 2713623712269068 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4407 c22240R_155_4 (by norm_num)

theorem c22240R_155_2 : rowsJ2 155 156 45 340 ≤ 2724649215231061 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4406 c22240R_155_3 (by norm_num)

theorem c22240R_155_1 : rowsJ2 155 156 42 340 ≤ 2734993680008078 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4405 c22240R_155_2 (by norm_num)

theorem c22240R_155_0 : rowsJ2 155 156 0 340 ≤ 2740590883188606 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22240R_4404 c22240R_155_1 (by norm_num)

theorem hr22240R_155 : rows2 155 156 ≤ 2740590883188606 := rows2_le_of_rowsJ2 155 156 c22240R_155_0

theorem c22240R_156_21 : rowsJ2 156 157 66 340 ≤ 2619147809765773 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4449 rows22240R_4450 (by norm_num)

theorem c22240R_156_20 : rowsJ2 156 157 64 340 ≤ 2629269823358794 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4448 c22240R_156_21 (by norm_num)

theorem c22240R_156_19 : rowsJ2 156 157 63 340 ≤ 2635758505581882 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4447 c22240R_156_20 (by norm_num)

theorem c22240R_156_18 : rowsJ2 156 157 62 340 ≤ 2643313690275739 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4446 c22240R_156_19 (by norm_num)

theorem c22240R_156_17 : rowsJ2 156 157 61 340 ≤ 2652023795137490 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4445 c22240R_156_18 (by norm_num)

theorem c22240R_156_16 : rowsJ2 156 157 60 340 ≤ 2661979340083991 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4444 c22240R_156_17 (by norm_num)

theorem c22240R_156_15 : rowsJ2 156 157 59 340 ≤ 2673273132351263 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4443 c22240R_156_16 (by norm_num)

theorem c22240R_156_14 : rowsJ2 156 157 58 340 ≤ 2686000457028480 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4442 c22240R_156_15 (by norm_num)

theorem c22240R_156_13 : rowsJ2 156 157 57 340 ≤ 2700259264545432 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4441 c22240R_156_14 (by norm_num)

theorem c22240R_156_12 : rowsJ2 156 157 56 340 ≤ 2716150374918251 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4440 c22240R_156_13 (by norm_num)

theorem c22240R_156_11 : rowsJ2 156 157 55 340 ≤ 2733777693074830 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4439 c22240R_156_12 (by norm_num)

theorem c22240R_156_10 : rowsJ2 156 157 54 340 ≤ 2749984265412723 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4438 c22240R_156_11 (by norm_num)

theorem c22240R_156_9 : rowsJ2 156 157 53 340 ≤ 2764814880821530 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4437 c22240R_156_10 (by norm_num)

theorem c22240R_156_8 : rowsJ2 156 157 52 340 ≤ 2778315615070444 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4436 c22240R_156_9 (by norm_num)

theorem c22240R_156_7 : rowsJ2 156 157 51 340 ≤ 2790533942886869 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4435 c22240R_156_8 (by norm_num)

theorem c22240R_156_6 : rowsJ2 156 157 50 340 ≤ 2801518912193399 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4434 c22240R_156_7 (by norm_num)

theorem c22240R_156_5 : rowsJ2 156 157 49 340 ≤ 2811321292192159 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4433 c22240R_156_6 (by norm_num)

theorem c22240R_156_4 : rowsJ2 156 157 48 340 ≤ 2819993746196039 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4432 c22240R_156_5 (by norm_num)

theorem c22240R_156_3 : rowsJ2 156 157 47 340 ≤ 2827590964274843 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4431 c22240R_156_4 (by norm_num)

theorem c22240R_156_2 : rowsJ2 156 157 45 340 ≤ 2839790107903612 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4430 c22240R_156_3 (by norm_num)

theorem c22240R_156_1 : rowsJ2 156 157 42 340 ≤ 2851536492155876 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4429 c22240R_156_2 (by norm_num)

theorem c22240R_156_0 : rowsJ2 156 157 0 340 ≤ 2858526859071953 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22240R_4428 c22240R_156_1 (by norm_num)

theorem hr22240R_156 : rows2 156 157 ≤ 2858526859071953 := rows2_le_of_rowsJ2 156 157 c22240R_156_0

theorem c22240R_157_20 : rowsJ2 157 158 65 340 ≤ 2615727882150842 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22240R_4471 rows22240R_4472 (by norm_num)

theorem c22240R_157_19 : rowsJ2 157 158 63 340 ≤ 2626941890946783 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22240R_4470 c22240R_157_20 (by norm_num)

theorem c22240R_157_18 : rowsJ2 157 158 62 340 ≤ 2634067298803379 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22240R_4469 c22240R_157_19 (by norm_num)

theorem c22240R_157_17 : rowsJ2 157 158 61 340 ≤ 2642323100337819 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22240R_4468 c22240R_157_18 (by norm_num)

theorem c22240R_157_16 : rowsJ2 157 158 60 340 ≤ 2651800443056143 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22240R_4467 c22240R_157_17 (by norm_num)

theorem c22240R_157_15 : rowsJ2 157 158 59 340 ≤ 2662592727961596 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22240R_4466 c22240R_157_16 (by norm_num)

theorem c22240R_157_14 : rowsJ2 157 158 58 340 ≤ 2674795804665408 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22240R_4465 c22240R_157_15 (by norm_num)

theorem c22240R_157_13 : rowsJ2 157 158 57 340 ≤ 2688508172725796 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22240R_4464 c22240R_157_14 (by norm_num)

theorem c22240R_157_12 : rowsJ2 157 158 56 340 ≤ 2703831180764655 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22240R_4463 c22240R_157_13 (by norm_num)

theorem c22240R_157_11 : rowsJ2 157 158 55 340 ≤ 2720869243336480 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22240R_4462 c22240R_157_12 (by norm_num)

theorem c22240R_157_10 : rowsJ2 157 158 54 340 ≤ 2738076432074080 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22240R_4461 c22240R_157_11 (by norm_num)

theorem c22240R_157_9 : rowsJ2 157 158 53 340 ≤ 2753860331297680 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22240R_4460 c22240R_157_10 (by norm_num)

theorem c22240R_157_8 : rowsJ2 157 158 52 340 ≤ 2768267123951831 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22240R_4459 c22240R_157_9 (by norm_num)

theorem c22240R_157_7 : rowsJ2 157 158 51 340 ≤ 2781344340985901 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22240R_4458 c22240R_157_8 (by norm_num)

theorem c22240R_157_6 : rowsJ2 157 158 50 340 ≤ 2793141010668453 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22240R_4457 c22240R_157_7 (by norm_num)

theorem c22240R_157_5 : rowsJ2 157 158 49 340 ≤ 2803707826934136 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22240R_4456 c22240R_157_6 (by norm_num)

theorem c22240R_157_4 : rowsJ2 157 158 48 340 ≤ 2813097307774047 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22240R_4455 c22240R_157_5 (by norm_num)

theorem c22240R_157_3 : rowsJ2 157 158 47 340 ≤ 2821363954712999 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22240R_4454 c22240R_157_4 (by norm_num)

theorem c22240R_157_2 : rowsJ2 157 158 45 340 ≤ 2834757986040181 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22240R_4453 c22240R_157_3 (by norm_num)

theorem c22240R_157_1 : rowsJ2 157 158 42 340 ≤ 2847930610011219 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22240R_4452 c22240R_157_2 (by norm_num)

theorem c22240R_157_0 : rowsJ2 157 158 0 340 ≤ 2856391720640678 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22240R_4451 c22240R_157_1 (by norm_num)

theorem hr22240R_157 : rows2 157 158 ≤ 2856391720640678 := rows2_le_of_rowsJ2 157 158 c22240R_157_0

theorem c22240R_158_21 : rowsJ2 158 159 66 340 ≤ 2604632416677813 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4494 rows22240R_4495 (by norm_num)

theorem c22240R_158_20 : rowsJ2 158 159 64 340 ≤ 2613350275286786 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4493 c22240R_158_21 (by norm_num)

theorem c22240R_158_19 : rowsJ2 158 159 62 340 ≤ 2625781101944278 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4492 c22240R_158_20 (by norm_num)

theorem c22240R_158_18 : rowsJ2 158 159 61 340 ≤ 2633609794003201 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4491 c22240R_158_19 (by norm_num)

theorem c22240R_158_17 : rowsJ2 158 159 60 340 ≤ 2642635730615866 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4490 c22240R_158_18 (by norm_num)

theorem c22240R_158_16 : rowsJ2 158 159 59 340 ≤ 2652952947004102 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4489 c22240R_158_17 (by norm_num)

theorem c22240R_158_15 : rowsJ2 158 159 58 340 ≤ 2664657893476917 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4488 c22240R_158_16 (by norm_num)

theorem c22240R_158_14 : rowsJ2 158 159 57 340 ≤ 2677849641378688 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4487 c22240R_158_15 (by norm_num)

theorem c22240R_158_13 : rowsJ2 158 159 56 340 ≤ 2692630096137436 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4486 c22240R_158_14 (by norm_num)

theorem c22240R_158_12 : rowsJ2 158 159 55 340 ≤ 2709104208999598 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4485 c22240R_158_13 (by norm_num)

theorem c22240R_158_11 : rowsJ2 158 159 54 340 ≤ 2727380207608948 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4484 c22240R_158_12 (by norm_num)

theorem c22240R_158_10 : rowsJ2 158 159 53 340 ≤ 2744184685334961 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4483 c22240R_158_11 (by norm_num)

theorem c22240R_158_9 : rowsJ2 158 159 52 340 ≤ 2759563980864144 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4482 c22240R_158_10 (by norm_num)

theorem c22240R_158_8 : rowsJ2 158 159 51 340 ≤ 2773565730852557 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4481 c22240R_158_9 (by norm_num)

theorem c22240R_158_7 : rowsJ2 158 159 50 340 ≤ 2786238992758131 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4480 c22240R_158_8 (by norm_num)

theorem c22240R_158_6 : rowsJ2 158 159 49 340 ≤ 2797634435511594 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4479 c22240R_158_7 (by norm_num)

theorem c22240R_158_5 : rowsJ2 158 159 48 340 ≤ 2807804475221117 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4478 c22240R_158_6 (by norm_num)

theorem c22240R_158_4 : rowsJ2 158 159 47 340 ≤ 2816803461222752 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4477 c22240R_158_5 (by norm_num)

theorem c22240R_158_3 : rowsJ2 158 159 46 340 ≤ 2824687852128816 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4476 c22240R_158_4 (by norm_num)

theorem c22240R_158_2 : rowsJ2 158 159 44 340 ≤ 2837350951585773 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4475 c22240R_158_3 (by norm_num)

theorem c22240R_158_1 : rowsJ2 158 159 41 340 ≤ 2849549014278571 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4474 c22240R_158_2 (by norm_num)

theorem c22240R_158_0 : rowsJ2 158 159 0 340 ≤ 2856583722641673 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22240R_4473 c22240R_158_1 (by norm_num)

theorem hr22240R_158 : rows2 158 159 ≤ 2856583722641673 := rows2_le_of_rowsJ2 158 159 c22240R_158_0

theorem c22240R_159_20 : rowsJ2 159 160 64 340 ≤ 2606211104007764 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22240R_4516 rows22240R_4517 (by norm_num)

theorem c22240R_159_19 : rowsJ2 159 160 62 340 ≤ 2617833709895538 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22240R_4515 c22240R_159_20 (by norm_num)

theorem c22240R_159_18 : rowsJ2 159 160 61 340 ≤ 2625219218833153 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22240R_4514 c22240R_159_19 (by norm_num)

theorem c22240R_159_17 : rowsJ2 159 160 60 340 ≤ 2633776843960488 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22240R_4513 c22240R_159_18 (by norm_num)

theorem c22240R_159_16 : rowsJ2 159 160 59 340 ≤ 2643601278780119 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22240R_4512 c22240R_159_17 (by norm_num)

theorem c22240R_159_15 : rowsJ2 159 160 58 340 ≤ 2654789607091165 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22240R_4511 c22240R_159_16 (by norm_num)

theorem c22240R_159_14 : rowsJ2 159 160 57 340 ≤ 2667441500310632 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22240R_4510 c22240R_159_15 (by norm_num)

theorem c22240R_159_13 : rowsJ2 159 160 56 340 ≤ 2681659435157111 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22240R_4509 c22240R_159_14 (by norm_num)

theorem c22240R_159_12 : rowsJ2 159 160 55 340 ≤ 2697548919392155 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22240R_4508 c22240R_159_13 (by norm_num)

theorem c22240R_159_11 : rowsJ2 159 160 54 340 ≤ 2715218717252369 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22240R_4507 c22240R_159_12 (by norm_num)

theorem c22240R_159_10 : rowsJ2 159 160 53 340 ≤ 2733065697048972 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22240R_4506 c22240R_159_11 (by norm_num)

theorem c22240R_159_9 : rowsJ2 159 160 52 340 ≤ 2749438037703815 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22240R_4505 c22240R_159_10 (by norm_num)

theorem c22240R_159_8 : rowsJ2 159 160 51 340 ≤ 2764383509643372 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22240R_4504 c22240R_159_9 (by norm_num)

theorem c22240R_159_7 : rowsJ2 159 160 50 340 ≤ 2777951251277771 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22240R_4503 c22240R_159_8 (by norm_num)

theorem c22240R_159_6 : rowsJ2 159 160 49 340 ≤ 2790191933420394 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22240R_4502 c22240R_159_7 (by norm_num)

theorem c22240R_159_5 : rowsJ2 159 160 48 340 ≤ 2801157921813845 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22240R_4501 c22240R_159_6 (by norm_num)

theorem c22240R_159_4 : rowsJ2 159 160 47 340 ≤ 2810903435459002 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22240R_4500 c22240R_159_5 (by norm_num)

theorem c22240R_159_3 : rowsJ2 159 160 46 340 ≤ 2819484738366661 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22240R_4499 c22240R_159_4 (by norm_num)

theorem c22240R_159_2 : rowsJ2 159 160 44 340 ≤ 2833391645900088 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22240R_4498 c22240R_159_3 (by norm_num)

theorem c22240R_159_1 : rowsJ2 159 160 41 340 ≤ 2847074134781065 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22240R_4497 c22240R_159_2 (by norm_num)

theorem c22240R_159_0 : rowsJ2 159 160 0 340 ≤ 2855577467354961 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22240R_4496 c22240R_159_1 (by norm_num)

theorem hr22240R_159 : rows2 159 160 ≤ 2855577467354961 := rows2_le_of_rowsJ2 159 160 c22240R_159_0

theorem c22240R_160_20 : rowsJ2 160 161 65 340 ≤ 2597063831789255 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22240R_4538 rows22240R_4539 (by norm_num)

theorem c22240R_160_19 : rowsJ2 160 161 63 340 ≤ 2606101662589155 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22240R_4537 c22240R_160_20 (by norm_num)

theorem c22240R_160_18 : rowsJ2 160 161 61 340 ≤ 2618989815356445 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22240R_4536 c22240R_160_19 (by norm_num)

theorem c22240R_160_17 : rowsJ2 160 161 60 340 ≤ 2627107104719276 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22240R_4535 c22240R_160_18 (by norm_num)

theorem c22240R_160_16 : rowsJ2 160 161 59 340 ≤ 2636466322701178 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22240R_4534 c22240R_160_17 (by norm_num)

theorem c22240R_160_15 : rowsJ2 160 161 58 340 ≤ 2647165218753966 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22240R_4533 c22240R_160_16 (by norm_num)

theorem c22240R_160_14 : rowsJ2 160 161 57 340 ≤ 2659304105545515 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22240R_4532 c22240R_160_15 (by norm_num)

theorem c22240R_160_13 : rowsJ2 160 161 56 340 ≤ 2672986067991614 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22240R_4531 c22240R_160_14 (by norm_num)

theorem c22240R_160_12 : rowsJ2 160 161 55 340 ≤ 2688317193671112 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22240R_4530 c22240R_160_13 (by norm_num)

theorem c22240R_160_11 : rowsJ2 160 161 54 340 ≤ 2705406812353442 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22240R_4529 c22240R_160_12 (by norm_num)

theorem c22240R_160_10 : rowsJ2 160 161 53 340 ≤ 2724367736327079 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22240R_4528 c22240R_160_11 (by norm_num)

theorem c22240R_160_9 : rowsJ2 160 161 52 340 ≤ 2741803592405035 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22240R_4527 c22240R_160_10 (by norm_num)

theorem c22240R_160_8 : rowsJ2 160 161 51 340 ≤ 2757762343026806 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22240R_4526 c22240R_160_9 (by norm_num)

theorem c22240R_160_7 : rowsJ2 160 161 50 340 ≤ 2772293256302131 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22240R_4525 c22240R_160_8 (by norm_num)

theorem c22240R_160_6 : rowsJ2 160 161 49 340 ≤ 2785447057045176 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22240R_4524 c22240R_160_7 (by norm_num)

theorem c22240R_160_5 : rowsJ2 160 161 48 340 ≤ 2797276108597854 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22240R_4523 c22240R_160_6 (by norm_num)

theorem c22240R_160_4 : rowsJ2 160 161 47 340 ≤ 2807834552162989 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22240R_4522 c22240R_160_5 (by norm_num)

theorem c22240R_160_3 : rowsJ2 160 161 46 340 ≤ 2817178502218702 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22240R_4521 c22240R_160_4 (by norm_num)

theorem c22240R_160_2 : rowsJ2 160 161 44 340 ≤ 2832458860234841 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22240R_4520 c22240R_160_3 (by norm_num)

theorem c22240R_160_1 : rowsJ2 160 161 41 340 ≤ 2847816279342999 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22240R_4519 c22240R_160_2 (by norm_num)

theorem c22240R_160_0 : rowsJ2 160 161 0 340 ≤ 2858096958674554 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22240R_4518 c22240R_160_1 (by norm_num)

theorem hr22240R_160 : rows2 160 161 ≤ 2858096958674554 := rows2_le_of_rowsJ2 160 161 c22240R_160_0

theorem c22240R_161_19 : rowsJ2 161 162 63 340 ≤ 2602610379014999 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22240R_4559 rows22240R_4560 (by norm_num)

theorem c22240R_161_18 : rowsJ2 161 162 61 340 ≤ 2614664124957381 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22240R_4558 c22240R_161_19 (by norm_num)

theorem c22240R_161_17 : rowsJ2 161 162 60 340 ≤ 2622324150616705 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22240R_4557 c22240R_161_18 (by norm_num)

theorem c22240R_161_16 : rowsJ2 161 162 59 340 ≤ 2631200357943665 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22240R_4556 c22240R_161_17 (by norm_num)

theorem c22240R_161_15 : rowsJ2 161 162 58 340 ≤ 2641391187556306 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22240R_4555 c22240R_161_16 (by norm_num)

theorem c22240R_161_14 : rowsJ2 161 162 57 340 ≤ 2652997617392302 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22240R_4554 c22240R_161_15 (by norm_num)

theorem c22240R_161_13 : rowsJ2 161 162 56 340 ≤ 2666123373416315 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22240R_4553 c22240R_161_14 (by norm_num)

theorem c22240R_161_12 : rowsJ2 161 162 55 340 ≤ 2680875151350234 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22240R_4552 c22240R_161_13 (by norm_num)

theorem c22240R_161_11 : rowsJ2 161 162 54 340 ≤ 2697362860905876 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22240R_4551 c22240R_161_12 (by norm_num)

theorem c22240R_161_10 : rowsJ2 161 162 53 340 ≤ 2715699880292580 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22240R_4550 c22240R_161_11 (by norm_num)

theorem c22240R_161_9 : rowsJ2 161 162 52 340 ≤ 2734222662398550 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22240R_4549 c22240R_161_10 (by norm_num)

theorem c22240R_161_8 : rowsJ2 161 162 51 340 ≤ 2751216623505775 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22240R_4548 c22240R_161_9 (by norm_num)

theorem c22240R_161_7 : rowsJ2 161 162 50 340 ≤ 2766731199153708 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22240R_4547 c22240R_161_8 (by norm_num)

theorem c22240R_161_6 : rowsJ2 161 162 49 340 ≤ 2780817217499218 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22240R_4546 c22240R_161_7 (by norm_num)

theorem c22240R_161_5 : rowsJ2 161 162 48 340 ≤ 2793527069492038 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22240R_4545 c22240R_161_6 (by norm_num)

theorem c22240R_161_4 : rowsJ2 161 162 47 340 ≤ 2804914867241484 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22240R_4544 c22240R_161_5 (by norm_num)

theorem c22240R_161_3 : rowsJ2 161 162 46 340 ≤ 2815036611686664 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22240R_4543 c22240R_161_4 (by norm_num)

theorem c22240R_161_2 : rowsJ2 161 162 44 340 ≤ 2831717017648506 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22240R_4542 c22240R_161_3 (by norm_num)

theorem c22240R_161_1 : rowsJ2 161 162 41 340 ≤ 2848780467500649 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22240R_4541 c22240R_161_2 (by norm_num)

theorem c22240R_161_0 : rowsJ2 161 162 0 340 ≤ 2860984713461045 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22240R_4540 c22240R_161_1 (by norm_num)

theorem hr22240R_161 : rows2 161 162 ≤ 2860984713461045 := rows2_le_of_rowsJ2 161 162 c22240R_161_0

theorem c22240R_162_19 : rowsJ2 162 163 62 340 ≤ 2606197367406738 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22240R_4580 rows22240R_4581 (by norm_num)

theorem c22240R_162_18 : rowsJ2 162 163 60 340 ≤ 2619568243304720 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22240R_4579 c22240R_162_19 (by norm_num)

theorem c22240R_162_17 : rowsJ2 162 163 59 340 ≤ 2627990228847155 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22240R_4578 c22240R_162_18 (by norm_num)

theorem c22240R_162_16 : rowsJ2 162 163 58 340 ≤ 2637701355984490 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22240R_4577 c22240R_162_17 (by norm_num)

theorem c22240R_162_15 : rowsJ2 162 163 57 340 ≤ 2648803302013843 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22240R_4576 c22240R_162_16 (by norm_num)

theorem c22240R_162_14 : rowsJ2 162 163 56 340 ≤ 2661400466797967 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22240R_4575 c22240R_162_15 (by norm_num)

theorem c22240R_162_13 : rowsJ2 162 163 55 340 ≤ 2675600196198899 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22240R_4574 c22240R_162_14 (by norm_num)

theorem c22240R_162_12 : rowsJ2 162 163 54 340 ≤ 2691513017603833 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22240R_4573 c22240R_162_13 (by norm_num)

theorem c22240R_162_11 : rowsJ2 162 163 53 340 ≤ 2709252899183151 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22240R_4572 c22240R_162_12 (by norm_num)

theorem c22240R_162_10 : rowsJ2 162 163 52 340 ≤ 2728937520706598 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22240R_4571 c22240R_162_11 (by norm_num)

theorem c22240R_162_9 : rowsJ2 162 163 51 340 ≤ 2747040549166409 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22240R_4570 c22240R_162_10 (by norm_num)

theorem c22240R_162_8 : rowsJ2 162 163 50 340 ≤ 2763611656212286 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22240R_4569 c22240R_162_9 (by norm_num)

theorem c22240R_162_7 : rowsJ2 162 163 49 340 ≤ 2778701831520512 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22240R_4568 c22240R_162_8 (by norm_num)

theorem c22240R_162_6 : rowsJ2 162 163 48 340 ≤ 2792363544292702 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22240R_4567 c22240R_162_7 (by norm_num)

theorem c22240R_162_5 : rowsJ2 162 163 47 340 ≤ 2804650929509176 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22240R_4566 c22240R_162_6 (by norm_num)

theorem c22240R_162_4 : rowsJ2 162 163 46 340 ≤ 2815619930701663 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22240R_4565 c22240R_162_5 (by norm_num)

theorem c22240R_162_3 : rowsJ2 162 163 45 340 ≤ 2825328562313301 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22240R_4564 c22240R_162_4 (by norm_num)

theorem c22240R_162_2 : rowsJ2 162 163 43 340 ≤ 2841208779102429 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22240R_4563 c22240R_162_3 (by norm_num)

theorem c22240R_162_1 : rowsJ2 162 163 40 340 ≤ 2857175502063769 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22240R_4562 c22240R_162_2 (by norm_num)

theorem c22240R_162_0 : rowsJ2 162 163 0 340 ≤ 2867260869526710 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22240R_4561 c22240R_162_1 (by norm_num)

theorem hr22240R_162 : rows2 162 163 ≤ 2867260869526710 := rows2_le_of_rowsJ2 162 163 c22240R_162_0

theorem c22240R_163_18 : rowsJ2 163 164 61 340 ≤ 2611798548316684 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22240R_4600 rows22240R_4601 (by norm_num)

theorem c22240R_163_17 : rowsJ2 163 164 59 340 ≤ 2626535520632436 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22240R_4599 c22240R_163_18 (by norm_num)

theorem c22240R_163_16 : rowsJ2 163 164 58 340 ≤ 2635748199800968 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22240R_4598 c22240R_163_17 (by norm_num)

theorem c22240R_163_15 : rowsJ2 163 164 57 340 ≤ 2646326041566637 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22240R_4597 c22240R_163_16 (by norm_num)

theorem c22240R_163_14 : rowsJ2 163 164 56 340 ≤ 2658374145166223 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22240R_4596 c22240R_163_15 (by norm_num)

theorem c22240R_163_13 : rowsJ2 163 164 55 340 ≤ 2672000530589547 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22240R_4595 c22240R_163_14 (by norm_num)

theorem c22240R_163_12 : rowsJ2 163 164 54 340 ≤ 2687316375829583 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22240R_4594 c22240R_163_13 (by norm_num)

theorem c22240R_163_11 : rowsJ2 163 164 53 340 ≤ 2704436267402771 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22240R_4593 c22240R_163_12 (by norm_num)

theorem c22240R_163_10 : rowsJ2 163 164 52 340 ≤ 2723478475953752 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22240R_4592 c22240R_163_11 (by norm_num)

theorem c22240R_163_9 : rowsJ2 163 164 51 340 ≤ 2742715592721226 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22240R_4591 c22240R_163_10 (by norm_num)

theorem c22240R_163_8 : rowsJ2 163 164 50 340 ≤ 2760366662931568 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22240R_4590 c22240R_163_9 (by norm_num)

theorem c22240R_163_7 : rowsJ2 163 164 49 340 ≤ 2776482884087147 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22240R_4589 c22240R_163_8 (by norm_num)

theorem c22240R_163_6 : rowsJ2 163 164 48 340 ≤ 2791116862707283 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22240R_4588 c22240R_163_7 (by norm_num)

theorem c22240R_163_5 : rowsJ2 163 164 47 340 ≤ 2804322784306267 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22240R_4587 c22240R_163_6 (by norm_num)

theorem c22240R_163_4 : rowsJ2 163 164 46 340 ≤ 2816156587191334 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22240R_4586 c22240R_163_5 (by norm_num)

theorem c22240R_163_3 : rowsJ2 163 164 45 340 ≤ 2826676177397039 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22240R_4585 c22240R_163_4 (by norm_num)

theorem c22240R_163_2 : rowsJ2 163 164 43 340 ≤ 2844015954063639 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22240R_4584 c22240R_163_3 (by norm_num)

theorem c22240R_163_1 : rowsJ2 163 164 40 340 ≤ 2861760934809978 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22240R_4583 c22240R_163_2 (by norm_num)

theorem c22240R_163_0 : rowsJ2 163 164 0 340 ≤ 2873717481268545 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22240R_4582 c22240R_163_1 (by norm_num)

theorem hr22240R_163 : rows2 163 164 ≤ 2873717481268545 := rows2_le_of_rowsJ2 163 164 c22240R_163_0

theorem c22240R_164_19 : rowsJ2 164 165 61 340 ≤ 2613404316499447 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22240R_4621 rows22240R_4622 (by norm_num)

theorem c22240R_164_18 : rowsJ2 164 165 59 340 ≤ 2627285014720154 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22240R_4620 c22240R_164_19 (by norm_num)

theorem c22240R_164_17 : rowsJ2 164 165 58 340 ≤ 2636028874271445 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22240R_4619 c22240R_164_18 (by norm_num)

theorem c22240R_164_16 : rowsJ2 164 165 57 340 ≤ 2646111807377848 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22240R_4618 c22240R_164_17 (by norm_num)

theorem c22240R_164_15 : rowsJ2 164 165 56 340 ≤ 2657639642048259 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22240R_4617 c22240R_164_16 (by norm_num)

theorem c22240R_164_14 : rowsJ2 164 165 55 340 ≤ 2670721107235880 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22240R_4616 c22240R_164_15 (by norm_num)

theorem c22240R_164_13 : rowsJ2 164 165 54 340 ≤ 2685468065170032 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22240R_4615 c22240R_164_14 (by norm_num)

theorem c22240R_164_12 : rowsJ2 164 165 53 340 ≤ 2701995763635390 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22240R_4614 c22240R_164_13 (by norm_num)

theorem c22240R_164_11 : rowsJ2 164 165 52 340 ≤ 2720423102821324 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22240R_4613 c22240R_164_12 (by norm_num)

theorem c22240R_164_10 : rowsJ2 164 165 51 340 ≤ 2740872928746257 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22240R_4612 c22240R_164_11 (by norm_num)

theorem c22240R_164_9 : rowsJ2 164 165 50 340 ≤ 2759681439953026 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22240R_4611 c22240R_164_10 (by norm_num)

theorem c22240R_164_8 : rowsJ2 164 165 49 340 ≤ 2776900110739150 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22240R_4610 c22240R_164_9 (by norm_num)

theorem c22240R_164_7 : rowsJ2 164 165 48 340 ≤ 2792581751984983 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22240R_4609 c22240R_164_8 (by norm_num)

theorem c22240R_164_6 : rowsJ2 164 165 47 340 ≤ 2806780661217135 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22240R_4608 c22240R_164_7 (by norm_num)

theorem c22240R_164_5 : rowsJ2 164 165 46 340 ≤ 2819552821975137 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22240R_4607 c22240R_164_6 (by norm_num)

theorem c22240R_164_4 : rowsJ2 164 165 45 340 ≤ 2830956092716719 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22240R_4606 c22240R_164_5 (by norm_num)

theorem c22240R_164_3 : rowsJ2 164 165 44 340 ≤ 2841050517843261 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22240R_4605 c22240R_164_4 (by norm_num)

theorem c22240R_164_2 : rowsJ2 164 165 42 340 ≤ 2857565455656391 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22240R_4604 c22240R_164_3 (by norm_num)

theorem c22240R_164_1 : rowsJ2 164 165 40 340 ≤ 2869631534555480 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22240R_4603 c22240R_164_2 (by norm_num)

theorem c22240R_164_0 : rowsJ2 164 165 0 340 ≤ 2883793927087984 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22240R_4602 c22240R_164_1 (by norm_num)

theorem hr22240R_164 : rows2 164 165 ≤ 2883793927087984 := rows2_le_of_rowsJ2 164 165 c22240R_164_0

theorem c22240R_165_18 : rowsJ2 165 166 60 340 ≤ 2622646846350349 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22240R_4641 rows22240R_4642 (by norm_num)

theorem c22240R_165_17 : rowsJ2 165 166 58 340 ≤ 2637951180484516 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22240R_4640 c22240R_165_18 (by norm_num)

theorem c22240R_165_16 : rowsJ2 165 166 57 340 ≤ 2647519432934859 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22240R_4639 c22240R_165_17 (by norm_num)

theorem c22240R_165_15 : rowsJ2 165 166 56 340 ≤ 2658506321875521 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22240R_4638 c22240R_165_16 (by norm_num)

theorem c22240R_165_14 : rowsJ2 165 166 55 340 ≤ 2671021305469862 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22240R_4637 c22240R_165_15 (by norm_num)

theorem c22240R_165_13 : rowsJ2 165 166 54 340 ≤ 2685176955635820 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22240R_4636 c22240R_165_14 (by norm_num)

theorem c22240R_165_12 : rowsJ2 165 166 53 340 ≤ 2701089205398589 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22240R_4635 c22240R_165_13 (by norm_num)

theorem c22240R_165_11 : rowsJ2 165 166 52 340 ≤ 2718877617525824 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22240R_4634 c22240R_165_12 (by norm_num)

theorem c22240R_165_10 : rowsJ2 165 166 51 340 ≤ 2738665669169455 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22240R_4633 c22240R_165_11 (by norm_num)

theorem c22240R_165_9 : rowsJ2 165 166 50 340 ≤ 2758658382584511 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22240R_4632 c22240R_165_10 (by norm_num)

theorem c22240R_165_8 : rowsJ2 165 166 49 340 ≤ 2777004560887664 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22240R_4631 c22240R_165_9 (by norm_num)

theorem c22240R_165_7 : rowsJ2 165 166 48 340 ≤ 2793757264050941 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22240R_4630 c22240R_165_8 (by norm_num)

theorem c22240R_165_6 : rowsJ2 165 166 47 340 ≤ 2808970969816130 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22240R_4629 c22240R_165_7 (by norm_num)

theorem c22240R_165_5 : rowsJ2 165 166 46 340 ≤ 2822701744666795 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22240R_4628 c22240R_165_6 (by norm_num)

theorem c22240R_165_4 : rowsJ2 165 166 45 340 ≤ 2835007450222939 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22240R_4627 c22240R_165_5 (by norm_num)

theorem c22240R_165_3 : rowsJ2 165 166 44 340 ≤ 2845948038985461 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22240R_4626 c22240R_165_4 (by norm_num)

theorem c22240R_165_2 : rowsJ2 165 166 42 340 ≤ 2863985702147272 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22240R_4625 c22240R_165_3 (by norm_num)

theorem c22240R_165_1 : rowsJ2 165 166 39 340 ≤ 2882452313728893 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22240R_4624 c22240R_165_2 (by norm_num)

theorem c22240R_165_0 : rowsJ2 165 166 0 340 ≤ 2893877192336359 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22240R_4623 c22240R_165_1 (by norm_num)

theorem hr22240R_165 : rows2 165 166 ≤ 2893877192336359 := rows2_le_of_rowsJ2 165 166 c22240R_165_0

theorem c22240R_166_17 : rowsJ2 166 167 59 340 ≤ 2634114091635870 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22240R_4660 rows22240R_4661 (by norm_num)

theorem c22240R_166_16 : rowsJ2 166 167 57 340 ≤ 2650997740382489 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22240R_4659 c22240R_166_17 (by norm_num)

theorem c22240R_166_15 : rowsJ2 166 167 56 340 ≤ 2661473738322855 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22240R_4658 c22240R_166_16 (by norm_num)

theorem c22240R_166_14 : rowsJ2 166 167 55 340 ≤ 2673451885433798 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22240R_4657 c22240R_166_15 (by norm_num)

theorem c22240R_166_13 : rowsJ2 166 167 54 340 ≤ 2687045493464521 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22240R_4656 c22240R_166_14 (by norm_num)

theorem c22240R_166_12 : rowsJ2 166 167 53 340 ≤ 2702371216366376 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22240R_4655 c22240R_166_13 (by norm_num)

theorem c22240R_166_11 : rowsJ2 166 167 52 340 ≤ 2719549314007492 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22240R_4654 c22240R_166_12 (by norm_num)

theorem c22240R_166_10 : rowsJ2 166 167 51 340 ≤ 2738703938643612 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22240R_4653 c22240R_166_11 (by norm_num)

theorem c22240R_166_9 : rowsJ2 166 167 50 340 ≤ 2759963438985570 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22240R_4652 c22240R_166_10 (by norm_num)

theorem c22240R_166_8 : rowsJ2 166 167 49 340 ≤ 2779518472144116 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22240R_4651 c22240R_166_9 (by norm_num)

theorem c22240R_166_7 : rowsJ2 166 167 48 340 ≤ 2797422421529091 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22240R_4650 c22240R_166_8 (by norm_num)

theorem c22240R_166_6 : rowsJ2 166 167 47 340 ≤ 2813730011972149 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22240R_4649 c22240R_166_7 (by norm_num)

theorem c22240R_166_5 : rowsJ2 166 167 46 340 ≤ 2828497464214378 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22240R_4648 c22240R_166_6 (by norm_num)

theorem c22240R_166_4 : rowsJ2 166 167 45 340 ≤ 2841782705071423 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22240R_4647 c22240R_166_5 (by norm_num)

theorem c22240R_166_3 : rowsJ2 166 167 44 340 ≤ 2853645654721880 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22240R_4646 c22240R_166_4 (by norm_num)

theorem c22240R_166_2 : rowsJ2 166 167 42 340 ≤ 2873355952806044 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22240R_4645 c22240R_166_3 (by norm_num)

theorem c22240R_166_1 : rowsJ2 166 167 39 340 ≤ 2893896905181425 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22240R_4644 c22240R_166_2 (by norm_num)

theorem c22240R_166_0 : rowsJ2 166 167 0 340 ≤ 2907411558414222 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22240R_4643 c22240R_166_1 (by norm_num)

theorem hr22240R_166 : rows2 166 167 ≤ 2907411558414222 := rows2_le_of_rowsJ2 166 167 c22240R_166_0

theorem c22240R_167_18 : rowsJ2 167 168 59 340 ≤ 2640421302682642 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22240R_4680 rows22240R_4681 (by norm_num)

theorem c22240R_167_17 : rowsJ2 167 168 57 340 ≤ 2656325475342730 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22240R_4679 c22240R_167_18 (by norm_num)

theorem c22240R_167_16 : rowsJ2 167 168 56 340 ≤ 2666269711964790 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22240R_4678 c22240R_167_17 (by norm_num)

theorem c22240R_167_15 : rowsJ2 167 168 55 340 ≤ 2677689207151882 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22240R_4677 c22240R_167_16 (by norm_num)

theorem c22240R_167_14 : rowsJ2 167 168 54 340 ≤ 2690698042785577 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22240R_4676 c22240R_167_15 (by norm_num)

theorem c22240R_167_13 : rowsJ2 167 168 53 340 ≤ 2705413613907071 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22240R_4675 c22240R_167_14 (by norm_num)

theorem c22240R_167_12 : rowsJ2 167 168 52 340 ≤ 2721956902932334 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22240R_4674 c22240R_167_13 (by norm_num)

theorem c22240R_167_11 : rowsJ2 167 168 51 340 ≤ 2740452761199258 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22240R_4673 c22240R_167_12 (by norm_num)

theorem c22240R_167_10 : rowsJ2 167 168 50 340 ≤ 2761030214899132 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22240R_4672 c22240R_167_11 (by norm_num)

theorem c22240R_167_9 : rowsJ2 167 168 49 340 ≤ 2781822747200366 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22240R_4671 c22240R_167_10 (by norm_num)

theorem c22240R_167_8 : rowsJ2 167 168 48 340 ≤ 2800904758852772 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22240R_4670 c22240R_167_9 (by norm_num)

theorem c22240R_167_7 : rowsJ2 167 168 47 340 ≤ 2818331271661234 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22240R_4669 c22240R_167_8 (by norm_num)

theorem c22240R_167_6 : rowsJ2 167 168 46 340 ≤ 2834158728081486 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22240R_4668 c22240R_167_7 (by norm_num)

theorem c22240R_167_5 : rowsJ2 167 168 45 340 ≤ 2848445173128921 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22240R_4667 c22240R_167_6 (by norm_num)

theorem c22240R_167_4 : rowsJ2 167 168 44 340 ≤ 2861250544385658 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22240R_4666 c22240R_167_5 (by norm_num)

theorem c22240R_167_3 : rowsJ2 167 168 43 340 ≤ 2872636955271857 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22240R_4665 c22240R_167_4 (by norm_num)

theorem c22240R_167_2 : rowsJ2 167 168 41 340 ≤ 2891413809027580 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22240R_4664 c22240R_167_3 (by norm_num)

theorem c22240R_167_1 : rowsJ2 167 168 39 340 ≤ 2905326459819044 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22240R_4663 c22240R_167_2 (by norm_num)

theorem c22240R_167_0 : rowsJ2 167 168 0 340 ≤ 2921157631849289 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22240R_4662 c22240R_167_1 (by norm_num)

theorem hr22240R_167 : rows2 167 168 ≤ 2921157631849289 := rows2_le_of_rowsJ2 167 168 c22240R_167_0

theorem c22240R_168_17 : rowsJ2 168 169 58 340 ≤ 2655429775923537 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22240R_4699 rows22240R_4700 (by norm_num)

theorem c22240R_168_16 : rowsJ2 168 169 56 340 ≤ 2672981705137731 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22240R_4698 c22240R_168_17 (by norm_num)

theorem c22240R_168_15 : rowsJ2 168 169 55 340 ≤ 2683873500061876 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22240R_4697 c22240R_168_16 (by norm_num)

theorem c22240R_168_14 : rowsJ2 168 169 54 340 ≤ 2696328090139220 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22240R_4696 c22240R_168_15 (by norm_num)

theorem c22240R_168_13 : rowsJ2 168 169 53 340 ≤ 2710463652355268 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22240R_4695 c22240R_168_14 (by norm_num)

theorem c22240R_168_12 : rowsJ2 168 169 52 340 ≤ 2726401922671602 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22240R_4694 c22240R_168_13 (by norm_num)

theorem c22240R_168_11 : rowsJ2 168 169 51 340 ≤ 2744268488165448 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22240R_4693 c22240R_168_12 (by norm_num)

theorem c22240R_168_10 : rowsJ2 168 169 50 340 ≤ 2764193088051182 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22240R_4692 c22240R_168_11 (by norm_num)

theorem c22240R_168_9 : rowsJ2 168 169 49 340 ≤ 2786309940889119 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22240R_4691 c22240R_168_10 (by norm_num)

theorem c22240R_168_8 : rowsJ2 168 169 48 340 ≤ 2806655501160850 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22240R_4690 c22240R_168_9 (by norm_num)

theorem c22240R_168_7 : rowsJ2 168 169 47 340 ≤ 2825285162138095 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22240R_4689 c22240R_168_8 (by norm_num)

theorem c22240R_168_6 : rowsJ2 168 169 46 340 ≤ 2842255660978073 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22240R_4688 c22240R_168_7 (by norm_num)

theorem c22240R_168_5 : rowsJ2 168 169 45 340 ≤ 2857625237761040 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22240R_4687 c22240R_168_6 (by norm_num)

theorem c22240R_168_4 : rowsJ2 168 169 44 340 ≤ 2871453915246572 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22240R_4686 c22240R_168_5 (by norm_num)

theorem c22240R_168_3 : rowsJ2 168 169 43 340 ≤ 2883803798241892 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22240R_4685 c22240R_168_4 (by norm_num)

theorem c22240R_168_2 : rowsJ2 168 169 41 340 ≤ 2904327594730446 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22240R_4684 c22240R_168_3 (by norm_num)

theorem c22240R_168_1 : rowsJ2 168 169 38 340 ≤ 2925724962171453 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22240R_4683 c22240R_168_2 (by norm_num)

theorem c22240R_168_0 : rowsJ2 168 169 0 340 ≤ 2938193132183118 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22240R_4682 c22240R_168_1 (by norm_num)

theorem hr22240R_168 : rows2 168 169 ≤ 2938193132183118 := rows2_le_of_rowsJ2 168 169 c22240R_168_0

theorem c22240R_169_17 : rowsJ2 169 170 57 340 ≤ 2672484560914341 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22240R_4718 rows22240R_4719 (by norm_num)

theorem c22240R_169_16 : rowsJ2 169 170 55 340 ≤ 2691749305522550 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22240R_4717 c22240R_169_17 (by norm_num)

theorem c22240R_169_15 : rowsJ2 169 170 54 340 ≤ 2703626616129642 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22240R_4716 c22240R_169_16 (by norm_num)

theorem c22240R_169_14 : rowsJ2 169 170 53 340 ≤ 2717158179856113 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22240R_4715 c22240R_169_15 (by norm_num)

theorem c22240R_169_13 : rowsJ2 169 170 52 340 ≤ 2732466516525789 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22240R_4714 c22240R_169_14 (by norm_num)

theorem c22240R_169_12 : rowsJ2 169 170 51 340 ≤ 2749677969053695 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22240R_4713 c22240R_169_13 (by norm_num)

theorem c22240R_169_11 : rowsJ2 169 170 50 340 ≤ 2768923015144814 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22240R_4712 c22240R_169_12 (by norm_num)

theorem c22240R_169_10 : rowsJ2 169 170 49 340 ≤ 2790336589597105 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22240R_4711 c22240R_169_11 (by norm_num)

theorem c22240R_169_9 : rowsJ2 169 170 48 340 ≤ 2811976376051320 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22240R_4710 c22240R_169_10 (by norm_num)

theorem c22240R_169_8 : rowsJ2 169 170 47 340 ≤ 2831837904661860 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22240R_4709 c22240R_169_9 (by norm_num)

theorem c22240R_169_7 : rowsJ2 169 170 46 340 ≤ 2849978256536683 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22240R_4708 c22240R_169_8 (by norm_num)

theorem c22240R_169_6 : rowsJ2 169 170 45 340 ≤ 2866455939800274 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22240R_4707 c22240R_169_7 (by norm_num)

theorem c22240R_169_5 : rowsJ2 169 170 44 340 ≤ 2881331120674690 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22240R_4706 c22240R_169_6 (by norm_num)

theorem c22240R_169_4 : rowsJ2 169 170 43 340 ≤ 2894665949435817 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22240R_4705 c22240R_169_5 (by norm_num)

theorem c22240R_169_3 : rowsJ2 169 170 42 340 ≤ 2906524823171788 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22240R_4704 c22240R_169_4 (by norm_num)

theorem c22240R_169_2 : rowsJ2 169 170 40 340 ≤ 2926085204771067 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22240R_4703 c22240R_169_3 (by norm_num)

theorem c22240R_169_1 : rowsJ2 169 170 38 340 ≤ 2940583309994503 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22240R_4702 c22240R_169_2 (by norm_num)

theorem c22240R_169_0 : rowsJ2 169 170 0 340 ≤ 2955237583949668 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22240R_4701 c22240R_169_1 (by norm_num)

theorem hr22240R_169 : rows2 169 170 ≤ 2955237583949668 := rows2_le_of_rowsJ2 169 170 c22240R_169_0

theorem c22240R_170_16 : rowsJ2 170 171 55 340 ≤ 2701708373676152 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22240R_4736 rows22240R_4737 (by norm_num)

theorem c22240R_170_15 : rowsJ2 170 171 54 340 ≤ 2713040324817954 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22240R_4735 c22240R_170_16 (by norm_num)

theorem c22240R_170_14 : rowsJ2 170 171 53 340 ≤ 2725999338037769 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22240R_4734 c22240R_170_15 (by norm_num)

theorem c22240R_170_13 : rowsJ2 170 171 52 340 ≤ 2740708791729493 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22240R_4733 c22240R_170_14 (by norm_num)

theorem c22240R_170_12 : rowsJ2 170 171 51 340 ≤ 2757295826529426 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22240R_4732 c22240R_170_13 (by norm_num)

theorem c22240R_170_11 : rowsJ2 170 171 50 340 ≤ 2775891690616003 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22240R_4731 c22240R_170_12 (by norm_num)

theorem c22240R_170_10 : rowsJ2 170 171 49 340 ≤ 2796632072795846 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22240R_4730 c22240R_170_11 (by norm_num)

theorem c22240R_170_9 : rowsJ2 170 171 48 340 ≤ 2819657448111543 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22240R_4729 c22240R_170_10 (by norm_num)

theorem c22240R_170_8 : rowsJ2 170 171 47 340 ≤ 2840840756647002 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22240R_4728 c22240R_170_9 (by norm_num)

theorem c22240R_170_7 : rowsJ2 170 171 46 340 ≤ 2860239512727871 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22240R_4727 c22240R_170_8 (by norm_num)

theorem c22240R_170_6 : rowsJ2 170 171 45 340 ≤ 2877912565856049 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22240R_4726 c22240R_170_7 (by norm_num)

theorem c22240R_170_5 : rowsJ2 170 171 44 340 ≤ 2893920309492486 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22240R_4725 c22240R_170_6 (by norm_num)

theorem c22240R_170_4 : rowsJ2 170 171 43 340 ≤ 2908325012879888 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22240R_4724 c22240R_170_5 (by norm_num)

theorem c22240R_170_3 : rowsJ2 170 171 42 340 ≤ 2921191091413533 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22240R_4723 c22240R_170_4 (by norm_num)

theorem c22240R_170_2 : rowsJ2 170 171 40 340 ≤ 2942577448455417 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22240R_4722 c22240R_170_3 (by norm_num)

theorem c22240R_170_1 : rowsJ2 170 171 38 340 ≤ 2958648584007152 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22240R_4721 c22240R_170_2 (by norm_num)

theorem c22240R_170_0 : rowsJ2 170 171 0 340 ≤ 2975792972248987 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22240R_4720 c22240R_170_1 (by norm_num)

theorem hr22240R_170 : rows2 170 171 ≤ 2975792972248987 := rows2_le_of_rowsJ2 170 171 c22240R_170_0

theorem c22240R_171_15 : rowsJ2 171 172 54 340 ≤ 2724019821309549 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22240R_4753 rows22240R_4754 (by norm_num)

theorem c22240R_171_14 : rowsJ2 171 172 53 340 ≤ 2736381976991264 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22240R_4752 c22240R_171_15 (by norm_num)

theorem c22240R_171_13 : rowsJ2 171 172 52 340 ≤ 2750467210240496 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22240R_4751 c22240R_171_14 (by norm_num)

theorem c22240R_171_12 : rowsJ2 171 172 51 340 ≤ 2766403523104619 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22240R_4750 c22240R_171_13 (by norm_num)

theorem c22240R_171_11 : rowsJ2 171 172 50 340 ≤ 2784322964594425 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22240R_4749 c22240R_171_12 (by norm_num)

theorem c22240R_171_10 : rowsJ2 171 172 49 340 ≤ 2804361997583598 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22240R_4748 c22240R_171_11 (by norm_num)

theorem c22240R_171_9 : rowsJ2 171 172 48 340 ≤ 2826661855297917 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22240R_4747 c22240R_171_10 (by norm_num)

theorem c22240R_171_8 : rowsJ2 171 172 47 340 ≤ 2849199828029764 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22240R_4746 c22240R_171_9 (by norm_num)

theorem c22240R_171_7 : rowsJ2 171 172 46 340 ≤ 2869887764704578 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22240R_4745 c22240R_171_8 (by norm_num)

theorem c22240R_171_6 : rowsJ2 171 172 45 340 ≤ 2888784919345034 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22240R_4744 c22240R_171_7 (by norm_num)

theorem c22240R_171_5 : rowsJ2 171 172 44 340 ≤ 2905951985979285 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22240R_4743 c22240R_171_6 (by norm_num)

theorem c22240R_171_4 : rowsJ2 171 172 43 340 ≤ 2921451416419592 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22240R_4742 c22240R_171_5 (by norm_num)

theorem c22240R_171_3 : rowsJ2 171 172 42 340 ≤ 2935347703295515 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22240R_4741 c22240R_171_4 (by norm_num)

theorem c22240R_171_2 : rowsJ2 171 172 40 340 ≤ 2958600710618683 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22240R_4740 c22240R_171_3 (by norm_num)

theorem c22240R_171_1 : rowsJ2 171 172 37 340 ≤ 2983218577359676 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22240R_4739 c22240R_171_2 (by norm_num)

theorem c22240R_171_0 : rowsJ2 171 172 0 340 ≤ 2996161493260405 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22240R_4738 c22240R_171_1 (by norm_num)

theorem hr22240R_171 : rows2 171 172 ≤ 2996161493260405 := rows2_le_of_rowsJ2 171 172 c22240R_171_0

theorem c22240R_172_15 : rowsJ2 172 173 53 340 ≤ 2748691971876765 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22240R_4770 rows22240R_4771 (by norm_num)

theorem c22240R_172_14 : rowsJ2 172 173 52 340 ≤ 2762185427319303 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22240R_4769 c22240R_172_15 (by norm_num)

theorem c22240R_172_13 : rowsJ2 172 173 51 340 ≤ 2777503018048617 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22240R_4768 c22240R_172_14 (by norm_num)

theorem c22240R_172_12 : rowsJ2 172 173 50 340 ≤ 2794777670081034 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22240R_4767 c22240R_172_13 (by norm_num)

theorem c22240R_172_11 : rowsJ2 172 173 49 340 ≤ 2814146663418990 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22240R_4766 c22240R_172_12 (by norm_num)

theorem c22240R_172_10 : rowsJ2 172 173 48 340 ≤ 2835752022592528 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22240R_4765 c22240R_172_11 (by norm_num)

theorem c22240R_172_9 : rowsJ2 172 173 47 340 ≤ 2859740898812088 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22240R_4764 c22240R_172_10 (by norm_num)

theorem c22240R_172_8 : rowsJ2 172 173 46 340 ≤ 2881812674685926 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22240R_4763 c22240R_172_9 (by norm_num)

theorem c22240R_172_7 : rowsJ2 172 173 45 340 ≤ 2902027109775581 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22240R_4762 c22240R_172_8 (by norm_num)

theorem c22240R_172_6 : rowsJ2 172 173 44 340 ≤ 2920445287621997 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22240R_4761 c22240R_172_7 (by norm_num)

theorem c22240R_172_5 : rowsJ2 172 173 43 340 ≤ 2937129927068808 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22240R_4760 c22240R_172_6 (by norm_num)

theorem c22240R_172_4 : rowsJ2 172 173 42 340 ≤ 2952145677826805 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22240R_4759 c22240R_172_5 (by norm_num)

theorem c22240R_172_3 : rowsJ2 172 173 41 340 ≤ 2965559401342957 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22240R_4758 c22240R_172_4 (by norm_num)

theorem c22240R_172_2 : rowsJ2 172 173 39 340 ≤ 2987861058881353 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22240R_4757 c22240R_172_3 (by norm_num)

theorem c22240R_172_1 : rowsJ2 172 173 37 340 ≤ 3004625670930189 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22240R_4756 c22240R_172_2 (by norm_num)

theorem c22240R_172_0 : rowsJ2 172 173 0 340 ≤ 3019842307071911 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22240R_4755 c22240R_172_1 (by norm_num)

theorem hr22240R_172 : rows2 172 173 ≤ 3019842307071911 := rows2_le_of_rowsJ2 172 173 c22240R_172_0

theorem c22240R_173_15 : rowsJ2 173 174 53 340 ≤ 2762777697369864 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22240R_4787 rows22240R_4788 (by norm_num)

theorem c22240R_173_14 : rowsJ2 173 174 52 340 ≤ 2775653715670006 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22240R_4786 c22240R_173_15 (by norm_num)

theorem c22240R_173_13 : rowsJ2 173 174 51 340 ≤ 2790325835151751 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22240R_4785 c22240R_173_14 (by norm_num)

theorem c22240R_173_12 : rowsJ2 173 174 50 340 ≤ 2806927906192390 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22240R_4784 c22240R_173_13 (by norm_num)

theorem c22240R_173_11 : rowsJ2 173 174 49 340 ≤ 2825598090026138 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22240R_4783 c22240R_173_12 (by norm_num)

theorem c22240R_173_10 : rowsJ2 173 174 48 340 ≤ 2846479232923943 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22240R_4782 c22240R_173_11 (by norm_num)

theorem c22240R_173_9 : rowsJ2 173 174 47 340 ≤ 2869719282633261 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22240R_4781 c22240R_173_10 (by norm_num)

theorem c22240R_173_8 : rowsJ2 173 174 46 340 ≤ 2893210183642280 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22240R_4780 c22240R_173_9 (by norm_num)

theorem c22240R_173_7 : rowsJ2 173 174 45 340 ≤ 2914774909912750 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22240R_4779 c22240R_173_8 (by norm_num)

theorem c22240R_173_6 : rowsJ2 173 174 44 340 ≤ 2934475015289735 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22240R_4778 c22240R_173_7 (by norm_num)

theorem c22240R_173_5 : rowsJ2 173 174 43 340 ≤ 2952373560831678 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22240R_4777 c22240R_173_6 (by norm_num)

theorem c22240R_173_4 : rowsJ2 173 174 42 340 ≤ 2968535422866807 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22240R_4776 c22240R_173_5 (by norm_num)

theorem c22240R_173_3 : rowsJ2 173 174 41 340 ≤ 2983027576043438 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22240R_4775 c22240R_173_4 (by norm_num)

theorem c22240R_173_2 : rowsJ2 173 174 39 340 ≤ 3007282942824463 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22240R_4774 c22240R_173_3 (by norm_num)

theorem c22240R_173_1 : rowsJ2 173 174 37 340 ≤ 3025729116783843 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22240R_4773 c22240R_173_2 (by norm_num)

theorem c22240R_173_0 : rowsJ2 173 174 0 340 ≤ 3043536624594634 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22240R_4772 c22240R_173_1 (by norm_num)

theorem hr22240R_173 : rows2 173 174 ≤ 3043536624594634 := rows2_le_of_rowsJ2 173 174 c22240R_173_0

theorem c22240R_174_14 : rowsJ2 174 175 52 340 ≤ 2790879740892822 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22240R_4803 rows22240R_4804 (by norm_num)

theorem c22240R_174_13 : rowsJ2 174 175 51 340 ≤ 2804939884810562 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22240R_4802 c22240R_174_14 (by norm_num)

theorem c22240R_174_12 : rowsJ2 174 175 50 340 ≤ 2820902399779597 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22240R_4801 c22240R_174_13 (by norm_num)

theorem c22240R_174_11 : rowsJ2 174 175 49 340 ≤ 2838906388803309 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22240R_4800 c22240R_174_12 (by norm_num)

theorem c22240R_174_10 : rowsJ2 174 175 48 340 ≤ 2859095597716784 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22240R_4799 c22240R_174_11 (by norm_num)

theorem c22240R_174_9 : rowsJ2 174 175 47 340 ≤ 2881618815220209 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22240R_4798 c22240R_174_10 (by norm_num)

theorem c22240R_174_8 : rowsJ2 174 175 46 340 ≤ 2906630317750711 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22240R_4797 c22240R_174_9 (by norm_num)

theorem c22240R_174_7 : rowsJ2 174 175 45 340 ≤ 2929645093369537 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22240R_4796 c22240R_174_8 (by norm_num)

theorem c22240R_174_6 : rowsJ2 174 175 44 340 ≤ 2950725276157561 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22240R_4795 c22240R_174_7 (by norm_num)

theorem c22240R_174_5 : rowsJ2 174 175 43 340 ≤ 2969934367140782 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22240R_4794 c22240R_174_6 (by norm_num)

theorem c22240R_174_4 : rowsJ2 174 175 42 340 ≤ 2987337561333336 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22240R_4793 c22240R_174_5 (by norm_num)

theorem c22240R_174_3 : rowsJ2 174 175 41 340 ≤ 3003002033485978 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22240R_4792 c22240R_174_4 (by norm_num)

theorem c22240R_174_2 : rowsJ2 174 175 39 340 ≤ 3029395217980906 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22240R_4791 c22240R_174_3 (by norm_num)

theorem c22240R_174_1 : rowsJ2 174 175 36 340 ≤ 3056913234836597 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22240R_4790 c22240R_174_2 (by norm_num)

theorem c22240R_174_0 : rowsJ2 174 175 0 340 ≤ 3070360508101740 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22240R_4789 c22240R_174_1 (by norm_num)

theorem hr22240R_174 : rows2 174 175 ≤ 3070360508101740 := rows2_le_of_rowsJ2 174 175 c22240R_174_0

theorem c22240R_175_14 : rowsJ2 175 176 51 340 ≤ 2821151843505479 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22240R_4819 rows22240R_4820 (by norm_num)

theorem c22240R_175_13 : rowsJ2 175 176 50 340 ≤ 2836446552332735 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22240R_4818 c22240R_175_14 (by norm_num)

theorem c22240R_175_12 : rowsJ2 175 176 49 340 ≤ 2853754993966006 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22240R_4817 c22240R_175_13 (by norm_num)

theorem c22240R_175_11 : rowsJ2 175 176 48 340 ≤ 2873221861382410 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22240R_4816 c22240R_175_12 (by norm_num)

theorem c22240R_175_10 : rowsJ2 175 176 47 340 ≤ 2894996848812453 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22240R_4815 c22240R_175_11 (by norm_num)

theorem c22240R_175_9 : rowsJ2 175 176 46 340 ≤ 2919235080148110 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22240R_4814 c22240R_175_10 (by norm_num)

theorem c22240R_175_8 : rowsJ2 175 176 45 340 ≤ 2943737802194802 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22240R_4813 c22240R_175_9 (by norm_num)

theorem c22240R_175_7 : rowsJ2 175 176 44 340 ≤ 2966233506978318 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22240R_4812 c22240R_175_8 (by norm_num)

theorem c22240R_175_6 : rowsJ2 175 176 43 340 ≤ 2986786224835287 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22240R_4811 c22240R_175_7 (by norm_num)

theorem c22240R_175_5 : rowsJ2 175 176 42 340 ≤ 3005461551944950 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22240R_4810 c22240R_175_6 (by norm_num)

theorem c22240R_175_4 : rowsJ2 175 176 41 340 ≤ 3022326939329881 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22240R_4809 c22240R_175_5 (by norm_num)

theorem c22240R_175_3 : rowsJ2 175 176 40 340 ≤ 3037451994325598 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22240R_4808 c22240R_175_4 (by norm_num)

theorem c22240R_175_2 : rowsJ2 175 176 38 340 ≤ 3062772230937466 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22240R_4807 c22240R_175_3 (by norm_num)

theorem c22240R_175_1 : rowsJ2 175 176 36 340 ≤ 3081153541233332 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22240R_4806 c22240R_175_2 (by norm_num)

theorem c22240R_175_0 : rowsJ2 175 176 0 340 ≤ 3096967757120637 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22240R_4805 c22240R_175_1 (by norm_num)

theorem hr22240R_175 : rows2 175 176 ≤ 3096967757120637 := rows2_le_of_rowsJ2 175 176 c22240R_175_0

theorem c22240R_176_14 : rowsJ2 176 177 51 340 ≤ 2838619340357571 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22240R_4835 rows22240R_4836 (by norm_num)

theorem c22240R_176_13 : rowsJ2 176 177 50 340 ≤ 2853280847139410 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22240R_4834 c22240R_176_14 (by norm_num)

theorem c22240R_176_12 : rowsJ2 176 177 49 340 ≤ 2869927852324720 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22240R_4833 c22240R_176_13 (by norm_num)

theorem c22240R_176_11 : rowsJ2 176 177 48 340 ≤ 2888706053409975 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22240R_4832 c22240R_176_12 (by norm_num)

theorem c22240R_176_10 : rowsJ2 176 177 47 340 ≤ 2909766112246374 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22240R_4831 c22240R_176_11 (by norm_num)

theorem c22240R_176_9 : rowsJ2 176 177 46 340 ≤ 2933264079869779 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22240R_4830 c22240R_176_10 (by norm_num)

theorem c22240R_176_8 : rowsJ2 176 177 45 340 ≤ 2959361856120011 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22240R_4829 c22240R_176_9 (by norm_num)

theorem c22240R_176_7 : rowsJ2 176 177 44 340 ≤ 2983378320741420 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22240R_4828 c22240R_176_8 (by norm_num)

theorem c22240R_176_6 : rowsJ2 176 177 43 340 ≤ 3005378154051956 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22240R_4827 c22240R_176_7 (by norm_num)

theorem c22240R_176_5 : rowsJ2 176 177 42 340 ≤ 3025427460327725 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22240R_4826 c22240R_176_6 (by norm_num)

theorem c22240R_176_4 : rowsJ2 176 177 41 340 ≤ 3043594067412721 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22240R_4825 c22240R_176_5 (by norm_num)

theorem c22240R_176_3 : rowsJ2 176 177 40 340 ≤ 3059947831340448 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22240R_4824 c22240R_176_4 (by norm_num)

theorem c22240R_176_2 : rowsJ2 176 177 38 340 ≤ 3087508321703371 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22240R_4823 c22240R_176_3 (by norm_num)

theorem c22240R_176_1 : rowsJ2 176 177 36 340 ≤ 3107742165359727 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22240R_4822 c22240R_176_2 (by norm_num)

theorem c22240R_176_0 : rowsJ2 176 177 0 340 ≤ 3126254492380717 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22240R_4821 c22240R_176_1 (by norm_num)

theorem hr22240R_176 : rows2 176 177 ≤ 3126254492380717 := rows2_le_of_rowsJ2 176 177 c22240R_176_0

theorem c22240R_177_13 : rowsJ2 177 178 50 340 ≤ 2871344746643186 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22240R_4850 rows22240R_4851 (by norm_num)

theorem c22240R_177_12 : rowsJ2 177 178 49 340 ≤ 2887300460707946 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22240R_4849 c22240R_177_13 (by norm_num)

theorem c22240R_177_11 : rowsJ2 177 178 48 340 ≤ 2905358981483953 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22240R_4848 c22240R_177_12 (by norm_num)

theorem c22240R_177_10 : rowsJ2 177 178 47 340 ≤ 2925671981979269 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22240R_4847 c22240R_177_11 (by norm_num)

theorem c22240R_177_9 : rowsJ2 177 178 46 340 ≤ 2948396488229680 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22240R_4846 c22240R_177_10 (by norm_num)

theorem c22240R_177_8 : rowsJ2 177 178 45 340 ≤ 2973695335373831 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22240R_4845 c22240R_177_9 (by norm_num)

theorem c22240R_177_7 : rowsJ2 177 178 44 340 ≤ 2999273299860559 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22240R_4844 c22240R_177_8 (by norm_num)

theorem c22240R_177_6 : rowsJ2 177 178 43 340 ≤ 3022758342368554 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22240R_4843 c22240R_177_7 (by norm_num)

theorem c22240R_177_5 : rowsJ2 177 178 42 340 ≤ 3044217173627200 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22240R_4842 c22240R_177_6 (by norm_num)

theorem c22240R_177_4 : rowsJ2 177 178 41 340 ≤ 3063718088964024 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22240R_4841 c22240R_177_5 (by norm_num)

theorem c22240R_177_3 : rowsJ2 177 178 40 340 ≤ 3081331276709791 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22240R_4840 c22240R_177_4 (by norm_num)

theorem c22240R_177_2 : rowsJ2 177 178 38 340 ≤ 3111186632012862 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22240R_4839 c22240R_177_3 (by norm_num)

theorem c22240R_177_1 : rowsJ2 177 178 36 340 ≤ 3133390573042600 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22240R_4838 c22240R_177_2 (by norm_num)

theorem c22240R_177_0 : rowsJ2 177 178 0 340 ≤ 3154872466112106 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22240R_4837 c22240R_177_1 (by norm_num)

theorem hr22240R_177 : rows2 177 178 ≤ 3154872466112106 := rows2_le_of_rowsJ2 177 178 c22240R_177_0

theorem c22240R_178_13 : rowsJ2 178 179 49 340 ≤ 2905317899152660 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22240R_4865 rows22240R_4866 (by norm_num)

theorem c22240R_178_12 : rowsJ2 178 179 48 340 ≤ 2922691994635562 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22240R_4864 c22240R_178_13 (by norm_num)

theorem c22240R_178_11 : rowsJ2 178 179 47 340 ≤ 2942292736333670 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22240R_4863 c22240R_178_12 (by norm_num)

theorem c22240R_178_10 : rowsJ2 178 179 46 340 ≤ 2964278184272298 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22240R_4862 c22240R_178_11 (by norm_num)

theorem c22240R_178_9 : rowsJ2 178 179 45 340 ≤ 2988812172756914 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22240R_4861 c22240R_178_10 (by norm_num)

theorem c22240R_178_8 : rowsJ2 178 179 44 340 ≤ 3016064800878937 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22240R_4860 c22240R_178_9 (by norm_num)

theorem c22240R_178_7 : rowsJ2 178 179 43 340 ≤ 3041146186483612 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22240R_4859 c22240R_178_8 (by norm_num)

theorem c22240R_178_6 : rowsJ2 178 179 42 340 ≤ 3064123771877794 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22240R_4858 c22240R_178_7 (by norm_num)

theorem c22240R_178_5 : rowsJ2 178 179 41 340 ≤ 3085066437076235 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22240R_4857 c22240R_178_6 (by norm_num)

theorem c22240R_178_4 : rowsJ2 178 179 40 340 ≤ 3104044812731454 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22240R_4856 c22240R_178_5 (by norm_num)

theorem c22240R_178_3 : rowsJ2 178 179 39 340 ≤ 3121131605294213 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22240R_4855 c22240R_178_4 (by norm_num)

theorem c22240R_178_2 : rowsJ2 178 179 37 340 ≤ 3149933701316169 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22240R_4854 c22240R_178_3 (by norm_num)

theorem c22240R_178_1 : rowsJ2 178 179 35 340 ≤ 3169055745537110 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22240R_4853 c22240R_178_2 (by norm_num)

theorem c22240R_178_0 : rowsJ2 178 179 0 340 ≤ 3185505406384692 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22240R_4852 c22240R_178_1 (by norm_num)

theorem hr22240R_178 : rows2 178 179 ≤ 3185505406384692 := rows2_le_of_rowsJ2 178 179 c22240R_178_0

theorem c22240R_179_12 : rowsJ2 179 180 48 340 ≤ 2995213716794264 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22240R_4879 rows22240R_4880 (by norm_num)

theorem c22240R_179_11 : rowsJ2 179 180 47 340 ≤ 3014069408573090 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22240R_4878 c22240R_179_12 (by norm_num)

theorem c22240R_179_10 : rowsJ2 179 180 46 340 ≤ 3035281833819166 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22240R_4877 c22240R_179_11 (by norm_num)

theorem c22240R_179_9 : rowsJ2 179 180 45 340 ≤ 3059015869774652 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22240R_4876 c22240R_179_10 (by norm_num)

theorem c22240R_179_8 : rowsJ2 179 180 44 340 ≤ 3085442624601330 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22240R_4875 c22240R_179_9 (by norm_num)

theorem c22240R_179_7 : rowsJ2 179 180 43 340 ≤ 3112164193586543 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22240R_4874 c22240R_179_8 (by norm_num)

theorem c22240R_179_6 : rowsJ2 179 180 42 340 ≤ 3136701514307842 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22240R_4873 c22240R_179_7 (by norm_num)

theorem c22240R_179_5 : rowsJ2 179 180 41 340 ≤ 3159124159968620 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22240R_4872 c22240R_179_6 (by norm_num)

theorem c22240R_179_4 : rowsJ2 179 180 40 340 ≤ 3179503303402343 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22240R_4871 c22240R_179_5 (by norm_num)

theorem c22240R_179_3 : rowsJ2 179 180 39 340 ≤ 3197912046633348 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22240R_4870 c22240R_179_4 (by norm_num)

theorem c22240R_179_2 : rowsJ2 179 180 37 340 ≤ 3229122462293594 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22240R_4869 c22240R_179_3 (by norm_num)

theorem c22240R_179_1 : rowsJ2 179 180 35 340 ≤ 3250178558180848 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22240R_4868 c22240R_179_2 (by norm_num)

theorem c22240R_179_0 : rowsJ2 179 180 0 340 ≤ 3269440557976193 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22240R_4867 c22240R_179_1 (by norm_num)

theorem hr22240R_179 : rows2 179 180 ≤ 3269440557976193 := rows2_le_of_rowsJ2 179 180 c22240R_179_0

theorem c22240R_180_11 : rowsJ2 180 181 47 340 ≤ 3138923155068250 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22240R_4892 rows22240R_4893 (by norm_num)

theorem c22240R_180_10 : rowsJ2 180 181 46 340 ≤ 3159398542831644 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22240R_4891 c22240R_180_11 (by norm_num)

theorem c22240R_180_9 : rowsJ2 180 181 45 340 ≤ 3182368198408965 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22240R_4890 c22240R_180_10 (by norm_num)

theorem c22240R_180_8 : rowsJ2 180 181 44 340 ≤ 3208004299879098 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22240R_4889 c22240R_180_9 (by norm_num)

theorem c22240R_180_7 : rowsJ2 180 181 43 340 ≤ 3236485752501960 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22240R_4888 c22240R_180_8 (by norm_num)

theorem c22240R_180_6 : rowsJ2 180 181 42 340 ≤ 3262700294621512 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22240R_4887 c22240R_180_7 (by norm_num)

theorem c22240R_180_5 : rowsJ2 180 181 41 340 ≤ 3286718330291723 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22240R_4886 c22240R_180_6 (by norm_num)

theorem c22240R_180_4 : rowsJ2 180 181 40 340 ≤ 3308611703250072 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22240R_4885 c22240R_180_5 (by norm_num)

theorem c22240R_180_3 : rowsJ2 180 181 39 340 ≤ 3328454031726273 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22240R_4884 c22240R_180_4 (by norm_num)

theorem c22240R_180_2 : rowsJ2 180 181 37 340 ≤ 3362291001229033 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22240R_4883 c22240R_180_3 (by norm_num)

theorem c22240R_180_1 : rowsJ2 180 181 35 340 ≤ 3385404913931497 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22240R_4882 c22240R_180_2 (by norm_num)

theorem c22240R_180_0 : rowsJ2 180 181 0 340 ≤ 3407763533842956 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22240R_4881 c22240R_180_1 (by norm_num)

theorem hr22240R_180 : rows2 180 181 ≤ 3407763533842956 := rows2_le_of_rowsJ2 180 181 c22240R_180_0

theorem c22240R_181_10 : rowsJ2 181 182 46 340 ≤ 3281437173644596 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22240R_4904 rows22240R_4905 (by norm_num)

theorem c22240R_181_9 : rowsJ2 181 182 45 340 ≤ 3303606520874928 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22240R_4903 c22240R_181_10 (by norm_num)

theorem c22240R_181_8 : rowsJ2 181 182 44 340 ≤ 3328414853370459 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22240R_4902 c22240R_181_9 (by norm_num)

theorem c22240R_181_7 : rowsJ2 181 182 43 340 ≤ 3356042158162992 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22240R_4901 c22240R_181_8 (by norm_num)

theorem c22240R_181_6 : rowsJ2 181 182 42 340 ≤ 3383981147664880 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22240R_4900 c22240R_181_7 (by norm_num)

theorem c22240R_181_5 : rowsJ2 181 182 41 340 ≤ 3409638706134932 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22240R_4899 c22240R_181_6 (by norm_num)

theorem c22240R_181_4 : rowsJ2 181 182 40 340 ≤ 3433087468159949 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22240R_4898 c22240R_181_5 (by norm_num)

theorem c22240R_181_3 : rowsJ2 181 182 39 340 ≤ 3454401678392889 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22240R_4897 c22240R_181_4 (by norm_num)

theorem c22240R_181_2 : rowsJ2 181 182 37 340 ≤ 3490933602770360 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22240R_4896 c22240R_181_3 (by norm_num)

theorem c22240R_181_1 : rowsJ2 181 182 34 340 ≤ 3524935884176473 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22240R_4895 c22240R_181_2 (by norm_num)

theorem c22240R_181_0 : rowsJ2 181 182 0 340 ≤ 3542061750027747 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22240R_4894 c22240R_181_1 (by norm_num)

theorem hr22240R_181 : rows2 181 182 ≤ 3542061750027747 := rows2_le_of_rowsJ2 181 182 c22240R_181_0

theorem c22240R_182_10 : rowsJ2 182 183 45 340 ≤ 3422931397358962 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22240R_4916 rows22240R_4917 (by norm_num)

theorem c22240R_182_9 : rowsJ2 182 183 44 340 ≤ 3446948767313714 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22240R_4915 c22240R_182_10 (by norm_num)

theorem c22240R_182_8 : rowsJ2 182 183 43 340 ≤ 3473758365544380 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22240R_4914 c22240R_182_9 (by norm_num)

theorem c22240R_182_7 : rowsJ2 182 183 42 340 ≤ 3503548559531340 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22240R_4913 c22240R_182_8 (by norm_num)

theorem c22240R_182_6 : rowsJ2 182 183 41 340 ≤ 3530969979487085 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22240R_4912 c22240R_182_7 (by norm_num)

theorem c22240R_182_5 : rowsJ2 182 183 40 340 ≤ 3556096202627374 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22240R_4911 c22240R_182_6 (by norm_num)

theorem c22240R_182_4 : rowsJ2 182 183 39 340 ≤ 3579002241698617 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22240R_4910 c22240R_182_5 (by norm_num)

theorem c22240R_182_3 : rowsJ2 182 183 38 340 ≤ 3599764903736977 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22240R_4909 c22240R_182_4 (by norm_num)

theorem c22240R_182_2 : rowsJ2 182 183 36 340 ≤ 3633773408486243 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22240R_4908 c22240R_182_3 (by norm_num)

theorem c22240R_182_1 : rowsJ2 182 183 34 340 ≤ 3655705004904367 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22240R_4907 c22240R_182_2 (by norm_num)

theorem c22240R_182_0 : rowsJ2 182 183 0 340 ≤ 3675764980854981 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22240R_4906 c22240R_182_1 (by norm_num)

theorem hr22240R_182 : rows2 182 183 ≤ 3675764980854981 := rows2_le_of_rowsJ2 182 183 c22240R_182_0

theorem c22240R_183_9 : rowsJ2 183 184 44 340 ≤ 3563288491104979 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22240R_4927 rows22240R_4928 (by norm_num)

theorem c22240R_183_8 : rowsJ2 183 184 43 340 ≤ 3589241102037823 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22240R_4926 c22240R_183_9 (by norm_num)

theorem c22240R_183_7 : rowsJ2 183 184 42 340 ≤ 3618147476126705 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22240R_4925 c22240R_183_8 (by norm_num)

theorem c22240R_183_6 : rowsJ2 183 184 41 340 ≤ 3647383686452897 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22240R_4924 c22240R_183_7 (by norm_num)

theorem c22240R_183_5 : rowsJ2 183 184 40 340 ≤ 3674234948411384 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22240R_4923 c22240R_183_6 (by norm_num)

theorem c22240R_183_4 : rowsJ2 183 184 39 340 ≤ 3698777175725412 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22240R_4922 c22240R_183_5 (by norm_num)

theorem c22240R_183_3 : rowsJ2 183 184 38 340 ≤ 3721087896989778 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22240R_4921 c22240R_183_4 (by norm_num)

theorem c22240R_183_2 : rowsJ2 183 184 36 340 ≤ 3757889227119698 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22240R_4920 c22240R_183_3 (by norm_num)

theorem c22240R_183_1 : rowsJ2 183 184 34 340 ≤ 3781972353883785 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22240R_4919 c22240R_183_2 (by norm_num)

theorem c22240R_183_0 : rowsJ2 183 184 0 340 ≤ 3805264449131171 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22240R_4918 c22240R_183_1 (by norm_num)

theorem hr22240R_183 : rows2 183 184 ≤ 3805264449131171 := rows2_le_of_rowsJ2 183 184 c22240R_183_0

theorem c22240R_184_8 : rowsJ2 184 185 43 340 ≤ 3702725825854281 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22240R_4937 rows22240R_4938 (by norm_num)

theorem c22240R_184_7 : rowsJ2 184 185 42 340 ≤ 3730786112555902 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22240R_4936 c22240R_184_8 (by norm_num)

theorem c22240R_184_6 : rowsJ2 184 185 41 340 ≤ 3761971499687915 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22240R_4935 c22240R_184_7 (by norm_num)

theorem c22240R_184_5 : rowsJ2 184 185 40 340 ≤ 3790679541757849 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22240R_4934 c22240R_184_6 (by norm_num)

theorem c22240R_184_4 : rowsJ2 184 185 39 340 ≤ 3816987221180013 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22240R_4933 c22240R_184_5 (by norm_num)

theorem c22240R_184_3 : rowsJ2 184 185 38 340 ≤ 3840972944363026 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22240R_4932 c22240R_184_4 (by norm_num)

theorem c22240R_184_2 : rowsJ2 184 185 36 340 ≤ 3880727158538704 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22240R_4931 c22240R_184_3 (by norm_num)

theorem c22240R_184_1 : rowsJ2 184 185 33 340 ≤ 3916166083098272 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22240R_4930 c22240R_184_2 (by norm_num)

theorem c22240R_184_0 : rowsJ2 184 185 0 340 ≤ 3934012082687241 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22240R_4929 c22240R_184_1 (by norm_num)

theorem hr22240R_184 : rows2 184 185 ≤ 3934012082687241 := rows2_le_of_rowsJ2 184 185 c22240R_184_0

theorem c22240R_185_8 : rowsJ2 185 186 42 340 ≤ 3841148362330868 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22240R_4947 rows22240R_4948 (by norm_num)

theorem c22240R_185_7 : rowsJ2 185 186 41 340 ≤ 3871418781789315 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22240R_4946 c22240R_185_8 (by norm_num)

theorem c22240R_185_6 : rowsJ2 185 186 40 340 ≤ 3902038588875120 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22240R_4945 c22240R_185_7 (by norm_num)

theorem c22240R_185_5 : rowsJ2 185 186 39 340 ≤ 3930163069283926 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22240R_4944 c22240R_185_6 (by norm_num)

theorem c22240R_185_4 : rowsJ2 185 186 38 340 ≤ 3955871654783622 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22240R_4943 c22240R_185_5 (by norm_num)

theorem c22240R_185_3 : rowsJ2 185 186 37 340 ≤ 3979245389959499 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22240R_4942 c22240R_185_4 (by norm_num)

theorem c22240R_185_2 : rowsJ2 185 186 35 340 ≤ 4014709757367095 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22240R_4941 c22240R_185_3 (by norm_num)

theorem c22240R_185_1 : rowsJ2 185 186 33 340 ≤ 4037574298301951 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22240R_4940 c22240R_185_2 (by norm_num)

theorem c22240R_185_0 : rowsJ2 185 186 0 340 ≤ 4058484331638629 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22240R_4939 c22240R_185_1 (by norm_num)

theorem hr22240R_185 : rows2 185 186 ≤ 4058484331638629 := rows2_le_of_rowsJ2 185 186 c22240R_185_0

theorem c22240R_186_7 : rowsJ2 186 187 41 340 ≤ 3978789301842619 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22240R_4956 rows22240R_4957 (by norm_num)

theorem c22240R_186_6 : rowsJ2 186 187 40 340 ≤ 4011463520669336 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22240R_4955 c22240R_186_7 (by norm_num)

theorem c22240R_186_5 : rowsJ2 186 187 39 340 ≤ 4041544551457786 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22240R_4954 c22240R_186_6 (by norm_num)

theorem c22240R_186_4 : rowsJ2 186 187 38 340 ≤ 4069113037078636 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22240R_4953 c22240R_186_5 (by norm_num)

theorem c22240R_186_3 : rowsJ2 186 187 37 340 ≤ 4094251023990934 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22240R_4952 c22240R_186_4 (by norm_num)

theorem c22240R_186_2 : rowsJ2 186 187 35 340 ≤ 4132642039166531 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22240R_4951 c22240R_186_3 (by norm_num)

theorem c22240R_186_1 : rowsJ2 186 187 33 340 ≤ 4157758323518779 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22240R_4950 c22240R_186_2 (by norm_num)

theorem c22240R_186_0 : rowsJ2 186 187 0 340 ≤ 4182045108026074 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22240R_4949 c22240R_186_1 (by norm_num)

theorem hr22240R_186 : rows2 186 187 ≤ 4182045108026074 := rows2_le_of_rowsJ2 186 187 c22240R_186_0

theorem c22240R_187_6 : rowsJ2 187 188 40 340 ≤ 4115501228988191 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22240R_4964 rows22240R_4965 (by norm_num)

theorem c22240R_187_5 : rowsJ2 187 188 39 340 ≤ 4147598244912869 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22240R_4963 c22240R_187_6 (by norm_num)

theorem c22240R_187_4 : rowsJ2 187 188 38 340 ≤ 4177082114278508 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22240R_4962 c22240R_187_5 (by norm_num)

theorem c22240R_187_3 : rowsJ2 187 188 37 340 ≤ 4204036049619474 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22240R_4961 c22240R_187_4 (by norm_num)

theorem c22240R_187_2 : rowsJ2 187 188 35 340 ≤ 4245523254886688 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22240R_4960 c22240R_187_3 (by norm_num)

theorem c22240R_187_1 : rowsJ2 187 188 32 340 ≤ 4282494029169202 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22240R_4959 c22240R_187_2 (by norm_num)

theorem c22240R_187_0 : rowsJ2 187 188 0 340 ≤ 4301107563817899 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22240R_4958 c22240R_187_1 (by norm_num)

theorem hr22240R_187 : rows2 187 188 ≤ 4301107563817899 := rows2_le_of_rowsJ2 187 188 c22240R_187_0

theorem c22240R_188_5 : rowsJ2 188 189 39 340 ≤ 4251353023368657 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22240R_4971 rows22240R_4972 (by norm_num)

theorem c22240R_188_4 : rowsJ2 188 189 38 340 ≤ 4282900701758479 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22240R_4970 c22240R_188_5 (by norm_num)

theorem c22240R_188_3 : rowsJ2 188 189 37 340 ≤ 4311816038584810 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22240R_4969 c22240R_188_4 (by norm_num)

theorem c22240R_188_2 : rowsJ2 188 189 35 340 ≤ 4356576233024901 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22240R_4968 c22240R_188_3 (by norm_num)

theorem c22240R_188_1 : rowsJ2 188 189 32 340 ≤ 4397097739306173 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22240R_4967 c22240R_188_2 (by norm_num)

theorem c22240R_188_0 : rowsJ2 188 189 0 340 ≤ 4418914053334986 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22240R_4966 c22240R_188_1 (by norm_num)

theorem hr22240R_188 : rows2 188 189 ≤ 4418914053334986 := rows2_le_of_rowsJ2 188 189 c22240R_188_0

theorem c22240R_189_5 : rowsJ2 189 190 38 340 ≤ 4383096531217439 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22240R_4978 rows22240R_4979 (by norm_num)

theorem c22240R_189_4 : rowsJ2 189 190 37 340 ≤ 4414033293799006 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22240R_4977 c22240R_189_5 (by norm_num)

theorem c22240R_189_3 : rowsJ2 189 190 36 340 ≤ 4440290343868998 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22240R_4976 c22240R_189_4 (by norm_num)

theorem c22240R_189_2 : rowsJ2 189 190 34 340 ≤ 4480378263038958 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22240R_4975 c22240R_189_3 (by norm_num)

theorem c22240R_189_1 : rowsJ2 189 190 32 340 ≤ 4506596810135951 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22240R_4974 c22240R_189_2 (by norm_num)

theorem c22240R_189_0 : rowsJ2 189 190 0 340 ≤ 4531944396081292 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22240R_4973 c22240R_189_1 (by norm_num)

theorem hr22240R_189 : rows2 189 190 ≤ 4531944396081292 := rows2_le_of_rowsJ2 189 190 c22240R_189_0

theorem c22240R_190_4 : rowsJ2 190 191 37 340 ≤ 4513894635109356 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22240R_4984 rows22240R_4985 (by norm_num)

theorem c22240R_190_3 : rowsJ2 190 191 36 340 ≤ 4542060104604168 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22240R_4983 c22240R_190_4 (by norm_num)

theorem c22240R_190_2 : rowsJ2 190 191 34 340 ≤ 4585397951717407 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22240R_4982 c22240R_190_3 (by norm_num)

theorem c22240R_190_1 : rowsJ2 190 191 31 340 ≤ 4624003510818132 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22240R_4981 c22240R_190_2 (by norm_num)

theorem c22240R_190_0 : rowsJ2 190 191 0 340 ≤ 4643435792189808 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22240R_4980 c22240R_190_1 (by norm_num)

theorem hr22240R_190 : rows2 190 191 ≤ 4643435792189808 := rows2_le_of_rowsJ2 190 191 c22240R_190_0

theorem c22240R_191_3 : rowsJ2 191 192 36 340 ≤ 4638470577267100 :=
  rowsJ2_le_of_split 191 192 (by norm_num) (by norm_num) rows22240R_4989 rows22240R_4990 (by norm_num)

theorem c22240R_191_2 : rowsJ2 191 192 34 340 ≤ 4685246039731948 :=
  rowsJ2_le_of_split 191 192 (by norm_num) (by norm_num) rows22240R_4988 c22240R_191_3 (by norm_num)

theorem c22240R_191_1 : rowsJ2 191 192 31 340 ≤ 4727574678060939 :=
  rowsJ2_le_of_split 191 192 (by norm_num) (by norm_num) rows22240R_4987 c22240R_191_2 (by norm_num)

theorem c22240R_191_0 : rowsJ2 191 192 0 340 ≤ 4750358043210391 :=
  rowsJ2_le_of_split 191 192 (by norm_num) (by norm_num) rows22240R_4986 c22240R_191_1 (by norm_num)

theorem hr22240R_191 : rows2 191 192 ≤ 4750358043210391 := rows2_le_of_rowsJ2 191 192 c22240R_191_0

theorem c22240R_192_2 : rowsJ2 192 193 34 340 ≤ 4782844493583579 :=
  rowsJ2_le_of_split 192 193 (by norm_num) (by norm_num) rows22240R_4993 rows22240R_4994 (by norm_num)

theorem c22240R_192_1 : rowsJ2 192 193 31 340 ≤ 4829183202919863 :=
  rowsJ2_le_of_split 192 193 (by norm_num) (by norm_num) rows22240R_4992 c22240R_192_2 (by norm_num)

theorem c22240R_192_0 : rowsJ2 192 193 0 340 ≤ 4855663082367628 :=
  rowsJ2_le_of_split 192 193 (by norm_num) (by norm_num) rows22240R_4991 c22240R_192_1 (by norm_num)

theorem hr22240R_192 : rows2 192 193 ≤ 4855663082367628 := rows2_le_of_rowsJ2 192 193 c22240R_192_0

theorem c22240R_193_2 : rowsJ2 193 194 33 340 ≤ 4900914622882334 :=
  rowsJ2_le_of_split 193 194 (by norm_num) (by norm_num) rows22240R_4997 rows22240R_4998 (by norm_num)

theorem c22240R_193_1 : rowsJ2 193 194 31 340 ≤ 4930945991707602 :=
  rowsJ2_le_of_split 193 194 (by norm_num) (by norm_num) rows22240R_4996 c22240R_193_2 (by norm_num)

theorem c22240R_193_0 : rowsJ2 193 194 0 340 ≤ 4961572828567470 :=
  rowsJ2_le_of_split 193 194 (by norm_num) (by norm_num) rows22240R_4995 c22240R_193_1 (by norm_num)

theorem hr22240R_193 : rows2 193 194 ≤ 4961572828567470 := rows2_le_of_rowsJ2 193 194 c22240R_193_0

theorem c22240R_194_2 : rowsJ2 194 195 33 340 ≤ 5000027043377892 :=
  rowsJ2_le_of_split 194 195 (by norm_num) (by norm_num) rows22240R_5001 rows22240R_5002 (by norm_num)

theorem c22240R_194_1 : rowsJ2 194 195 30 340 ≤ 5044286748720889 :=
  rowsJ2_le_of_split 194 195 (by norm_num) (by norm_num) rows22240R_5000 c22240R_194_2 (by norm_num)

theorem c22240R_194_0 : rowsJ2 194 195 0 340 ≤ 5068102933710114 :=
  rowsJ2_le_of_split 194 195 (by norm_num) (by norm_num) rows22240R_4999 c22240R_194_1 (by norm_num)

theorem hr22240R_194 : rows2 194 195 ≤ 5068102933710114 := rows2_le_of_rowsJ2 194 195 c22240R_194_0

theorem c22240R_195_1 : rowsJ2 195 196 30 340 ≤ 5147604469701864 :=
  rowsJ2_le_of_split 195 196 (by norm_num) (by norm_num) rows22240R_5004 rows22240R_5005 (by norm_num)

theorem c22240R_195_0 : rowsJ2 195 196 0 340 ≤ 5175294051416758 :=
  rowsJ2_le_of_split 195 196 (by norm_num) (by norm_num) rows22240R_5003 c22240R_195_1 (by norm_num)

theorem hr22240R_195 : rows2 195 196 ≤ 5175294051416758 := rows2_le_of_rowsJ2 195 196 c22240R_195_0

theorem c22240R_196_1 : rowsJ2 196 197 30 340 ≤ 5251104990751825 :=
  rowsJ2_le_of_split 196 197 (by norm_num) (by norm_num) rows22240R_5007 rows22240R_5008 (by norm_num)

theorem c22240R_196_0 : rowsJ2 196 197 0 340 ≤ 5283141946022975 :=
  rowsJ2_le_of_split 196 197 (by norm_num) (by norm_num) rows22240R_5006 c22240R_196_1 (by norm_num)

theorem hr22240R_196 : rows2 196 197 ≤ 5283141946022975 := rows2_le_of_rowsJ2 196 197 c22240R_196_0

theorem c22240R_197_1 : rowsJ2 197 198 29 340 ≤ 5366723365541435 :=
  rowsJ2_le_of_split 197 198 (by norm_num) (by norm_num) rows22240R_5010 rows22240R_5011 (by norm_num)

theorem c22240R_197_0 : rowsJ2 197 198 0 340 ≤ 5391643640747075 :=
  rowsJ2_le_of_split 197 198 (by norm_num) (by norm_num) rows22240R_5009 c22240R_197_1 (by norm_num)

theorem hr22240R_197 : rows2 197 198 ≤ 5391643640747075 := rows2_le_of_rowsJ2 197 198 c22240R_197_0

theorem c22240R_198_0 : rowsJ2 198 199 0 340 ≤ 5500727503920550 :=
  rowsJ2_le_of_split 198 199 (by norm_num) (by norm_num) rows22240R_5012 rows22240R_5013 (by norm_num)

theorem hr22240R_198 : rows2 198 199 ≤ 5500727503920550 := rows2_le_of_rowsJ2 198 199 c22240R_198_0

theorem c22240R_199_0 : rowsJ2 199 200 0 340 ≤ 5611049483370703 :=
  rowsJ2_le_of_split 199 200 (by norm_num) (by norm_num) rows22240R_5014 rows22240R_5015 (by norm_num)

theorem hr22240R_199 : rows2 199 200 ≤ 5611049483370703 := rows2_le_of_rowsJ2 199 200 c22240R_199_0

theorem c22240R_200_0 : rowsJ2 200 201 0 340 ≤ 5723282621946092 :=
  rowsJ2_le_of_split 200 201 (by norm_num) (by norm_num) rows22240R_5016 rows22240R_5017 (by norm_num)

theorem hr22240R_200 : rows2 200 201 ≤ 5723282621946092 := rows2_le_of_rowsJ2 200 201 c22240R_200_0

theorem c22240R_201_0 : rowsJ2 201 202 0 340 ≤ 5837331113621144 :=
  rowsJ2_le_of_split 201 202 (by norm_num) (by norm_num) rows22240R_5018 rows22240R_5019 (by norm_num)

theorem hr22240R_201 : rows2 201 202 ≤ 5837331113621144 := rows2_le_of_rowsJ2 201 202 c22240R_201_0

theorem t22240R_236 : rows2 336 340 ≤ 54747938989286175 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5064 rows22240R_5065 (by norm_num)

theorem t22240R_235 : rows2 333 340 ≤ 93382038015527092 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5063 t22240R_236 (by norm_num)

theorem t22240R_234 : rows2 330 340 ≤ 130088465793773369 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5062 t22240R_235 (by norm_num)

theorem t22240R_233 : rows2 327 340 ≤ 165081126017367369 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5061 t22240R_234 (by norm_num)

theorem t22240R_232 : rows2 324 340 ≤ 198436030219582413 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5060 t22240R_233 (by norm_num)

theorem t22240R_231 : rows2 320 340 ≤ 240635212784509122 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5059 t22240R_232 (by norm_num)

theorem t22240R_230 : rows2 272 340 ≤ 272481207251452027 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5058 t22240R_231 (by norm_num)

theorem t22240R_229 : rows2 270 340 ≤ 293526844977684325 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5057 t22240R_230 (by norm_num)

theorem t22240R_228 : rows2 268 340 ≤ 314456617278203510 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5056 t22240R_229 (by norm_num)

theorem t22240R_227 : rows2 266 340 ≤ 335268963732763738 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5055 t22240R_228 (by norm_num)

theorem t22240R_226 : rows2 264 340 ≤ 355962797771667015 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5054 t22240R_227 (by norm_num)

theorem t22240R_225 : rows2 262 340 ≤ 376537851053719672 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5053 t22240R_226 (by norm_num)

theorem t22240R_224 : rows2 260 340 ≤ 396994234618750007 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5052 t22240R_225 (by norm_num)

theorem t22240R_223 : rows2 258 340 ≤ 417332336392662853 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5051 t22240R_224 (by norm_num)

theorem t22240R_222 : rows2 256 340 ≤ 437553195661717314 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5050 t22240R_223 (by norm_num)

theorem t22240R_221 : rows2 254 340 ≤ 457658075432331663 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5049 t22240R_222 (by norm_num)

theorem t22240R_220 : rows2 252 340 ≤ 477648393416130224 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5048 t22240R_221 (by norm_num)

theorem t22240R_219 : rows2 250 340 ≤ 497526095348600653 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5047 t22240R_220 (by norm_num)

theorem t22240R_218 : rows2 248 340 ≤ 517293255515234673 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5046 t22240R_219 (by norm_num)

theorem t22240R_217 : rows2 246 340 ≤ 536952007797174679 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5045 t22240R_218 (by norm_num)

theorem t22240R_216 : rows2 244 340 ≤ 556504937819520504 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5044 t22240R_217 (by norm_num)

theorem t22240R_215 : rows2 242 340 ≤ 575954209070575570 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5043 t22240R_216 (by norm_num)

theorem t22240R_214 : rows2 240 340 ≤ 595299353158147675 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5042 t22240R_215 (by norm_num)

theorem t22240R_213 : rows2 238 340 ≤ 614539474137014819 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5041 t22240R_214 (by norm_num)

theorem t22240R_212 : rows2 236 340 ≤ 633673850586995301 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5040 t22240R_213 (by norm_num)

theorem t22240R_211 : rows2 234 340 ≤ 652495781869969716 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5039 t22240R_212 (by norm_num)

theorem t22240R_210 : rows2 232 340 ≤ 670815485787699095 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5038 t22240R_211 (by norm_num)

theorem t22240R_209 : rows2 230 340 ≤ 688655960529095767 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5037 t22240R_210 (by norm_num)

theorem t22240R_208 : rows2 228 340 ≤ 706038341915369704 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5036 t22240R_209 (by norm_num)

theorem t22240R_207 : rows2 226 340 ≤ 722982194606480863 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5035 t22240R_208 (by norm_num)

theorem t22240R_206 : rows2 224 340 ≤ 739505574374516880 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5034 t22240R_207 (by norm_num)

theorem t22240R_205 : rows2 222 340 ≤ 755625283782455714 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5033 t22240R_206 (by norm_num)

theorem t22240R_204 : rows2 220 340 ≤ 771360372525228426 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5032 t22240R_205 (by norm_num)

theorem t22240R_203 : rows2 218 340 ≤ 786735852325033237 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5031 t22240R_204 (by norm_num)

theorem t22240R_202 : rows2 216 340 ≤ 801776195533585331 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5030 t22240R_203 (by norm_num)

theorem t22240R_201 : rows2 214 340 ≤ 816504840014494380 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5029 t22240R_202 (by norm_num)

theorem t22240R_200 : rows2 212 340 ≤ 830944156069008524 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5028 t22240R_201 (by norm_num)

theorem t22240R_199 : rows2 210 340 ≤ 845063564327495469 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5027 t22240R_200 (by norm_num)

theorem t22240R_198 : rows2 208 340 ≤ 858623196607451159 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5026 t22240R_199 (by norm_num)

theorem t22240R_197 : rows2 207 340 ≤ 865200326664071135 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5025 t22240R_198 (by norm_num)

theorem t22240R_196 : rows2 206 340 ≤ 871646393234519714 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5024 t22240R_197 (by norm_num)

theorem t22240R_195 : rows2 205 340 ≤ 877964459285486275 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5023 t22240R_196 (by norm_num)

theorem t22240R_194 : rows2 204 340 ≤ 884157729838193165 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5022 t22240R_195 (by norm_num)

theorem t22240R_193 : rows2 203 340 ≤ 890229385004339124 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5021 t22240R_194 (by norm_num)

theorem t22240R_192 : rows2 202 340 ≤ 896182604265884118 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_5020 t22240R_193 (by norm_num)

theorem t22240R_191 : rows2 201 340 ≤ 902019935379505262 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_201 t22240R_192 (by norm_num)

theorem t22240R_190 : rows2 200 340 ≤ 907743218001451354 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_200 t22240R_191 (by norm_num)

theorem t22240R_189 : rows2 199 340 ≤ 913354267484822057 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_199 t22240R_190 (by norm_num)

theorem t22240R_188 : rows2 198 340 ≤ 918854994988742607 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_198 t22240R_189 (by norm_num)

theorem t22240R_187 : rows2 197 340 ≤ 924246638629489682 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_197 t22240R_188 (by norm_num)

theorem t22240R_186 : rows2 196 340 ≤ 929529780575512657 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_196 t22240R_187 (by norm_num)

theorem t22240R_185 : rows2 195 340 ≤ 934705074626929415 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_195 t22240R_186 (by norm_num)

theorem t22240R_184 : rows2 194 340 ≤ 939773177560639529 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_194 t22240R_185 (by norm_num)

theorem t22240R_183 : rows2 193 340 ≤ 944734750389206999 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_193 t22240R_184 (by norm_num)

theorem t22240R_182 : rows2 192 340 ≤ 949590413471574627 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_192 t22240R_183 (by norm_num)

theorem t22240R_181 : rows2 191 340 ≤ 954340771514785018 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_191 t22240R_182 (by norm_num)

theorem t22240R_180 : rows2 190 340 ≤ 958984207306974826 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_190 t22240R_181 (by norm_num)

theorem t22240R_179 : rows2 189 340 ≤ 963516151703056118 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_189 t22240R_180 (by norm_num)

theorem t22240R_178 : rows2 188 340 ≤ 967935065756391104 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_188 t22240R_179 (by norm_num)

theorem t22240R_177 : rows2 187 340 ≤ 972236173320209003 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_187 t22240R_178 (by norm_num)

theorem t22240R_176 : rows2 186 340 ≤ 976418218428235077 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_186 t22240R_177 (by norm_num)

theorem t22240R_175 : rows2 185 340 ≤ 980476702759873706 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_185 t22240R_176 (by norm_num)

theorem t22240R_174 : rows2 184 340 ≤ 984410714842560947 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_184 t22240R_175 (by norm_num)

theorem t22240R_173 : rows2 183 340 ≤ 988215979291692118 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_183 t22240R_174 (by norm_num)

theorem t22240R_172 : rows2 182 340 ≤ 991891744272547099 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_182 t22240R_173 (by norm_num)

theorem t22240R_171 : rows2 181 340 ≤ 995433806022574846 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_181 t22240R_172 (by norm_num)

theorem t22240R_170 : rows2 180 340 ≤ 998841569556417802 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_180 t22240R_171 (by norm_num)

theorem t22240R_169 : rows2 179 340 ≤ 1002111010114393995 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_179 t22240R_170 (by norm_num)

theorem t22240R_168 : rows2 178 340 ≤ 1005296515520778687 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_178 t22240R_169 (by norm_num)

theorem t22240R_167 : rows2 177 340 ≤ 1008451387986890793 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_177 t22240R_168 (by norm_num)

theorem t22240R_166 : rows2 176 340 ≤ 1011577642479271510 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_176 t22240R_167 (by norm_num)

theorem t22240R_165 : rows2 175 340 ≤ 1014674610236392147 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_175 t22240R_166 (by norm_num)

theorem t22240R_164 : rows2 174 340 ≤ 1017744970744493887 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_174 t22240R_165 (by norm_num)

theorem t22240R_163 : rows2 173 340 ≤ 1020788507369088521 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_173 t22240R_164 (by norm_num)

theorem t22240R_162 : rows2 172 340 ≤ 1023808349676160432 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_172 t22240R_163 (by norm_num)

theorem t22240R_161 : rows2 171 340 ≤ 1026804511169420837 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_171 t22240R_162 (by norm_num)

theorem t22240R_160 : rows2 170 340 ≤ 1029780304141669824 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_170 t22240R_161 (by norm_num)

theorem t22240R_159 : rows2 169 340 ≤ 1032735541725619492 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_169 t22240R_160 (by norm_num)

theorem t22240R_158 : rows2 168 340 ≤ 1035673734857802610 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_168 t22240R_159 (by norm_num)

theorem t22240R_157 : rows2 167 340 ≤ 1038594892489651899 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_167 t22240R_158 (by norm_num)

theorem t22240R_156 : rows2 166 340 ≤ 1041502304048066121 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_166 t22240R_157 (by norm_num)

theorem t22240R_155 : rows2 165 340 ≤ 1044396181240402480 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_165 t22240R_156 (by norm_num)

theorem t22240R_154 : rows2 164 340 ≤ 1047279975167490464 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_164 t22240R_155 (by norm_num)

theorem t22240R_153 : rows2 163 340 ≤ 1050153692648759009 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_163 t22240R_154 (by norm_num)

theorem t22240R_152 : rows2 162 340 ≤ 1053020953518285719 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_162 t22240R_153 (by norm_num)

theorem t22240R_151 : rows2 161 340 ≤ 1055881938231746764 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_161 t22240R_152 (by norm_num)

theorem t22240R_150 : rows2 160 340 ≤ 1058740035190421318 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_160 t22240R_151 (by norm_num)

theorem t22240R_149 : rows2 159 340 ≤ 1061595612657776279 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_159 t22240R_150 (by norm_num)

theorem t22240R_148 : rows2 158 340 ≤ 1064452196380417952 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_158 t22240R_149 (by norm_num)

theorem t22240R_147 : rows2 157 340 ≤ 1067308588101058630 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_157 t22240R_148 (by norm_num)

theorem t22240R_146 : rows2 156 340 ≤ 1070167114960130583 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_156 t22240R_147 (by norm_num)

theorem t22240R_145 : rows2 155 340 ≤ 1072907705843319189 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_155 t22240R_146 (by norm_num)

theorem t22240R_144 : rows2 154 340 ≤ 1075530626782192767 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_154 t22240R_145 (by norm_num)

theorem t22240R_143 : rows2 153 340 ≤ 1078033164861883902 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_153 t22240R_144 (by norm_num)

theorem t22240R_142 : rows2 152 340 ≤ 1080415681526703984 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_152 t22240R_143 (by norm_num)

theorem t22240R_141 : rows2 151 340 ≤ 1082675214576104726 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_151 t22240R_142 (by norm_num)

theorem t22240R_140 : rows2 150 340 ≤ 1084812405151593284 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_150 t22240R_141 (by norm_num)

theorem t22240R_139 : rows2 149 340 ≤ 1086824404984587325 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_149 t22240R_140 (by norm_num)

theorem t22240R_138 : rows2 148 340 ≤ 1088711557632080543 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_148 t22240R_139 (by norm_num)

theorem t22240R_137 : rows2 147 340 ≤ 1090472828672792768 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_147 t22240R_138 (by norm_num)

theorem t22240R_136 : rows2 146 340 ≤ 1092208188867863157 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_146 t22240R_137 (by norm_num)

theorem t22240R_135 : rows2 145 340 ≤ 1093813894192591022 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_145 t22240R_136 (by norm_num)

theorem t22240R_134 : rows2 144 340 ≤ 1095384527051664562 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_144 t22240R_135 (by norm_num)

theorem t22240R_133 : rows2 143 340 ≤ 1096819129564765082 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_143 t22240R_134 (by norm_num)

theorem t22240R_132 : rows2 142 340 ≤ 1098208926265981156 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_142 t22240R_133 (by norm_num)

theorem t22240R_131 : rows2 141 340 ≤ 1099455749968963628 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_141 t22240R_132 (by norm_num)

theorem t22240R_130 : rows2 140 340 ≤ 1100647406132503858 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_140 t22240R_131 (by norm_num)

theorem t22240R_129 : rows2 139 340 ≤ 1101688695323605864 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_139 t22240R_130 (by norm_num)

theorem t22240R_128 : rows2 138 340 ≤ 1102664893803680846 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_138 t22240R_129 (by norm_num)

theorem t22240R_127 : rows2 137 340 ≤ 1103483011340917715 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_137 t22240R_128 (by norm_num)

theorem t22240R_126 : rows2 136 340 ≤ 1104225199600823410 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_136 t22240R_127 (by norm_num)

theorem t22240R_125 : rows2 135 340 ≤ 1104963286394397069 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_135 t22240R_126 (by norm_num)

theorem t22240R_124 : rows2 134 340 ≤ 1105783455104034804 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_134 t22240R_125 (by norm_num)

theorem t22240R_123 : rows2 133 340 ≤ 1106603749436907601 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_133 t22240R_124 (by norm_num)

theorem t22240R_122 : rows2 132 340 ≤ 1107508780687909811 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_132 t22240R_123 (by norm_num)

theorem t22240R_121 : rows2 131 340 ≤ 1108418385537621724 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_131 t22240R_122 (by norm_num)

theorem t22240R_120 : rows2 130 340 ≤ 1109415270240222685 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_130 t22240R_121 (by norm_num)

theorem t22240R_119 : rows2 129 340 ≤ 1110418962115618097 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_129 t22240R_120 (by norm_num)

theorem t22240R_118 : rows2 128 340 ≤ 1111512063614596145 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_128 t22240R_119 (by norm_num)

theorem t22240R_117 : rows2 127 340 ≤ 1112613019579199582 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_127 t22240R_118 (by norm_num)

theorem t22240R_116 : rows2 126 340 ≤ 1113805030913697081 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_126 t22240R_117 (by norm_num)

theorem t22240R_115 : rows2 125 340 ≤ 1115005493508787793 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_125 t22240R_116 (by norm_num)

theorem t22240R_114 : rows2 124 340 ≤ 1116299108732446024 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_124 t22240R_115 (by norm_num)

theorem t22240R_113 : rows2 123 340 ≤ 1117602093614895914 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_123 t22240R_114 (by norm_num)

theorem t22240R_112 : rows2 122 340 ≤ 1119000830757438176 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_122 t22240R_113 (by norm_num)

theorem t22240R_111 : rows2 121 340 ≤ 1120410384700487943 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_121 t22240R_112 (by norm_num)

theorem t22240R_110 : rows2 120 340 ≤ 1121918831006049283 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_120 t22240R_111 (by norm_num)

theorem t22240R_109 : rows2 119 340 ≤ 1123440696374185614 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_119 t22240R_110 (by norm_num)

theorem t22240R_108 : rows2 118 340 ≤ 1125065850116703967 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_118 t22240R_109 (by norm_num)

theorem t22240R_107 : rows2 117 340 ≤ 1126707609714997660 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_117 t22240R_108 (by norm_num)

theorem t22240R_106 : rows2 116 340 ≤ 1128457526640994940 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_116 t22240R_107 (by norm_num)

theorem t22240R_105 : rows2 115 340 ≤ 1130226140052884364 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_115 t22240R_106 (by norm_num)

theorem t22240R_104 : rows2 114 340 ≤ 1132137591947921603 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_114 t22240R_105 (by norm_num)

theorem t22240R_103 : rows2 113 340 ≤ 1133885561920816053 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_113 t22240R_104 (by norm_num)

theorem t22240R_102 : rows2 112 340 ≤ 1135559318393711494 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_112 t22240R_103 (by norm_num)

theorem t22240R_101 : rows2 111 340 ≤ 1137059769632608886 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_111 t22240R_102 (by norm_num)

theorem t22240R_100 : rows2 110 340 ≤ 1138477770909519010 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_110 t22240R_101 (by norm_num)

theorem t22240R_99 : rows2 109 340 ≤ 1139712140700259333 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_109 t22240R_100 (by norm_num)

theorem t22240R_98 : rows2 108 340 ≤ 1140855492007349931 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_108 t22240R_99 (by norm_num)

theorem t22240R_97 : rows2 107 340 ≤ 1141805699500647271 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_107 t22240R_98 (by norm_num)

theorem t22240R_96 : rows2 106 340 ≤ 1142656996044343369 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_106 t22240R_97 (by norm_num)

theorem t22240R_95 : rows2 105 340 ≤ 1143304937282367517 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_105 t22240R_96 (by norm_num)

theorem t22240R_94 : rows2 104 340 ≤ 1143845611967427609 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_104 t22240R_95 (by norm_num)

theorem t22240R_93 : rows2 103 340 ≤ 1144138333293177349 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_103 t22240R_94 (by norm_num)

theorem t22240R_92 : rows2 102 340 ≤ 1144417728623581075 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_102 t22240R_93 (by norm_num)

theorem t22240R_91 : rows2 101 340 ≤ 1144685053389086938 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_101 t22240R_92 (by norm_num)

theorem t22240R_90 : rows2 100 340 ≤ 1144945562971657730 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_100 t22240R_91 (by norm_num)

theorem t22240R_89 : rows2 99 340 ≤ 1145199615646591750 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_99 t22240R_90 (by norm_num)

theorem t22240R_88 : rows2 98 340 ≤ 1145451471976382248 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_98 t22240R_89 (by norm_num)

theorem t22240R_87 : rows2 97 340 ≤ 1145700164934083799 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_97 t22240R_88 (by norm_num)

theorem t22240R_86 : rows2 96 340 ≤ 1145948380064834382 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_96 t22240R_87 (by norm_num)

theorem t22240R_85 : rows2 95 340 ≤ 1146194738905452257 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_95 t22240R_86 (by norm_num)

theorem t22240R_84 : rows2 94 340 ≤ 1146440216912185188 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_94 t22240R_85 (by norm_num)

theorem t22240R_83 : rows2 93 340 ≤ 1146681420777822464 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_93 t22240R_84 (by norm_num)

theorem t22240R_82 : rows2 92 340 ≤ 1146918035059350957 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_92 t22240R_83 (by norm_num)

theorem t22240R_81 : rows2 91 340 ≤ 1147143405865688477 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_91 t22240R_82 (by norm_num)

theorem t22240R_80 : rows2 90 340 ≤ 1147354592350030641 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_90 t22240R_81 (by norm_num)

theorem t22240R_79 : rows2 89 340 ≤ 1147542008509977081 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_89 t22240R_80 (by norm_num)

theorem t22240R_78 : rows2 88 340 ≤ 1147701472842717092 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_88 t22240R_79 (by norm_num)

theorem t22240R_77 : rows2 87 340 ≤ 1147829388600499005 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_87 t22240R_78 (by norm_num)

theorem t22240R_76 : rows2 86 340 ≤ 1147931102887628940 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_86 t22240R_77 (by norm_num)

theorem t22240R_75 : rows2 85 340 ≤ 1148009539398242295 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_85 t22240R_76 (by norm_num)

theorem t22240R_74 : rows2 84 340 ≤ 1148072028419658551 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_84 t22240R_75 (by norm_num)

theorem t22240R_73 : rows2 83 340 ≤ 1148121714198548147 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_83 t22240R_74 (by norm_num)

theorem t22240R_72 : rows2 82 340 ≤ 1148163301398533295 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_82 t22240R_73 (by norm_num)

theorem t22240R_71 : rows2 81 340 ≤ 1148198001365294123 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_81 t22240R_72 (by norm_num)

theorem t22240R_70 : rows2 80 340 ≤ 1148230320885341993 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_80 t22240R_71 (by norm_num)

theorem t22240R_69 : rows2 79 340 ≤ 1148260618005741263 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_79 t22240R_70 (by norm_num)

theorem t22240R_68 : rows2 78 340 ≤ 1148292523334937492 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_78 t22240R_69 (by norm_num)

theorem t22240R_67 : rows2 77 340 ≤ 1148326926570986878 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_77 t22240R_68 (by norm_num)

theorem t22240R_66 : rows2 76 340 ≤ 1148366315025075188 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_76 t22240R_67 (by norm_num)

theorem t22240R_65 : rows2 75 340 ≤ 1148413499389605074 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_75 t22240R_66 (by norm_num)

theorem t22240R_64 : rows2 74 340 ≤ 1148469067258958173 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_74 t22240R_65 (by norm_num)

theorem t22240R_63 : rows2 73 340 ≤ 1148534568362059833 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_73 t22240R_64 (by norm_num)

theorem t22240R_62 : rows2 72 340 ≤ 1148611301471566268 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_72 t22240R_63 (by norm_num)

theorem t22240R_61 : rows2 71 340 ≤ 1148699715267846953 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_71 t22240R_62 (by norm_num)

theorem t22240R_60 : rows2 70 340 ≤ 1148800110538301979 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_70 t22240R_61 (by norm_num)

theorem t22240R_59 : rows2 69 340 ≤ 1148910997511088019 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_69 t22240R_60 (by norm_num)

theorem t22240R_58 : rows2 68 340 ≤ 1149031082315406464 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_68 t22240R_59 (by norm_num)

theorem t22240R_57 : rows2 67 340 ≤ 1149158449987237714 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_67 t22240R_58 (by norm_num)

theorem t22240R_56 : rows2 66 340 ≤ 1149291397923513476 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_66 t22240R_57 (by norm_num)

theorem t22240R_55 : rows2 65 340 ≤ 1149428084254482814 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_65 t22240R_56 (by norm_num)

theorem t22240R_54 : rows2 64 340 ≤ 1149566726916882880 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_64 t22240R_55 (by norm_num)

theorem t22240R_53 : rows2 63 340 ≤ 1149704471824204287 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_63 t22240R_54 (by norm_num)

theorem t22240R_52 : rows2 62 340 ≤ 1149838639531068605 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_62 t22240R_53 (by norm_num)

theorem t22240R_51 : rows2 61 340 ≤ 1149965273809963878 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_61 t22240R_52 (by norm_num)

theorem t22240R_50 : rows2 60 340 ≤ 1150080883053682530 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_60 t22240R_51 (by norm_num)

theorem t22240R_49 : rows2 59 340 ≤ 1150184085026045025 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_59 t22240R_50 (by norm_num)

theorem t22240R_48 : rows2 58 340 ≤ 1150274674615787398 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_58 t22240R_49 (by norm_num)

theorem t22240R_47 : rows2 57 340 ≤ 1150352673030006177 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_57 t22240R_48 (by norm_num)

theorem t22240R_46 : rows2 56 340 ≤ 1150418451413987438 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_56 t22240R_47 (by norm_num)

theorem t22240R_45 : rows2 55 340 ≤ 1150472932994863357 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_55 t22240R_46 (by norm_num)

theorem t22240R_44 : rows2 54 340 ≤ 1150517557142578569 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_54 t22240R_45 (by norm_num)

theorem t22240R_43 : rows2 53 340 ≤ 1150553819260921938 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_53 t22240R_44 (by norm_num)

theorem t22240R_42 : rows2 52 340 ≤ 1150583106063081544 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_52 t22240R_43 (by norm_num)

theorem t22240R_41 : rows2 51 340 ≤ 1150606824149232948 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_51 t22240R_42 (by norm_num)

theorem t22240R_40 : rows2 50 340 ≤ 1150626476019151951 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_50 t22240R_41 (by norm_num)

theorem t22240R_39 : rows2 49 340 ≤ 1150643214621795485 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_49 t22240R_40 (by norm_num)

theorem t22240R_38 : rows2 48 340 ≤ 1150658042275555988 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_48 t22240R_39 (by norm_num)

theorem t22240R_37 : rows2 47 340 ≤ 1150671954217740846 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_47 t22240R_38 (by norm_num)

theorem t22240R_36 : rows2 46 340 ≤ 1150685868900231568 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_46 t22240R_37 (by norm_num)

theorem t22240R_35 : rows2 45 340 ≤ 1150700337417987912 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_45 t22240R_36 (by norm_num)

theorem t22240R_34 : rows2 44 340 ≤ 1150715788456650182 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_44 t22240R_35 (by norm_num)

theorem t22240R_33 : rows2 43 340 ≤ 1150732390793262249 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_43 t22240R_34 (by norm_num)

theorem t22240R_32 : rows2 42 340 ≤ 1150750317923746542 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_42 t22240R_33 (by norm_num)

theorem t22240R_31 : rows2 41 340 ≤ 1150769500592286292 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_41 t22240R_32 (by norm_num)

theorem t22240R_30 : rows2 40 340 ≤ 1150789857135962542 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_40 t22240R_31 (by norm_num)

theorem t22240R_29 : rows2 39 340 ≤ 1150811235394205886 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_39 t22240R_30 (by norm_num)

theorem t22240R_28 : rows2 38 340 ≤ 1150833551643008936 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_38 t22240R_29 (by norm_num)

theorem t22240R_27 : rows2 37 340 ≤ 1150856517284414877 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_37 t22240R_28 (by norm_num)

theorem t22240R_26 : rows2 36 340 ≤ 1150879604083959745 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_36 t22240R_27 (by norm_num)

theorem t22240R_25 : rows2 35 340 ≤ 1150902649805401553 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_35 t22240R_26 (by norm_num)

theorem t22240R_24 : rows2 34 340 ≤ 1150925558179940411 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_34 t22240R_25 (by norm_num)

theorem t22240R_23 : rows2 33 340 ≤ 1150948306998664022 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_33 t22240R_24 (by norm_num)

theorem t22240R_22 : rows2 32 340 ≤ 1150970900677579595 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_32 t22240R_23 (by norm_num)

theorem t22240R_21 : rows2 31 340 ≤ 1150993227111321514 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_31 t22240R_22 (by norm_num)

theorem t22240R_20 : rows2 30 340 ≤ 1151015098754960193 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_30 t22240R_21 (by norm_num)

theorem t22240R_19 : rows2 29 340 ≤ 1151036264316812305 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_29 t22240R_20 (by norm_num)

theorem t22240R_18 : rows2 28 340 ≤ 1151056463458439705 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_28 t22240R_19 (by norm_num)

theorem t22240R_17 : rows2 27 340 ≤ 1151075431023996978 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_27 t22240R_18 (by norm_num)

theorem t22240R_16 : rows2 26 340 ≤ 1151092930714115287 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_26 t22240R_17 (by norm_num)

theorem t22240R_15 : rows2 25 340 ≤ 1151108776079018336 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_25 t22240R_16 (by norm_num)

theorem t22240R_14 : rows2 24 340 ≤ 1151122840106444791 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_24 t22240R_15 (by norm_num)

theorem t22240R_13 : rows2 23 340 ≤ 1151135079888397019 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_23 t22240R_14 (by norm_num)

theorem t22240R_12 : rows2 22 340 ≤ 1151145603726293463 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_22 t22240R_13 (by norm_num)

theorem t22240R_11 : rows2 21 340 ≤ 1151154619627137933 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_21 t22240R_12 (by norm_num)

theorem t22240R_10 : rows2 20 340 ≤ 1151162450145441631 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_20 t22240R_11 (by norm_num)

theorem t22240R_9 : rows2 19 340 ≤ 1151169450072286934 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_19 t22240R_10 (by norm_num)

theorem t22240R_8 : rows2 18 340 ≤ 1151175958522174339 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_18 t22240R_9 (by norm_num)

theorem t22240R_7 : rows2 17 340 ≤ 1151182292624588716 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_17 t22240R_8 (by norm_num)

theorem t22240R_6 : rows2 16 340 ≤ 1151188631956336891 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_16 t22240R_7 (by norm_num)

theorem t22240R_5 : rows2 15 340 ≤ 1151194982278661459 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_15 t22240R_6 (by norm_num)

theorem t22240R_4 : rows2 14 340 ≤ 1151201224945936485 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22240R_14 t22240R_5 (by norm_num)

theorem t22240R_3 : rows2 13 340 ≤ 1151207158881018589 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_3 t22240R_4 (by norm_num)

theorem t22240R_2 : rows2 12 340 ≤ 1151212580299177810 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_2 t22240R_3 (by norm_num)

theorem t22240R_1 : rows2 10 340 ≤ 1151221156361317587 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_1 t22240R_2 (by norm_num)

theorem t22240R_0 : rows2 0 340 ≤ 1151230848467235036 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22240R_0 t22240R_1 (by norm_num)

/-- **The refined certificate on `grid22240R`**: the loss's bound is less than `K`, the 5066 parts checked by the
kernel. -/
theorem total2_lt_22240R : total2 < K := by
  rw [total2_eq_rows2_full]
  exact lt_of_le_of_lt t22240R_0 (by decide +kernel)

end

end SieveCert

#print axioms SieveCert.total2_lt_22240R
