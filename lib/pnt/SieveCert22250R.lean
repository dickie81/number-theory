/-
# The refined certificate of the sieve route's loss at `L = 89/40` with `n = 360`: `total2 < K`

On `SieveGrid22250R.grid22250R` (`U1 = ⌈(41479/100000)DEN⌉`, `U2 = ⌊(47555/100000)DEN⌋`, `n = 360`),
`SieveCert.total2` is less than `K` (it is below `0.99358K`, rounded up; the certificate of `SieveCertDefs.lean` on
the same grid totals `1.11520K`): `total2` is `rows2 0 n` (`SieveCert2.total2_eq_rows2_full`), and its bound is
assembled one step at a time from the 5796 parts' bounds (`rows22250R_0` … `rows22250R_5795`, each by `decide
+kernel` in one of the 465 part files): a heavy row's bound from its column pieces' (`rowsJ2_le_of_split`,
`rows2_le_of_rowsJ2`), then the 254 ranges of rows from the last to the first (`rows2_le_of_split`), every bound a
literal and every step a theorem of its own (`c22250R_…`, `hr22250R_…`, `t22250R_…`); the bounds, `⌈1.001 × part⌉`
computed exactly in integers, sum to `1146656663135250298`, less than `K` by `decide +kernel` (`total2_lt_22250R`).

The file imports `SieveCert2.lean` and `SieveCert22250RP1.lean` … `SieveCert22250RP465.lean`.
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
import SieveCert22250RP352
import SieveCert22250RP353
import SieveCert22250RP354
import SieveCert22250RP355
import SieveCert22250RP356
import SieveCert22250RP357
import SieveCert22250RP358
import SieveCert22250RP359
import SieveCert22250RP360
import SieveCert22250RP361
import SieveCert22250RP362
import SieveCert22250RP363
import SieveCert22250RP364
import SieveCert22250RP365
import SieveCert22250RP366
import SieveCert22250RP367
import SieveCert22250RP368
import SieveCert22250RP369
import SieveCert22250RP370
import SieveCert22250RP371
import SieveCert22250RP372
import SieveCert22250RP373
import SieveCert22250RP374
import SieveCert22250RP375
import SieveCert22250RP376
import SieveCert22250RP377
import SieveCert22250RP378
import SieveCert22250RP379
import SieveCert22250RP380
import SieveCert22250RP381
import SieveCert22250RP382
import SieveCert22250RP383
import SieveCert22250RP384
import SieveCert22250RP385
import SieveCert22250RP386
import SieveCert22250RP387
import SieveCert22250RP388
import SieveCert22250RP389
import SieveCert22250RP390
import SieveCert22250RP391
import SieveCert22250RP392
import SieveCert22250RP393
import SieveCert22250RP394
import SieveCert22250RP395
import SieveCert22250RP396
import SieveCert22250RP397
import SieveCert22250RP398
import SieveCert22250RP399
import SieveCert22250RP400
import SieveCert22250RP401
import SieveCert22250RP402
import SieveCert22250RP403
import SieveCert22250RP404
import SieveCert22250RP405
import SieveCert22250RP406
import SieveCert22250RP407
import SieveCert22250RP408
import SieveCert22250RP409
import SieveCert22250RP410
import SieveCert22250RP411
import SieveCert22250RP412
import SieveCert22250RP413
import SieveCert22250RP414
import SieveCert22250RP415
import SieveCert22250RP416
import SieveCert22250RP417
import SieveCert22250RP418
import SieveCert22250RP419
import SieveCert22250RP420
import SieveCert22250RP421
import SieveCert22250RP422
import SieveCert22250RP423
import SieveCert22250RP424
import SieveCert22250RP425
import SieveCert22250RP426
import SieveCert22250RP427
import SieveCert22250RP428
import SieveCert22250RP429
import SieveCert22250RP430
import SieveCert22250RP431
import SieveCert22250RP432
import SieveCert22250RP433
import SieveCert22250RP434
import SieveCert22250RP435
import SieveCert22250RP436
import SieveCert22250RP437
import SieveCert22250RP438
import SieveCert22250RP439
import SieveCert22250RP440
import SieveCert22250RP441
import SieveCert22250RP442
import SieveCert22250RP443
import SieveCert22250RP444
import SieveCert22250RP445
import SieveCert22250RP446
import SieveCert22250RP447
import SieveCert22250RP448
import SieveCert22250RP449
import SieveCert22250RP450
import SieveCert22250RP451
import SieveCert22250RP452
import SieveCert22250RP453
import SieveCert22250RP454
import SieveCert22250RP455
import SieveCert22250RP456
import SieveCert22250RP457
import SieveCert22250RP458
import SieveCert22250RP459
import SieveCert22250RP460
import SieveCert22250RP461
import SieveCert22250RP462
import SieveCert22250RP463
import SieveCert22250RP464
import SieveCert22250RP465

namespace SieveCert

section

attribute [local instance] grid22250R

/-! The chain of bounds: `c22250R_{i}_{m}` for the heavy row `i` from its `m`-th column piece on, `hr22250R_{i}` for
the heavy row `i`, `t22250R_{m}` for the rows from the `m`-th range on; each a theorem of its own, its name distinct
from the other certificates' chains in the same namespace. -/

theorem c22250R_14_0 : rowsJ2 14 15 0 360 ≤ 4012516434634 :=
  rowsJ2_le_of_split 14 15 (by norm_num) (by norm_num) rows22250R_4 rows22250R_5 (by norm_num)

theorem hr22250R_14 : rows2 14 15 ≤ 4012516434634 := rows2_le_of_rowsJ2 14 15 c22250R_14_0

theorem c22250R_15_0 : rowsJ2 15 16 0 360 ≤ 3968921115783 :=
  rowsJ2_le_of_split 15 16 (by norm_num) (by norm_num) rows22250R_6 rows22250R_7 (by norm_num)

theorem hr22250R_15 : rows2 15 16 ≤ 3968921115783 := rows2_le_of_rowsJ2 15 16 c22250R_15_0

theorem c22250R_16_0 : rowsJ2 16 17 0 360 ≤ 3882654240961 :=
  rowsJ2_le_of_split 16 17 (by norm_num) (by norm_num) rows22250R_8 rows22250R_9 (by norm_num)

theorem hr22250R_16 : rows2 16 17 ≤ 3882654240961 := rows2_le_of_rowsJ2 16 17 c22250R_16_0

theorem c22250R_17_1 : rowsJ2 17 18 14 360 ≤ 970796683838 :=
  rowsJ2_le_of_split 17 18 (by norm_num) (by norm_num) rows22250R_11 rows22250R_12 (by norm_num)

theorem c22250R_17_0 : rowsJ2 17 18 0 360 ≤ 3851651848036 :=
  rowsJ2_le_of_split 17 18 (by norm_num) (by norm_num) rows22250R_10 c22250R_17_1 (by norm_num)

theorem hr22250R_17 : rows2 17 18 ≤ 3851651848036 := rows2_le_of_rowsJ2 17 18 c22250R_17_0

theorem c22250R_18_1 : rowsJ2 18 19 14 360 ≤ 1348192903767 :=
  rowsJ2_le_of_split 18 19 (by norm_num) (by norm_num) rows22250R_14 rows22250R_15 (by norm_num)

theorem c22250R_18_0 : rowsJ2 18 19 0 360 ≤ 3983039858009 :=
  rowsJ2_le_of_split 18 19 (by norm_num) (by norm_num) rows22250R_13 c22250R_18_1 (by norm_num)

theorem hr22250R_18 : rows2 18 19 ≤ 3983039858009 := rows2_le_of_rowsJ2 18 19 c22250R_18_0

theorem c22250R_19_2 : rowsJ2 19 20 17 360 ≤ 1451028875391 :=
  rowsJ2_le_of_split 19 20 (by norm_num) (by norm_num) rows22250R_18 rows22250R_19 (by norm_num)

theorem c22250R_19_1 : rowsJ2 19 20 14 360 ≤ 1999611926401 :=
  rowsJ2_le_of_split 19 20 (by norm_num) (by norm_num) rows22250R_17 c22250R_19_2 (by norm_num)

theorem c22250R_19_0 : rowsJ2 19 20 0 360 ≤ 4402173952750 :=
  rowsJ2_le_of_split 19 20 (by norm_num) (by norm_num) rows22250R_16 c22250R_19_1 (by norm_num)

theorem hr22250R_19 : rows2 19 20 ≤ 4402173952750 := rows2_le_of_rowsJ2 19 20 c22250R_19_0

theorem c22250R_20_3 : rowsJ2 20 21 19 360 ≤ 1608566119871 :=
  rowsJ2_le_of_split 20 21 (by norm_num) (by norm_num) rows22250R_23 rows22250R_24 (by norm_num)

theorem c22250R_20_2 : rowsJ2 20 21 17 360 ≤ 2428888155952 :=
  rowsJ2_le_of_split 20 21 (by norm_num) (by norm_num) rows22250R_22 c22250R_20_3 (by norm_num)

theorem c22250R_20_1 : rowsJ2 20 21 14 360 ≤ 2931976844343 :=
  rowsJ2_le_of_split 20 21 (by norm_num) (by norm_num) rows22250R_21 c22250R_20_2 (by norm_num)

theorem c22250R_20_0 : rowsJ2 20 21 0 360 ≤ 5110500462345 :=
  rowsJ2_le_of_split 20 21 (by norm_num) (by norm_num) rows22250R_20 c22250R_20_1 (by norm_num)

theorem hr22250R_20 : rows2 20 21 ≤ 5110500462345 := rows2_le_of_rowsJ2 20 21 c22250R_20_0

theorem c22250R_21_4 : rowsJ2 21 22 20 360 ≤ 2104139095939 :=
  rowsJ2_le_of_split 21 22 (by norm_num) (by norm_num) rows22250R_29 rows22250R_30 (by norm_num)

theorem c22250R_21_3 : rowsJ2 21 22 19 360 ≤ 2823505164101 :=
  rowsJ2_le_of_split 21 22 (by norm_num) (by norm_num) rows22250R_28 c22250R_21_4 (by norm_num)

theorem c22250R_21_2 : rowsJ2 21 22 17 360 ≤ 3688482173207 :=
  rowsJ2_le_of_split 21 22 (by norm_num) (by norm_num) rows22250R_27 c22250R_21_3 (by norm_num)

theorem c22250R_21_1 : rowsJ2 21 22 14 360 ≤ 4167995309837 :=
  rowsJ2_le_of_split 21 22 (by norm_num) (by norm_num) rows22250R_26 c22250R_21_2 (by norm_num)

theorem c22250R_21_0 : rowsJ2 21 22 0 360 ≤ 6135672941051 :=
  rowsJ2_le_of_split 21 22 (by norm_num) (by norm_num) rows22250R_25 c22250R_21_1 (by norm_num)

theorem hr22250R_21 : rows2 21 22 ≤ 6135672941051 := rows2_le_of_rowsJ2 21 22 c22250R_21_0

theorem c22250R_22_5 : rowsJ2 22 23 21 360 ≤ 2572462475873 :=
  rowsJ2_le_of_split 22 23 (by norm_num) (by norm_num) rows22250R_36 rows22250R_37 (by norm_num)

theorem c22250R_22_4 : rowsJ2 22 23 20 360 ≤ 3542986000670 :=
  rowsJ2_le_of_split 22 23 (by norm_num) (by norm_num) rows22250R_35 c22250R_22_5 (by norm_num)

theorem c22250R_22_3 : rowsJ2 22 23 19 360 ≤ 4291585853973 :=
  rowsJ2_le_of_split 22 23 (by norm_num) (by norm_num) rows22250R_34 c22250R_22_4 (by norm_num)

theorem c22250R_22_2 : rowsJ2 22 23 17 360 ≤ 5206513288213 :=
  rowsJ2_le_of_split 22 23 (by norm_num) (by norm_num) rows22250R_33 c22250R_22_3 (by norm_num)

theorem c22250R_22_1 : rowsJ2 22 23 14 360 ≤ 5671039889671 :=
  rowsJ2_le_of_split 22 23 (by norm_num) (by norm_num) rows22250R_32 c22250R_22_2 (by norm_num)

theorem c22250R_22_0 : rowsJ2 22 23 0 360 ≤ 7435898785839 :=
  rowsJ2_le_of_split 22 23 (by norm_num) (by norm_num) rows22250R_31 c22250R_22_1 (by norm_num)

theorem hr22250R_22 : rows2 22 23 ≤ 7435898785839 := rows2_le_of_rowsJ2 22 23 c22250R_22_0

theorem c22250R_23_6 : rowsJ2 23 24 22 360 ≤ 2904701732884 :=
  rowsJ2_le_of_split 23 24 (by norm_num) (by norm_num) rows22250R_44 rows22250R_45 (by norm_num)

theorem c22250R_23_5 : rowsJ2 23 24 21 360 ≤ 4118836837705 :=
  rowsJ2_le_of_split 23 24 (by norm_num) (by norm_num) rows22250R_43 c22250R_23_6 (by norm_num)

theorem c22250R_23_4 : rowsJ2 23 24 20 360 ≤ 5123323509643 :=
  rowsJ2_le_of_split 23 24 (by norm_num) (by norm_num) rows22250R_42 c22250R_23_5 (by norm_num)

theorem c22250R_23_3 : rowsJ2 23 24 19 360 ≤ 5902139145866 :=
  rowsJ2_le_of_split 23 24 (by norm_num) (by norm_num) rows22250R_41 c22250R_23_4 (by norm_num)

theorem c22250R_23_2 : rowsJ2 23 24 17 360 ≤ 6866163314263 :=
  rowsJ2_le_of_split 23 24 (by norm_num) (by norm_num) rows22250R_40 c22250R_23_3 (by norm_num)

theorem c22250R_23_1 : rowsJ2 23 24 14 360 ≤ 7342728614013 :=
  rowsJ2_le_of_split 23 24 (by norm_num) (by norm_num) rows22250R_39 c22250R_23_2 (by norm_num)

theorem c22250R_23_0 : rowsJ2 23 24 0 360 ≤ 8917552431123 :=
  rowsJ2_le_of_split 23 24 (by norm_num) (by norm_num) rows22250R_38 c22250R_23_1 (by norm_num)

theorem hr22250R_23 : rows2 23 24 ≤ 8917552431123 := rows2_le_of_rowsJ2 23 24 c22250R_23_0

theorem c22250R_24_7 : rowsJ2 24 25 23 360 ≤ 3095283804145 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22250R_53 rows22250R_54 (by norm_num)

theorem c22250R_24_6 : rowsJ2 24 25 22 360 ≤ 4477387017967 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22250R_52 c22250R_24_7 (by norm_num)

theorem c22250R_24_5 : rowsJ2 24 25 21 360 ≤ 5705323168577 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22250R_51 c22250R_24_6 (by norm_num)

theorem c22250R_24_4 : rowsJ2 24 25 20 360 ≤ 6741878488683 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22250R_50 c22250R_24_5 (by norm_num)

theorem c22250R_24_3 : rowsJ2 24 25 19 360 ≤ 7560034902874 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22250R_49 c22250R_24_4 (by norm_num)

theorem c22250R_24_2 : rowsJ2 24 25 17 360 ≤ 8581473162544 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22250R_48 c22250R_24_3 (by norm_num)

theorem c22250R_24_1 : rowsJ2 24 25 14 360 ≤ 9072804449674 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22250R_47 c22250R_24_2 (by norm_num)

theorem c22250R_24_0 : rowsJ2 24 25 0 360 ≤ 10467824058014 :=
  rowsJ2_le_of_split 24 25 (by norm_num) (by norm_num) rows22250R_46 c22250R_24_1 (by norm_num)

theorem hr22250R_24 : rows2 24 25 ≤ 10467824058014 := rows2_le_of_rowsJ2 24 25 c22250R_24_0

theorem c22250R_25_8 : rowsJ2 25 26 24 360 ≤ 3127937705858 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22250R_63 rows22250R_64 (by norm_num)

theorem c22250R_25_7 : rowsJ2 25 26 23 360 ≤ 4611142836905 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22250R_62 c22250R_25_8 (by norm_num)

theorem c22250R_25_6 : rowsJ2 25 26 22 360 ≤ 5984889056332 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22250R_61 c22250R_25_7 (by norm_num)

theorem c22250R_25_5 : rowsJ2 25 26 21 360 ≤ 7218762673565 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22250R_60 c22250R_25_6 (by norm_num)

theorem c22250R_25_4 : rowsJ2 25 26 20 360 ≤ 8281767840258 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22250R_59 c22250R_25_5 (by norm_num)

theorem c22250R_25_3 : rowsJ2 25 26 19 360 ≤ 9140192004365 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22250R_58 c22250R_25_4 (by norm_num)

theorem c22250R_25_2 : rowsJ2 25 26 17 360 ≤ 10222585537388 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22250R_57 c22250R_25_3 (by norm_num)

theorem c22250R_25_1 : rowsJ2 25 26 14 360 ≤ 10753160052575 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22250R_56 c22250R_25_2 (by norm_num)

theorem c22250R_25_0 : rowsJ2 25 26 0 360 ≤ 11981219477289 :=
  rowsJ2_le_of_split 25 26 (by norm_num) (by norm_num) rows22250R_55 c22250R_25_1 (by norm_num)

theorem hr22250R_25 : rows2 25 26 ≤ 11981219477289 := rows2_le_of_rowsJ2 25 26 c22250R_25_0

theorem c22250R_26_9 : rowsJ2 26 27 25 360 ≤ 3039898614230 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22250R_74 rows22250R_75 (by norm_num)

theorem c22250R_26_8 : rowsJ2 26 27 24 360 ≤ 4544774355665 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22250R_73 c22250R_26_9 (by norm_num)

theorem c22250R_26_7 : rowsJ2 26 27 23 360 ≤ 5997939433139 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22250R_72 c22250R_26_8 (by norm_num)

theorem c22250R_26_6 : rowsJ2 26 27 22 360 ≤ 7360861457637 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22250R_71 c22250R_26_7 (by norm_num)

theorem c22250R_26_5 : rowsJ2 26 27 21 360 ≤ 8595993567648 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22250R_70 c22250R_26_6 (by norm_num)

theorem c22250R_26_4 : rowsJ2 26 27 20 360 ≤ 9677385016356 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22250R_69 c22250R_26_5 (by norm_num)

theorem c22250R_26_3 : rowsJ2 26 27 19 360 ≤ 10570317623134 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22250R_68 c22250R_26_4 (by norm_num)

theorem c22250R_26_2 : rowsJ2 26 27 17 360 ≤ 11728565853171 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22250R_67 c22250R_26_3 (by norm_num)

theorem c22250R_26_1 : rowsJ2 26 27 14 360 ≤ 12303815954150 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22250R_66 c22250R_26_2 (by norm_num)

theorem c22250R_26_0 : rowsJ2 26 27 0 360 ≤ 13374599968239 :=
  rowsJ2_le_of_split 26 27 (by norm_num) (by norm_num) rows22250R_65 c22250R_26_1 (by norm_num)

theorem hr22250R_26 : rows2 26 27 ≤ 13374599968239 := rows2_le_of_rowsJ2 26 27 c22250R_26_0

theorem c22250R_27_10 : rowsJ2 27 28 26 360 ≤ 2892387417952 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_86 rows22250R_87 (by norm_num)

theorem c22250R_27_9 : rowsJ2 27 28 25 360 ≤ 4355230501752 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_85 c22250R_27_10 (by norm_num)

theorem c22250R_27_8 : rowsJ2 27 28 24 360 ≤ 5805688405766 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_84 c22250R_27_9 (by norm_num)

theorem c22250R_27_7 : rowsJ2 27 28 23 360 ≤ 7226030835536 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_83 c22250R_27_8 (by norm_num)

theorem c22250R_27_6 : rowsJ2 27 28 22 360 ≤ 8571165338177 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_82 c22250R_27_7 (by norm_num)

theorem c22250R_27_5 : rowsJ2 27 28 21 360 ≤ 9804930569933 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_81 c22250R_27_6 (by norm_num)

theorem c22250R_27_4 : rowsJ2 27 28 20 360 ≤ 10894705515290 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_80 c22250R_27_5 (by norm_num)

theorem c22250R_27_3 : rowsJ2 27 28 19 360 ≤ 11813943258309 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_79 c22250R_27_4 (by norm_num)

theorem c22250R_27_2 : rowsJ2 27 28 17 360 ≤ 13052399787473 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_78 c22250R_27_3 (by norm_num)

theorem c22250R_27_1 : rowsJ2 27 28 14 360 ≤ 13687837815658 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_77 c22250R_27_2 (by norm_num)

theorem c22250R_27_0 : rowsJ2 27 28 0 360 ≤ 14616345510343 :=
  rowsJ2_le_of_split 27 28 (by norm_num) (by norm_num) rows22250R_76 c22250R_27_1 (by norm_num)

theorem hr22250R_27 : rows2 27 28 ≤ 14616345510343 := rows2_le_of_rowsJ2 27 28 c22250R_27_0

theorem c22250R_28_11 : rowsJ2 28 29 27 360 ≤ 2668709787161 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_99 rows22250R_100 (by norm_num)

theorem c22250R_28_10 : rowsJ2 28 29 26 360 ≤ 4065813520396 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_98 c22250R_28_11 (by norm_num)

theorem c22250R_28_9 : rowsJ2 28 29 25 360 ≤ 5469849695060 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_97 c22250R_28_10 (by norm_num)

theorem c22250R_28_8 : rowsJ2 28 29 24 360 ≤ 6869761800885 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_96 c22250R_28_9 (by norm_num)

theorem c22250R_28_7 : rowsJ2 28 29 23 360 ≤ 8247504906908 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_95 c22250R_28_8 (by norm_num)

theorem c22250R_28_6 : rowsJ2 28 29 22 360 ≤ 9571900130061 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_94 c22250R_28_7 (by norm_num)

theorem c22250R_28_5 : rowsJ2 28 29 21 360 ≤ 10797179333775 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_93 c22250R_28_6 (by norm_num)

theorem c22250R_28_4 : rowsJ2 28 29 20 360 ≤ 11892588342411 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_92 c22250R_28_5 (by norm_num)

theorem c22250R_28_3 : rowsJ2 28 29 19 360 ≤ 12832569871060 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_91 c22250R_28_4 (by norm_num)

theorem c22250R_28_2 : rowsJ2 28 29 17 360 ≤ 14146347174731 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_90 c22250R_28_3 (by norm_num)

theorem c22250R_28_1 : rowsJ2 28 29 14 360 ≤ 14851206815070 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_89 c22250R_28_2 (by norm_num)

theorem c22250R_28_0 : rowsJ2 28 29 0 360 ≤ 15655261180940 :=
  rowsJ2_le_of_split 28 29 (by norm_num) (by norm_num) rows22250R_88 c22250R_28_1 (by norm_num)

theorem hr22250R_28 : rows2 28 29 ≤ 15655261180940 := rows2_le_of_rowsJ2 28 29 c22250R_28_0

theorem c22250R_29_12 : rowsJ2 29 30 28 360 ≤ 2405849868242 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_113 rows22250R_114 (by norm_num)

theorem c22250R_29_11 : rowsJ2 29 30 27 360 ≤ 3694932210879 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_112 c22250R_29_12 (by norm_num)

theorem c22250R_29_10 : rowsJ2 29 30 26 360 ≤ 5025380590848 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_111 c22250R_29_11 (by norm_num)

theorem c22250R_29_9 : rowsJ2 29 30 25 360 ≤ 6377217283247 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_110 c22250R_29_10 (by norm_num)

theorem c22250R_29_8 : rowsJ2 29 30 24 360 ≤ 7723402240704 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_109 c22250R_29_9 (by norm_num)

theorem c22250R_29_7 : rowsJ2 29 30 23 360 ≤ 9055796832696 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_108 c22250R_29_8 (by norm_num)

theorem c22250R_29_6 : rowsJ2 29 30 22 360 ≤ 10349509394609 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_107 c22250R_29_7 (by norm_num)

theorem c22250R_29_5 : rowsJ2 29 30 21 360 ≤ 11566247019596 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_106 c22250R_29_6 (by norm_num)

theorem c22250R_29_4 : rowsJ2 29 30 20 360 ≤ 12662566369590 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_105 c22250R_29_5 (by norm_num)

theorem c22250R_29_3 : rowsJ2 29 30 19 360 ≤ 13615215717887 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_104 c22250R_29_4 (by norm_num)

theorem c22250R_29_2 : rowsJ2 29 30 17 360 ≤ 14993199077879 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_103 c22250R_29_3 (by norm_num)

theorem c22250R_29_1 : rowsJ2 29 30 14 360 ≤ 15784121105613 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_102 c22250R_29_2 (by norm_num)

theorem c22250R_29_0 : rowsJ2 29 30 0 360 ≤ 16478458875141 :=
  rowsJ2_le_of_split 29 30 (by norm_num) (by norm_num) rows22250R_101 c22250R_29_1 (by norm_num)

theorem hr22250R_29 : rows2 29 30 ≤ 16478458875141 := rows2_le_of_rowsJ2 29 30 c22250R_29_0

theorem c22250R_30_13 : rowsJ2 30 31 29 360 ≤ 2124212480626 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_128 rows22250R_129 (by norm_num)

theorem c22250R_30_12 : rowsJ2 30 31 28 360 ≤ 3284970486878 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_127 c22250R_30_13 (by norm_num)

theorem c22250R_30_11 : rowsJ2 30 31 27 360 ≤ 4501382978546 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_126 c22250R_30_12 (by norm_num)

theorem c22250R_30_10 : rowsJ2 30 31 26 360 ≤ 5768603729791 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_125 c22250R_30_11 (by norm_num)

theorem c22250R_30_9 : rowsJ2 30 31 25 360 ≤ 7061843232635 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_124 c22250R_30_10 (by norm_num)

theorem c22250R_30_8 : rowsJ2 30 31 24 360 ≤ 8360824879861 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_123 c22250R_30_9 (by norm_num)

theorem c22250R_30_7 : rowsJ2 30 31 23 360 ≤ 9644595243651 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_122 c22250R_30_8 (by norm_num)

theorem c22250R_30_6 : rowsJ2 30 31 22 360 ≤ 10904724060919 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_121 c22250R_30_7 (by norm_num)

theorem c22250R_30_5 : rowsJ2 30 31 21 360 ≤ 12102809049434 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_120 c22250R_30_6 (by norm_num)

theorem c22250R_30_4 : rowsJ2 30 31 20 360 ≤ 13199843650700 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_119 c22250R_30_5 (by norm_num)

theorem c22250R_30_3 : rowsJ2 30 31 19 360 ≤ 14160316484510 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_118 c22250R_30_4 (by norm_num)

theorem c22250R_30_2 : rowsJ2 30 31 17 360 ≤ 15594900586357 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_117 c22250R_30_3 (by norm_num)

theorem c22250R_30_1 : rowsJ2 30 31 14 360 ≤ 16469282865474 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_116 c22250R_30_2 (by norm_num)

theorem c22250R_30_0 : rowsJ2 30 31 0 360 ≤ 17071275897449 :=
  rowsJ2_le_of_split 30 31 (by norm_num) (by norm_num) rows22250R_115 c22250R_30_1 (by norm_num)

theorem hr22250R_30 : rows2 30 31 ≤ 17071275897449 := rows2_le_of_rowsJ2 30 31 c22250R_30_0

theorem c22250R_31_14 : rowsJ2 31 32 30 360 ≤ 1838416373031 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_144 rows22250R_145 (by norm_num)

theorem c22250R_31_13 : rowsJ2 31 32 29 360 ≤ 2861086991923 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_143 c22250R_31_14 (by norm_num)

theorem c22250R_31_12 : rowsJ2 31 32 28 360 ≤ 3947758930840 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_142 c22250R_31_13 (by norm_num)

theorem c22250R_31_11 : rowsJ2 31 32 27 360 ≤ 5094684296028 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_141 c22250R_31_12 (by norm_num)

theorem c22250R_31_10 : rowsJ2 31 32 26 360 ≤ 6292270596922 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_140 c22250R_31_11 (by norm_num)

theorem c22250R_31_9 : rowsJ2 31 32 25 360 ≤ 7530250393063 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_139 c22250R_31_10 (by norm_num)

theorem c22250R_31_8 : rowsJ2 31 32 24 360 ≤ 8778735935774 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_138 c22250R_31_9 (by norm_num)

theorem c22250R_31_7 : rowsJ2 31 32 23 360 ≤ 10020326479670 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_137 c22250R_31_8 (by norm_num)

theorem c22250R_31_6 : rowsJ2 31 32 22 360 ≤ 11236963593070 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_136 c22250R_31_7 (by norm_num)

theorem c22250R_31_5 : rowsJ2 31 32 21 360 ≤ 12413344200379 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_135 c22250R_31_6 (by norm_num)

theorem c22250R_31_4 : rowsJ2 31 32 20 360 ≤ 13503885303660 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_134 c22250R_31_5 (by norm_num)

theorem c22250R_31_3 : rowsJ2 31 32 19 360 ≤ 14471878292281 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_133 c22250R_31_4 (by norm_num)

theorem c22250R_31_2 : rowsJ2 31 32 17 360 ≤ 15949195741330 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_132 c22250R_31_3 (by norm_num)

theorem c22250R_31_1 : rowsJ2 31 32 14 360 ≤ 16913412491930 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_131 c22250R_31_2 (by norm_num)

theorem c22250R_31_0 : rowsJ2 31 32 0 360 ≤ 17443456792739 :=
  rowsJ2_le_of_split 31 32 (by norm_num) (by norm_num) rows22250R_130 c22250R_31_1 (by norm_num)

theorem hr22250R_31 : rows2 31 32 ≤ 17443456792739 := rows2_le_of_rowsJ2 31 32 c22250R_31_0

theorem c22250R_32_15 : rowsJ2 32 33 31 360 ≤ 1592813778175 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_161 rows22250R_162 (by norm_num)

theorem c22250R_32_14 : rowsJ2 32 33 30 360 ≤ 2472284769323 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_160 c22250R_32_15 (by norm_num)

theorem c22250R_32_13 : rowsJ2 32 33 29 360 ≤ 3419848577896 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_159 c22250R_32_14 (by norm_num)

theorem c22250R_32_12 : rowsJ2 32 33 28 360 ≤ 4435528667625 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_158 c22250R_32_13 (by norm_num)

theorem c22250R_32_11 : rowsJ2 32 33 27 360 ≤ 5511318237303 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_157 c22250R_32_12 (by norm_num)

theorem c22250R_32_10 : rowsJ2 32 33 26 360 ≤ 6642403780107 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_156 c22250R_32_11 (by norm_num)

theorem c22250R_32_9 : rowsJ2 32 33 25 360 ≤ 7818626759312 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_155 c22250R_32_10 (by norm_num)

theorem c22250R_32_8 : rowsJ2 32 33 24 360 ≤ 9019865887167 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_154 c22250R_32_9 (by norm_num)

theorem c22250R_32_7 : rowsJ2 32 33 23 360 ≤ 10215898937643 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_153 c22250R_32_8 (by norm_num)

theorem c22250R_32_6 : rowsJ2 32 33 22 360 ≤ 11395413318737 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_152 c22250R_32_7 (by norm_num)

theorem c22250R_32_5 : rowsJ2 32 33 21 360 ≤ 12540027942397 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_151 c22250R_32_6 (by norm_num)

theorem c22250R_32_4 : rowsJ2 32 33 20 360 ≤ 13620874111368 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_150 c22250R_32_5 (by norm_num)

theorem c22250R_32_3 : rowsJ2 32 33 19 360 ≤ 14591595890069 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_149 c22250R_32_4 (by norm_num)

theorem c22250R_32_2 : rowsJ2 32 33 17 360 ≤ 16105587021803 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_148 c22250R_32_3 (by norm_num)

theorem c22250R_32_1 : rowsJ2 32 33 14 360 ≤ 17154354814151 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_147 c22250R_32_2 (by norm_num)

theorem c22250R_32_0 : rowsJ2 32 33 0 360 ≤ 17629807234289 :=
  rowsJ2_le_of_split 32 33 (by norm_num) (by norm_num) rows22250R_146 c22250R_32_1 (by norm_num)

theorem hr22250R_32 : rows2 32 33 ≤ 17629807234289 := rows2_le_of_rowsJ2 32 33 c22250R_32_0

theorem c22250R_33_15 : rowsJ2 33 34 32 360 ≤ 1416863854946 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_178 rows22250R_179 (by norm_num)

theorem c22250R_33_14 : rowsJ2 33 34 31 360 ≤ 2172560625029 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_177 c22250R_33_15 (by norm_num)

theorem c22250R_33_13 : rowsJ2 33 34 30 360 ≤ 2982288066977 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_176 c22250R_33_14 (by norm_num)

theorem c22250R_33_12 : rowsJ2 33 34 29 360 ≤ 3857216913602 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_175 c22250R_33_13 (by norm_num)

theorem c22250R_33_11 : rowsJ2 33 34 28 360 ≤ 4800682413153 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_174 c22250R_33_12 (by norm_num)

theorem c22250R_33_10 : rowsJ2 33 34 27 360 ≤ 5808387737024 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_173 c22250R_33_11 (by norm_num)

theorem c22250R_33_9 : rowsJ2 33 34 26 360 ≤ 6871275160267 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_172 c22250R_33_10 (by norm_num)

theorem c22250R_33_8 : rowsJ2 33 34 25 360 ≤ 7983980456895 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_171 c22250R_33_9 (by norm_num)

theorem c22250R_33_7 : rowsJ2 33 34 24 360 ≤ 9131384643167 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_170 c22250R_33_8 (by norm_num)

theorem c22250R_33_6 : rowsJ2 33 34 23 360 ≤ 10288239857357 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_169 c22250R_33_7 (by norm_num)

theorem c22250R_33_5 : rowsJ2 33 34 22 360 ≤ 11427169367024 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_168 c22250R_33_6 (by norm_num)

theorem c22250R_33_4 : rowsJ2 33 34 21 360 ≤ 12539758409624 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_167 c22250R_33_5 (by norm_num)

theorem c22250R_33_3 : rowsJ2 33 34 19 360 ≤ 14573875040478 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_166 c22250R_33_4 (by norm_num)

theorem c22250R_33_2 : rowsJ2 33 34 17 360 ≤ 16113927394701 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_165 c22250R_33_3 (by norm_num)

theorem c22250R_33_1 : rowsJ2 33 34 14 360 ≤ 17251064445709 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_164 c22250R_33_2 (by norm_num)

theorem c22250R_33_0 : rowsJ2 33 34 0 360 ≤ 17686474550829 :=
  rowsJ2_le_of_split 33 34 (by norm_num) (by norm_num) rows22250R_163 c22250R_33_1 (by norm_num)

theorem hr22250R_33 : rows2 33 34 ≤ 17686474550829 := rows2_le_of_rowsJ2 33 34 c22250R_33_0

theorem c22250R_34_16 : rowsJ2 34 35 33 360 ≤ 1332515035473 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_196 rows22250R_197 (by norm_num)

theorem c22250R_34_15 : rowsJ2 34 35 32 360 ≤ 1998392620786 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_195 c22250R_34_16 (by norm_num)

theorem c22250R_34_14 : rowsJ2 34 35 31 360 ≤ 2693256511194 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_194 c22250R_34_15 (by norm_num)

theorem c22250R_34_13 : rowsJ2 34 35 30 360 ≤ 3438277617254 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_193 c22250R_34_14 (by norm_num)

theorem c22250R_34_12 : rowsJ2 34 35 29 360 ≤ 4242534625107 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_192 c22250R_34_13 (by norm_num)

theorem c22250R_34_11 : rowsJ2 34 35 28 360 ≤ 5116220695292 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_191 c22250R_34_12 (by norm_num)

theorem c22250R_34_10 : rowsJ2 34 35 27 360 ≤ 6054057100413 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_190 c22250R_34_11 (by norm_num)

theorem c22250R_34_9 : rowsJ2 34 35 26 360 ≤ 7051757138090 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_189 c22250R_34_10 (by norm_num)

theorem c22250R_34_8 : rowsJ2 34 35 25 360 ≤ 8099198970456 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_188 c22250R_34_9 (by norm_num)

theorem c22250R_34_7 : rowsJ2 34 35 24 360 ≤ 9190927565470 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_187 c22250R_34_8 (by norm_num)

theorem c22250R_34_6 : rowsJ2 34 35 23 360 ≤ 10301923752036 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_186 c22250R_34_7 (by norm_num)

theorem c22250R_34_5 : rowsJ2 34 35 22 360 ≤ 11406584304525 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_185 c22250R_34_6 (by norm_num)

theorem c22250R_34_4 : rowsJ2 34 35 21 360 ≤ 12483601405838 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_184 c22250R_34_5 (by norm_num)

theorem c22250R_34_3 : rowsJ2 34 35 19 360 ≤ 14489504346259 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_183 c22250R_34_4 (by norm_num)

theorem c22250R_34_2 : rowsJ2 34 35 17 360 ≤ 16054926813861 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_182 c22250R_34_3 (by norm_num)

theorem c22250R_34_1 : rowsJ2 34 35 14 360 ≤ 17269836614335 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_181 c22250R_34_2 (by norm_num)

theorem c22250R_34_0 : rowsJ2 34 35 0 360 ≤ 17682899184827 :=
  rowsJ2_le_of_split 34 35 (by norm_num) (by norm_num) rows22250R_180 c22250R_34_1 (by norm_num)

theorem hr22250R_34 : rows2 34 35 ≤ 17682899184827 := rows2_le_of_rowsJ2 34 35 c22250R_34_0

theorem c22250R_35_16 : rowsJ2 35 36 34 360 ≤ 1359395195190 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_214 rows22250R_215 (by norm_num)

theorem c22250R_35_15 : rowsJ2 35 36 33 360 ≤ 1979455686718 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_213 c22250R_35_16 (by norm_num)

theorem c22250R_35_14 : rowsJ2 35 36 32 360 ≤ 2597254693407 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_212 c22250R_35_15 (by norm_num)

theorem c22250R_35_13 : rowsJ2 35 36 31 360 ≤ 3239119530257 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_211 c22250R_35_14 (by norm_num)

theorem c22250R_35_12 : rowsJ2 35 36 30 360 ≤ 3921841452854 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_210 c22250R_35_13 (by norm_num)

theorem c22250R_35_11 : rowsJ2 35 36 29 360 ≤ 4661007860556 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_209 c22250R_35_12 (by norm_num)

theorem c22250R_35_10 : rowsJ2 35 36 28 360 ≤ 5463030858466 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_208 c22250R_35_11 (by norm_num)

theorem c22250R_35_9 : rowsJ2 35 36 27 360 ≤ 6333924722044 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_207 c22250R_35_10 (by norm_num)

theorem c22250R_35_8 : rowsJ2 35 36 26 360 ≤ 7264610543670 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_206 c22250R_35_9 (by norm_num)

theorem c22250R_35_7 : rowsJ2 35 36 25 360 ≤ 8249760481087 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_205 c22250R_35_8 (by norm_num)

theorem c22250R_35_6 : rowsJ2 35 36 24 360 ≤ 9279160851115 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_204 c22250R_35_7 (by norm_num)

theorem c22250R_35_5 : rowsJ2 35 36 23 360 ≤ 10342377679684 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_203 c22250R_35_6 (by norm_num)

theorem c22250R_35_4 : rowsJ2 35 36 21 360 ≤ 12456920003978 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_202 c22250R_35_5 (by norm_num)

theorem c22250R_35_3 : rowsJ2 35 36 19 360 ≤ 14423882071061 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_201 c22250R_35_4 (by norm_num)

theorem c22250R_35_2 : rowsJ2 35 36 17 360 ≤ 16009355984895 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_200 c22250R_35_3 (by norm_num)

theorem c22250R_35_1 : rowsJ2 35 36 14 360 ≤ 17299159835025 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_199 c22250R_35_2 (by norm_num)

theorem c22250R_35_0 : rowsJ2 35 36 0 360 ≤ 17704804616420 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22250R_198 c22250R_35_1 (by norm_num)

theorem hr22250R_35 : rows2 35 36 ≤ 17704804616420 := rows2_le_of_rowsJ2 35 36 c22250R_35_0

theorem c22250R_36_16 : rowsJ2 36 37 35 360 ≤ 1396111260621 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_232 rows22250R_233 (by norm_num)

theorem c22250R_36_15 : rowsJ2 36 37 34 360 ≤ 2019638630685 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_231 c22250R_36_16 (by norm_num)

theorem c22250R_36_14 : rowsJ2 36 37 33 360 ≤ 2606783637103 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_230 c22250R_36_15 (by norm_num)

theorem c22250R_36_13 : rowsJ2 36 37 32 360 ≤ 3183667378508 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_229 c22250R_36_14 (by norm_num)

theorem c22250R_36_12 : rowsJ2 36 37 31 360 ≤ 3775456338100 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_228 c22250R_36_13 (by norm_num)

theorem c22250R_36_11 : rowsJ2 36 37 30 360 ≤ 4403713485654 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_227 c22250R_36_12 (by norm_num)

theorem c22250R_36_10 : rowsJ2 36 37 29 360 ≤ 5079035072684 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_226 c22250R_36_11 (by norm_num)

theorem c22250R_36_9 : rowsJ2 36 37 28 360 ≤ 5814970373974 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_225 c22250R_36_10 (by norm_num)

theorem c22250R_36_8 : rowsJ2 36 37 27 360 ≤ 6617002056424 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_224 c22250R_36_9 (by norm_num)

theorem c22250R_36_7 : rowsJ2 36 37 26 360 ≤ 7483566943740 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_223 c22250R_36_8 (by norm_num)

theorem c22250R_36_6 : rowsJ2 36 37 25 360 ≤ 8404555967179 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_222 c22250R_36_7 (by norm_num)

theorem c22250R_36_5 : rowsJ2 36 37 23 360 ≤ 10383264563595 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_221 c22250R_36_6 (by norm_num)

theorem c22250R_36_4 : rowsJ2 36 37 21 360 ≤ 12425045252367 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_220 c22250R_36_5 (by norm_num)

theorem c22250R_36_3 : rowsJ2 36 37 19 360 ≤ 14348908461408 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_219 c22250R_36_4 (by norm_num)

theorem c22250R_36_2 : rowsJ2 36 37 17 360 ≤ 15948829627516 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_218 c22250R_36_3 (by norm_num)

theorem c22250R_36_1 : rowsJ2 36 37 14 360 ≤ 17307844635738 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_217 c22250R_36_2 (by norm_num)

theorem c22250R_36_0 : rowsJ2 36 37 0 360 ≤ 17718195650649 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22250R_216 c22250R_36_1 (by norm_num)

theorem hr22250R_36 : rows2 36 37 ≤ 17718195650649 := rows2_le_of_rowsJ2 36 37 c22250R_36_0

theorem c22250R_37_17 : rowsJ2 37 38 36 360 ≤ 1334455575596 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_251 rows22250R_252 (by norm_num)

theorem c22250R_37_16 : rowsJ2 37 38 35 360 ≤ 1989376281644 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_250 c22250R_37_17 (by norm_num)

theorem c22250R_37_15 : rowsJ2 37 38 34 360 ≤ 2594303897420 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_249 c22250R_37_16 (by norm_num)

theorem c22250R_37_14 : rowsJ2 37 38 33 360 ≤ 3150066113974 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_248 c22250R_37_15 (by norm_num)

theorem c22250R_37_13 : rowsJ2 37 38 32 360 ≤ 3691511837993 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_247 c22250R_37_14 (by norm_num)

theorem c22250R_37_12 : rowsJ2 37 38 31 360 ≤ 4240395856040 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_246 c22250R_37_13 (by norm_num)

theorem c22250R_37_11 : rowsJ2 37 38 30 360 ≤ 4816436397803 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_245 c22250R_37_12 (by norm_num)

theorem c22250R_37_10 : rowsJ2 37 38 29 360 ≤ 5435751703687 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_244 c22250R_37_11 (by norm_num)

theorem c22250R_37_9 : rowsJ2 37 38 28 360 ≤ 6107390615624 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_243 c22250R_37_10 (by norm_num)

theorem c22250R_37_8 : rowsJ2 37 38 27 360 ≤ 6843365589413 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_242 c22250R_37_9 (by norm_num)

theorem c22250R_37_7 : rowsJ2 37 38 26 360 ≤ 7643853900317 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_241 c22250R_37_8 (by norm_num)

theorem c22250R_37_6 : rowsJ2 37 38 25 360 ≤ 8503543528988 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_240 c22250R_37_7 (by norm_num)

theorem c22250R_37_5 : rowsJ2 37 38 23 360 ≤ 10364455844812 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_239 c22250R_37_6 (by norm_num)

theorem c22250R_37_4 : rowsJ2 37 38 21 360 ≤ 12327813992457 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_238 c22250R_37_5 (by norm_num)

theorem c22250R_37_3 : rowsJ2 37 38 19 360 ≤ 14204407048705 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_237 c22250R_37_4 (by norm_num)

theorem c22250R_37_2 : rowsJ2 37 38 17 360 ≤ 15810643436207 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_236 c22250R_37_3 (by norm_num)

theorem c22250R_37_1 : rowsJ2 37 38 14 360 ≤ 17233397101672 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_235 c22250R_37_2 (by norm_num)

theorem c22250R_37_0 : rowsJ2 37 38 0 360 ≤ 17663408022977 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22250R_234 c22250R_37_1 (by norm_num)

theorem hr22250R_37 : rows2 37 38 ≤ 17663408022977 := rows2_le_of_rowsJ2 37 38 c22250R_37_0

theorem c22250R_38_18 : rowsJ2 38 39 37 360 ≤ 1197894933817 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_271 rows22250R_272 (by norm_num)

theorem c22250R_38_17 : rowsJ2 38 39 36 360 ≤ 1826036933889 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_270 c22250R_38_18 (by norm_num)

theorem c22250R_38_16 : rowsJ2 38 39 35 360 ≤ 2445508293273 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_269 c22250R_38_17 (by norm_num)

theorem c22250R_38_15 : rowsJ2 38 39 34 360 ≤ 3032455037763 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_268 c22250R_38_16 (by norm_num)

theorem c22250R_38_14 : rowsJ2 38 39 33 360 ≤ 3563803004895 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_267 c22250R_38_15 (by norm_num)

theorem c22250R_38_13 : rowsJ2 38 39 32 360 ≤ 4071353748641 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_266 c22250R_38_14 (by norm_num)

theorem c22250R_38_12 : rowsJ2 38 39 31 360 ≤ 4580118505550 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_265 c22250R_38_13 (by norm_num)

theorem c22250R_38_11 : rowsJ2 38 39 30 360 ≤ 5111125574452 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_264 c22250R_38_12 (by norm_num)

theorem c22250R_38_10 : rowsJ2 38 39 29 360 ≤ 5676683145616 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_263 c22250R_38_11 (by norm_num)

theorem c22250R_38_9 : rowsJ2 38 39 28 360 ≤ 6291859312236 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_262 c22250R_38_10 (by norm_num)

theorem c22250R_38_8 : rowsJ2 38 39 27 360 ≤ 6962473000199 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_261 c22250R_38_9 (by norm_num)

theorem c22250R_38_7 : rowsJ2 38 39 26 360 ≤ 7699664455274 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_260 c22250R_38_8 (by norm_num)

theorem c22250R_38_6 : rowsJ2 38 39 25 360 ≤ 8496062729351 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_259 c22250R_38_7 (by norm_num)

theorem c22250R_38_5 : rowsJ2 38 39 23 360 ≤ 10240056116350 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_258 c22250R_38_6 (by norm_num)

theorem c22250R_38_4 : rowsJ2 38 39 21 360 ≤ 12116041492755 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_257 c22250R_38_5 (by norm_num)

theorem c22250R_38_3 : rowsJ2 38 39 19 360 ≤ 13942682359567 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_256 c22250R_38_4 (by norm_num)

theorem c22250R_38_2 : rowsJ2 38 39 17 360 ≤ 15546601197339 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_255 c22250R_38_3 (by norm_num)

theorem c22250R_38_1 : rowsJ2 38 39 14 360 ≤ 17029087351540 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_254 c22250R_38_2 (by norm_num)

theorem c22250R_38_0 : rowsJ2 38 39 0 360 ≤ 17490896085078 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22250R_253 c22250R_38_1 (by norm_num)

theorem hr22250R_38 : rows2 38 39 ≤ 17490896085078 := rows2_le_of_rowsJ2 38 39 c22250R_38_0

theorem c22250R_39_18 : rowsJ2 39 40 38 360 ≤ 1025304546535 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_291 rows22250R_292 (by norm_num)

theorem c22250R_39_17 : rowsJ2 39 40 37 360 ≤ 1590265903793 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_290 c22250R_39_18 (by norm_num)

theorem c22250R_39_16 : rowsJ2 39 40 36 360 ≤ 2171849068178 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_289 c22250R_39_17 (by norm_num)

theorem c22250R_39_15 : rowsJ2 39 40 35 360 ≤ 2756707845011 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_288 c22250R_39_16 (by norm_num)

theorem c22250R_39_14 : rowsJ2 39 40 34 360 ≤ 3317437005650 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_287 c22250R_39_15 (by norm_num)

theorem c22250R_39_13 : rowsJ2 39 40 33 360 ≤ 3827178630265 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_286 c22250R_39_14 (by norm_num)

theorem c22250R_39_12 : rowsJ2 39 40 32 360 ≤ 4304250734327 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_285 c22250R_39_13 (by norm_num)

theorem c22250R_39_11 : rowsJ2 39 40 31 360 ≤ 4776437018937 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_284 c22250R_39_12 (by norm_num)

theorem c22250R_39_10 : rowsJ2 39 40 30 360 ≤ 5265205417196 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_283 c22250R_39_11 (by norm_num)

theorem c22250R_39_9 : rowsJ2 39 40 29 360 ≤ 5785315206847 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_282 c22250R_39_10 (by norm_num)

theorem c22250R_39_8 : rowsJ2 39 40 28 360 ≤ 6345116888185 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_281 c22250R_39_9 (by norm_num)

theorem c22250R_39_7 : rowsJ2 39 40 27 360 ≤ 6958762637907 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_280 c22250R_39_8 (by norm_num)

theorem c22250R_39_6 : rowsJ2 39 40 25 360 ≤ 8366433844598 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_279 c22250R_39_7 (by norm_num)

theorem c22250R_39_5 : rowsJ2 39 40 23 360 ≤ 9994281547817 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_278 c22250R_39_6 (by norm_num)

theorem c22250R_39_4 : rowsJ2 39 40 21 360 ≤ 11773889162110 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_277 c22250R_39_5 (by norm_num)

theorem c22250R_39_3 : rowsJ2 39 40 19 360 ≤ 13547876490193 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_276 c22250R_39_4 (by norm_num)

theorem c22250R_39_2 : rowsJ2 39 40 17 360 ≤ 15138279990867 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_275 c22250R_39_3 (by norm_num)

theorem c22250R_39_1 : rowsJ2 39 40 14 360 ≤ 16678539227703 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_274 c22250R_39_2 (by norm_num)

theorem c22250R_39_0 : rowsJ2 39 40 0 360 ≤ 17181041215611 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22250R_273 c22250R_39_1 (by norm_num)

theorem hr22250R_39 : rows2 39 40 ≤ 17181041215611 := rows2_le_of_rowsJ2 39 40 c22250R_39_0

theorem c22250R_40_19 : rowsJ2 40 41 39 360 ≤ 786326992742 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_312 rows22250R_313 (by norm_num)

theorem c22250R_40_18 : rowsJ2 40 41 38 360 ≤ 1241987073778 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_311 c22250R_40_19 (by norm_num)

theorem c22250R_40_17 : rowsJ2 40 41 37 360 ≤ 1723508793468 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_310 c22250R_40_18 (by norm_num)

theorem c22250R_40_16 : rowsJ2 40 41 36 360 ≤ 2234934629370 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_309 c22250R_40_17 (by norm_num)

theorem c22250R_40_15 : rowsJ2 40 41 35 360 ≤ 2749290758456 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_308 c22250R_40_16 (by norm_num)

theorem c22250R_40_14 : rowsJ2 40 41 34 360 ≤ 3261282115062 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_307 c22250R_40_15 (by norm_num)

theorem c22250R_40_13 : rowsJ2 40 41 33 360 ≤ 3731567604297 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_306 c22250R_40_14 (by norm_num)

theorem c22250R_40_12 : rowsJ2 40 41 32 360 ≤ 4169658995551 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_305 c22250R_40_13 (by norm_num)

theorem c22250R_40_11 : rowsJ2 40 41 31 360 ≤ 4598719469481 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_304 c22250R_40_12 (by norm_num)

theorem c22250R_40_10 : rowsJ2 40 41 30 360 ≤ 5044277287623 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_303 c22250R_40_11 (by norm_num)

theorem c22250R_40_9 : rowsJ2 40 41 29 360 ≤ 5516643142627 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_302 c22250R_40_10 (by norm_num)

theorem c22250R_40_8 : rowsJ2 40 41 28 360 ≤ 6028341856942 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_301 c22250R_40_9 (by norm_num)

theorem c22250R_40_7 : rowsJ2 40 41 27 360 ≤ 6585572798554 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_300 c22250R_40_8 (by norm_num)

theorem c22250R_40_6 : rowsJ2 40 41 25 360 ≤ 7873600099104 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_299 c22250R_40_7 (by norm_num)

theorem c22250R_40_5 : rowsJ2 40 41 23 360 ≤ 9385967744558 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_298 c22250R_40_6 (by norm_num)

theorem c22250R_40_4 : rowsJ2 40 41 21 360 ≤ 11065003763145 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_297 c22250R_40_5 (by norm_num)

theorem c22250R_40_3 : rowsJ2 40 41 19 360 ≤ 12780343544875 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_296 c22250R_40_4 (by norm_num)

theorem c22250R_40_2 : rowsJ2 40 41 17 360 ≤ 14347564640985 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_295 c22250R_40_3 (by norm_num)

theorem c22250R_40_1 : rowsJ2 40 41 14 360 ≤ 15946693281374 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_294 c22250R_40_2 (by norm_num)

theorem c22250R_40_0 : rowsJ2 40 41 0 360 ≤ 16493993305386 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22250R_293 c22250R_40_1 (by norm_num)

theorem hr22250R_40 : rows2 40 41 ≤ 16493993305386 := rows2_le_of_rowsJ2 40 41 c22250R_40_0

theorem c22250R_41_20 : rowsJ2 41 42 40 360 ≤ 562956895541 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_334 rows22250R_335 (by norm_num)

theorem c22250R_41_19 : rowsJ2 41 42 39 360 ≤ 903521695562 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_333 c22250R_41_20 (by norm_num)

theorem c22250R_41_18 : rowsJ2 41 42 38 360 ≤ 1279412943557 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_332 c22250R_41_19 (by norm_num)

theorem c22250R_41_17 : rowsJ2 41 42 37 360 ≤ 1690816969910 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_331 c22250R_41_18 (by norm_num)

theorem c22250R_41_16 : rowsJ2 41 42 36 360 ≤ 2124301163942 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_330 c22250R_41_17 (by norm_num)

theorem c22250R_41_15 : rowsJ2 41 42 35 360 ≤ 2577723159803 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_329 c22250R_41_16 (by norm_num)

theorem c22250R_41_14 : rowsJ2 41 42 34 360 ≤ 3028475994745 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_328 c22250R_41_15 (by norm_num)

theorem c22250R_41_13 : rowsJ2 41 42 33 360 ≤ 3463999707496 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_327 c22250R_41_14 (by norm_num)

theorem c22250R_41_12 : rowsJ2 41 42 32 360 ≤ 3863450206371 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_326 c22250R_41_13 (by norm_num)

theorem c22250R_41_11 : rowsJ2 41 42 31 360 ≤ 4254075945341 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_325 c22250R_41_12 (by norm_num)

theorem c22250R_41_10 : rowsJ2 41 42 30 360 ≤ 4656806870589 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_324 c22250R_41_11 (by norm_num)

theorem c22250R_41_9 : rowsJ2 41 42 29 360 ≤ 5086144672862 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_323 c22250R_41_10 (by norm_num)

theorem c22250R_41_8 : rowsJ2 41 42 28 360 ≤ 5550184609840 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_322 c22250R_41_9 (by norm_num)

theorem c22250R_41_7 : rowsJ2 41 42 27 360 ≤ 6059331498577 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_321 c22250R_41_8 (by norm_num)

theorem c22250R_41_6 : rowsJ2 41 42 25 360 ≤ 7233871579526 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_320 c22250R_41_7 (by norm_num)

theorem c22250R_41_5 : rowsJ2 41 42 23 360 ≤ 8631320463215 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_319 c22250R_41_6 (by norm_num)

theorem c22250R_41_4 : rowsJ2 41 42 21 360 ≤ 10205509303907 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_318 c22250R_41_5 (by norm_num)

theorem c22250R_41_3 : rowsJ2 41 42 19 360 ≤ 11856174132957 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_317 c22250R_41_4 (by norm_num)

theorem c22250R_41_2 : rowsJ2 41 42 17 360 ≤ 13390556038382 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_316 c22250R_41_3 (by norm_num)

theorem c22250R_41_1 : rowsJ2 41 42 14 360 ≤ 15042285955434 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_315 c22250R_41_2 (by norm_num)

theorem c22250R_41_0 : rowsJ2 41 42 0 360 ≤ 15646259310391 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22250R_314 c22250R_41_1 (by norm_num)

theorem hr22250R_41 : rows2 41 42 ≤ 15646259310391 := rows2_le_of_rowsJ2 41 42 c22250R_41_0

theorem c22250R_42_21 : rowsJ2 42 43 41 360 ≤ 370945041666 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_357 rows22250R_358 (by norm_num)

theorem c22250R_42_20 : rowsJ2 42 43 40 360 ≤ 606619284689 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_356 c22250R_42_21 (by norm_num)

theorem c22250R_42_19 : rowsJ2 42 43 39 360 ≤ 874585515442 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_355 c22250R_42_20 (by norm_num)

theorem c22250R_42_18 : rowsJ2 42 43 38 360 ≤ 1182150026673 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_354 c22250R_42_19 (by norm_num)

theorem c22250R_42_17 : rowsJ2 42 43 37 360 ≤ 1519191798729 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_353 c22250R_42_18 (by norm_num)

theorem c22250R_42_16 : rowsJ2 42 43 36 360 ≤ 1887987443631 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_352 c22250R_42_17 (by norm_num)

theorem c22250R_42_15 : rowsJ2 42 43 35 360 ≤ 2272573490351 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_351 c22250R_42_16 (by norm_num)

theorem c22250R_42_14 : rowsJ2 42 43 34 360 ≤ 2671549477768 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_350 c22250R_42_15 (by norm_num)

theorem c22250R_42_13 : rowsJ2 42 43 33 360 ≤ 3059636821670 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_349 c22250R_42_14 (by norm_num)

theorem c22250R_42_12 : rowsJ2 42 43 32 360 ≤ 3425118142978 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_348 c22250R_42_13 (by norm_num)

theorem c22250R_42_11 : rowsJ2 42 43 31 360 ≤ 3777627019577 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_347 c22250R_42_12 (by norm_num)

theorem c22250R_42_10 : rowsJ2 42 43 30 360 ≤ 4142210885118 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_346 c22250R_42_11 (by norm_num)

theorem c22250R_42_9 : rowsJ2 42 43 29 360 ≤ 4528889034557 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_345 c22250R_42_10 (by norm_num)

theorem c22250R_42_8 : rowsJ2 42 43 28 360 ≤ 4949979434736 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_344 c22250R_42_9 (by norm_num)

theorem c22250R_42_7 : rowsJ2 42 43 27 360 ≤ 5411473284097 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_343 c22250R_42_8 (by norm_num)

theorem c22250R_42_6 : rowsJ2 42 43 26 360 ≤ 5921717751400 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_342 c22250R_42_7 (by norm_num)

theorem c22250R_42_5 : rowsJ2 42 43 24 360 ≤ 7099105127823 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_341 c22250R_42_6 (by norm_num)

theorem c22250R_42_4 : rowsJ2 42 43 22 360 ≤ 8483549686904 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_340 c22250R_42_5 (by norm_num)

theorem c22250R_42_3 : rowsJ2 42 43 20 360 ≤ 10022595693924 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_339 c22250R_42_4 (by norm_num)

theorem c22250R_42_2 : rowsJ2 42 43 17 360 ≤ 12312415498446 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_338 c22250R_42_3 (by norm_num)

theorem c22250R_42_1 : rowsJ2 42 43 14 360 ≤ 14004845773539 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_337 c22250R_42_2 (by norm_num)

theorem c22250R_42_0 : rowsJ2 42 43 0 360 ≤ 14671611708108 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22250R_336 c22250R_42_1 (by norm_num)

theorem hr22250R_42 : rows2 42 43 ≤ 14671611708108 := rows2_le_of_rowsJ2 42 43 c22250R_42_0

theorem c22250R_43_22 : rowsJ2 43 44 42 360 ≤ 218460848765 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_381 rows22250R_382 (by norm_num)

theorem c22250R_43_21 : rowsJ2 43 44 41 360 ≤ 363772870643 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_380 c22250R_43_22 (by norm_num)

theorem c22250R_43_20 : rowsJ2 43 44 40 360 ≤ 535594313750 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_379 c22250R_43_21 (by norm_num)

theorem c22250R_43_19 : rowsJ2 43 44 39 360 ≤ 740683092232 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_378 c22250R_43_20 (by norm_num)

theorem c22250R_43_18 : rowsJ2 43 44 38 360 ≤ 978275110413 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_377 c22250R_43_19 (by norm_num)

theorem c22250R_43_17 : rowsJ2 43 44 37 360 ≤ 1249665881230 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_376 c22250R_43_18 (by norm_num)

theorem c22250R_43_16 : rowsJ2 43 44 36 360 ≤ 1549455256128 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_375 c22250R_43_17 (by norm_num)

theorem c22250R_43_15 : rowsJ2 43 44 35 360 ≤ 1874763374553 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_374 c22250R_43_16 (by norm_num)

theorem c22250R_43_14 : rowsJ2 43 44 34 360 ≤ 2213945657505 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_373 c22250R_43_15 (by norm_num)

theorem c22250R_43_13 : rowsJ2 43 44 33 360 ≤ 2559387370080 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_372 c22250R_43_14 (by norm_num)

theorem c22250R_43_12 : rowsJ2 43 44 32 360 ≤ 2891163426066 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_371 c22250R_43_13 (by norm_num)

theorem c22250R_43_11 : rowsJ2 43 44 31 360 ≤ 3210212407910 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_370 c22250R_43_12 (by norm_num)

theorem c22250R_43_10 : rowsJ2 43 44 30 360 ≤ 3536951021015 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_369 c22250R_43_11 (by norm_num)

theorem c22250R_43_9 : rowsJ2 43 44 29 360 ≤ 3885642352775 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_368 c22250R_43_10 (by norm_num)

theorem c22250R_43_8 : rowsJ2 43 44 28 360 ≤ 4264138718506 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_367 c22250R_43_9 (by norm_num)

theorem c22250R_43_7 : rowsJ2 43 44 27 360 ≤ 4682685182550 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_366 c22250R_43_8 (by norm_num)

theorem c22250R_43_6 : rowsJ2 43 44 26 360 ≤ 5145228772045 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_365 c22250R_43_7 (by norm_num)

theorem c22250R_43_5 : rowsJ2 43 44 24 360 ≤ 6217859416721 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_364 c22250R_43_6 (by norm_num)

theorem c22250R_43_4 : rowsJ2 43 44 22 360 ≤ 7496297440100 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_363 c22250R_43_5 (by norm_num)

theorem c22250R_43_3 : rowsJ2 43 44 20 360 ≤ 8936675878020 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_362 c22250R_43_4 (by norm_num)

theorem c22250R_43_2 : rowsJ2 43 44 17 360 ≤ 11153461835349 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_361 c22250R_43_3 (by norm_num)

theorem c22250R_43_1 : rowsJ2 43 44 14 360 ≤ 12869455701067 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_360 c22250R_43_2 (by norm_num)

theorem c22250R_43_0 : rowsJ2 43 44 0 360 ≤ 13611078150848 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22250R_359 c22250R_43_1 (by norm_num)

theorem hr22250R_43 : rows2 43 44 ≤ 13611078150848 := rows2_le_of_rowsJ2 43 44 c22250R_43_0

theorem c22250R_44_22 : rowsJ2 44 45 43 360 ≤ 132870793376 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_405 rows22250R_406 (by norm_num)

theorem c22250R_44_21 : rowsJ2 44 45 42 360 ≤ 225399157988 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_404 c22250R_44_22 (by norm_num)

theorem c22250R_44_20 : rowsJ2 44 45 41 360 ≤ 335196176692 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_403 c22250R_44_21 (by norm_num)

theorem c22250R_44_19 : rowsJ2 44 45 40 360 ≤ 471332763404 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_402 c22250R_44_20 (by norm_num)

theorem c22250R_44_18 : rowsJ2 44 45 39 360 ≤ 631707120086 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_401 c22250R_44_19 (by norm_num)

theorem c22250R_44_17 : rowsJ2 44 45 38 360 ≤ 825406265075 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_400 c22250R_44_18 (by norm_num)

theorem c22250R_44_16 : rowsJ2 44 45 37 360 ≤ 1046018829204 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_399 c22250R_44_17 (by norm_num)

theorem c22250R_44_15 : rowsJ2 44 45 36 360 ≤ 1298912956102 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_398 c22250R_44_16 (by norm_num)

theorem c22250R_44_14 : rowsJ2 44 45 35 360 ≤ 1572854669097 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_397 c22250R_44_15 (by norm_num)

theorem c22250R_44_13 : rowsJ2 44 45 34 360 ≤ 1869524551402 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_396 c22250R_44_14 (by norm_num)

theorem c22250R_44_12 : rowsJ2 44 45 33 360 ≤ 2170211327104 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_395 c22250R_44_13 (by norm_num)

theorem c22250R_44_11 : rowsJ2 44 45 32 360 ≤ 2472931588395 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_394 c22250R_44_12 (by norm_num)

theorem c22250R_44_10 : rowsJ2 44 45 31 360 ≤ 2758765182293 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_393 c22250R_44_11 (by norm_num)

theorem c22250R_44_9 : rowsJ2 44 45 30 360 ≤ 3052307622632 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_392 c22250R_44_10 (by norm_num)

theorem c22250R_44_8 : rowsJ2 44 45 29 360 ≤ 3363300776661 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_391 c22250R_44_9 (by norm_num)

theorem c22250R_44_7 : rowsJ2 44 45 28 360 ≤ 3703872457368 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_390 c22250R_44_8 (by norm_num)

theorem c22250R_44_6 : rowsJ2 44 45 27 360 ≤ 4079815857755 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_389 c22250R_44_7 (by norm_num)

theorem c22250R_44_5 : rowsJ2 44 45 25 360 ≤ 4963093360298 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_388 c22250R_44_6 (by norm_num)

theorem c22250R_44_4 : rowsJ2 44 45 23 360 ≤ 6038771474031 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_387 c22250R_44_5 (by norm_num)

theorem c22250R_44_3 : rowsJ2 44 45 20 360 ≤ 7993828359313 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_386 c22250R_44_4 (by norm_num)

theorem c22250R_44_2 : rowsJ2 44 45 17 360 ≤ 10124040791096 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_385 c22250R_44_3 (by norm_num)

theorem c22250R_44_1 : rowsJ2 44 45 14 360 ≤ 11850117793223 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_384 c22250R_44_2 (by norm_num)

theorem c22250R_44_0 : rowsJ2 44 45 0 360 ≤ 12674429975853 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22250R_383 c22250R_44_1 (by norm_num)

theorem hr22250R_44 : rows2 44 45 ≤ 12674429975853 := rows2_le_of_rowsJ2 44 45 c22250R_44_0

theorem c22250R_45_23 : rowsJ2 45 46 44 360 ≤ 70691694566 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_430 rows22250R_431 (by norm_num)

theorem c22250R_45_22 : rowsJ2 45 46 43 360 ≤ 123622398773 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_429 c22250R_45_23 (by norm_num)

theorem c22250R_45_21 : rowsJ2 45 46 42 360 ≤ 189854698340 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_428 c22250R_45_22 (by norm_num)

theorem c22250R_45_20 : rowsJ2 45 46 41 360 ≤ 273268950581 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_427 c22250R_45_21 (by norm_num)

theorem c22250R_45_19 : rowsJ2 45 46 40 360 ≤ 373987704716 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_426 c22250R_45_20 (by norm_num)

theorem c22250R_45_18 : rowsJ2 45 46 39 360 ≤ 498797172095 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_425 c22250R_45_19 (by norm_num)

theorem c22250R_45_17 : rowsJ2 45 46 38 360 ≤ 647894447730 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_424 c22250R_45_18 (by norm_num)

theorem c22250R_45_16 : rowsJ2 45 46 37 360 ≤ 825833682975 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_423 c22250R_45_17 (by norm_num)

theorem c22250R_45_15 : rowsJ2 45 46 36 360 ≤ 1029172001982 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_422 c22250R_45_16 (by norm_num)

theorem c22250R_45_14 : rowsJ2 45 46 35 360 ≤ 1259503709065 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_421 c22250R_45_15 (by norm_num)

theorem c22250R_45_13 : rowsJ2 45 46 34 360 ≤ 1508104895619 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_420 c22250R_45_14 (by norm_num)

theorem c22250R_45_12 : rowsJ2 45 46 33 360 ≤ 1772548643077 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_419 c22250R_45_13 (by norm_num)

theorem c22250R_45_11 : rowsJ2 45 46 32 360 ≤ 2036814234763 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_418 c22250R_45_12 (by norm_num)

theorem c22250R_45_10 : rowsJ2 45 46 31 360 ≤ 2294070666633 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_417 c22250R_45_11 (by norm_num)

theorem c22250R_45_9 : rowsJ2 45 46 30 360 ≤ 2554647483526 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_416 c22250R_45_10 (by norm_num)

theorem c22250R_45_8 : rowsJ2 45 46 29 360 ≤ 2832587639536 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_415 c22250R_45_9 (by norm_num)

theorem c22250R_45_7 : rowsJ2 45 46 28 360 ≤ 3135512289322 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_414 c22250R_45_8 (by norm_num)

theorem c22250R_45_6 : rowsJ2 45 46 27 360 ≤ 3473521368058 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_413 c22250R_45_7 (by norm_num)

theorem c22250R_45_5 : rowsJ2 45 46 25 360 ≤ 4271077923971 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_412 c22250R_45_6 (by norm_num)

theorem c22250R_45_4 : rowsJ2 45 46 23 360 ≤ 5250592669362 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_411 c22250R_45_5 (by norm_num)

theorem c22250R_45_3 : rowsJ2 45 46 20 360 ≤ 7059531766696 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_410 c22250R_45_4 (by norm_num)

theorem c22250R_45_2 : rowsJ2 45 46 17 360 ≤ 9094443040260 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_409 c22250R_45_3 (by norm_num)

theorem c22250R_45_1 : rowsJ2 45 46 14 360 ≤ 10812197999833 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_408 c22250R_45_2 (by norm_num)

theorem c22250R_45_0 : rowsJ2 45 46 0 360 ≤ 11725418206881 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22250R_407 c22250R_45_1 (by norm_num)

theorem hr22250R_45 : rows2 45 46 ≤ 11725418206881 := rows2_le_of_rowsJ2 45 46 c22250R_45_0

theorem c22250R_46_24 : rowsJ2 46 47 45 360 ≤ 31916440626 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_456 rows22250R_457 (by norm_num)

theorem c22250R_46_23 : rowsJ2 46 47 44 360 ≤ 57801401016 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_455 c22250R_46_24 (by norm_num)

theorem c22250R_46_22 : rowsJ2 46 47 43 360 ≤ 90724091161 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_454 c22250R_46_23 (by norm_num)

theorem c22250R_46_21 : rowsJ2 46 47 42 360 ≤ 136886461883 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_453 c22250R_46_22 (by norm_num)

theorem c22250R_46_20 : rowsJ2 46 47 41 360 ≤ 194098332229 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_452 c22250R_46_21 (by norm_num)

theorem c22250R_46_19 : rowsJ2 46 47 40 360 ≤ 268526512881 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_451 c22250R_46_20 (by norm_num)

theorem c22250R_46_18 : rowsJ2 46 47 39 360 ≤ 358027408822 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_450 c22250R_46_19 (by norm_num)

theorem c22250R_46_17 : rowsJ2 46 47 38 360 ≤ 471666980108 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_449 c22250R_46_18 (by norm_num)

theorem c22250R_46_16 : rowsJ2 46 47 37 360 ≤ 606202061016 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_448 c22250R_46_17 (by norm_num)

theorem c22250R_46_15 : rowsJ2 46 47 36 360 ≤ 768074835642 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_447 c22250R_46_16 (by norm_num)

theorem c22250R_46_14 : rowsJ2 46 47 35 360 ≤ 952093169506 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_446 c22250R_46_15 (by norm_num)

theorem c22250R_46_13 : rowsJ2 46 47 34 360 ≤ 1160350461797 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_445 c22250R_46_14 (by norm_num)

theorem c22250R_46_12 : rowsJ2 46 47 33 360 ≤ 1382919660907 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_444 c22250R_46_13 (by norm_num)

theorem c22250R_46_11 : rowsJ2 46 47 32 360 ≤ 1617186504465 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_443 c22250R_46_12 (by norm_num)

theorem c22250R_46_10 : rowsJ2 46 47 31 360 ≤ 1846047155380 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_442 c22250R_46_11 (by norm_num)

theorem c22250R_46_9 : rowsJ2 46 47 30 360 ≤ 2078291771450 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_441 c22250R_46_10 (by norm_num)

theorem c22250R_46_8 : rowsJ2 46 47 29 360 ≤ 2323398183265 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_440 c22250R_46_9 (by norm_num)

theorem c22250R_46_7 : rowsJ2 46 47 28 360 ≤ 2593320393273 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_439 c22250R_46_8 (by norm_num)

theorem c22250R_46_6 : rowsJ2 46 47 27 360 ≤ 2893663375436 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_438 c22250R_46_7 (by norm_num)

theorem c22250R_46_5 : rowsJ2 46 47 26 360 ≤ 3232556877413 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_437 c22250R_46_6 (by norm_num)

theorem c22250R_46_4 : rowsJ2 46 47 24 360 ≤ 4032414908267 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_436 c22250R_46_5 (by norm_num)

theorem c22250R_46_3 : rowsJ2 46 47 21 360 ≤ 5573210974859 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_435 c22250R_46_4 (by norm_num)

theorem c22250R_46_2 : rowsJ2 46 47 18 360 ≤ 7447642365529 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_434 c22250R_46_3 (by norm_num)

theorem c22250R_46_1 : rowsJ2 46 47 14 360 ≤ 9798169005850 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_433 c22250R_46_2 (by norm_num)

theorem c22250R_46_0 : rowsJ2 46 47 0 360 ≤ 10799808968052 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22250R_432 c22250R_46_1 (by norm_num)

theorem hr22250R_46 : rows2 46 47 ≤ 10799808968052 := rows2_le_of_rowsJ2 46 47 c22250R_46_0

theorem c22250R_47_25 : rowsJ2 47 48 46 360 ≤ 141023692522 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_483 rows22250R_484 (by norm_num)

theorem c22250R_47_24 : rowsJ2 47 48 45 360 ≤ 150702053857 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_482 c22250R_47_25 (by norm_num)

theorem c22250R_47_23 : rowsJ2 47 48 44 360 ≤ 162847528010 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_481 c22250R_47_24 (by norm_num)

theorem c22250R_47_22 : rowsJ2 47 48 43 360 ≤ 182009744050 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_480 c22250R_47_23 (by norm_num)

theorem c22250R_47_21 : rowsJ2 47 48 42 360 ≤ 208230972526 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_479 c22250R_47_22 (by norm_num)

theorem c22250R_47_20 : rowsJ2 47 48 41 360 ≤ 245462219760 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_478 c22250R_47_21 (by norm_num)

theorem c22250R_47_19 : rowsJ2 47 48 40 360 ≤ 293772360865 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_477 c22250R_47_20 (by norm_num)

theorem c22250R_47_18 : rowsJ2 47 48 39 360 ≤ 357088879011 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_476 c22250R_47_19 (by norm_num)

theorem c22250R_47_17 : rowsJ2 47 48 38 360 ≤ 435516721112 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_475 c22250R_47_18 (by norm_num)

theorem c22250R_47_16 : rowsJ2 47 48 37 360 ≤ 534724299641 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_474 c22250R_47_17 (by norm_num)

theorem c22250R_47_15 : rowsJ2 47 48 36 360 ≤ 654379234200 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_473 c22250R_47_16 (by norm_num)

theorem c22250R_47_14 : rowsJ2 47 48 35 360 ≤ 798147222165 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_472 c22250R_47_15 (by norm_num)

theorem c22250R_47_13 : rowsJ2 47 48 34 360 ≤ 963315072166 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_471 c22250R_47_14 (by norm_num)

theorem c22250R_47_12 : rowsJ2 47 48 33 360 ≤ 1148803252271 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_470 c22250R_47_13 (by norm_num)

theorem c22250R_47_11 : rowsJ2 47 48 32 360 ≤ 1347365623174 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_469 c22250R_47_12 (by norm_num)

theorem c22250R_47_10 : rowsJ2 47 48 31 360 ≤ 1552464893050 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_468 c22250R_47_11 (by norm_num)

theorem c22250R_47_9 : rowsJ2 47 48 30 360 ≤ 1756546604654 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_467 c22250R_47_10 (by norm_num)

theorem c22250R_47_8 : rowsJ2 47 48 29 360 ≤ 1973451653049 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_466 c22250R_47_9 (by norm_num)

theorem c22250R_47_7 : rowsJ2 47 48 28 360 ≤ 2210581378488 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_465 c22250R_47_8 (by norm_num)

theorem c22250R_47_6 : rowsJ2 47 48 27 360 ≤ 2477904991558 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_464 c22250R_47_7 (by norm_num)

theorem c22250R_47_5 : rowsJ2 47 48 26 360 ≤ 2779066656700 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_463 c22250R_47_6 (by norm_num)

theorem c22250R_47_4 : rowsJ2 47 48 24 360 ≤ 3498044064699 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_462 c22250R_47_5 (by norm_num)

theorem c22250R_47_3 : rowsJ2 47 48 21 360 ≤ 4904701554841 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_461 c22250R_47_4 (by norm_num)

theorem c22250R_47_2 : rowsJ2 47 48 18 360 ≤ 6649712115932 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_460 c22250R_47_3 (by norm_num)

theorem c22250R_47_1 : rowsJ2 47 48 14 360 ≤ 8943046025046 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_459 c22250R_47_2 (by norm_num)

theorem c22250R_47_0 : rowsJ2 47 48 0 360 ≤ 10032620942668 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22250R_458 c22250R_47_1 (by norm_num)

theorem hr22250R_47 : rows2 47 48 ≤ 10032620942668 := rows2_le_of_rowsJ2 47 48 c22250R_47_0

theorem c22250R_48_26 : rowsJ2 48 49 47 360 ≤ 699987406600 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_511 rows22250R_512 (by norm_num)

theorem c22250R_48_25 : rowsJ2 48 49 46 360 ≤ 705138089469 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_510 c22250R_48_26 (by norm_num)

theorem c22250R_48_24 : rowsJ2 48 49 45 360 ≤ 710787167568 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_509 c22250R_48_25 (by norm_num)

theorem c22250R_48_23 : rowsJ2 48 49 44 360 ≤ 718888465894 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_508 c22250R_48_24 (by norm_num)

theorem c22250R_48_22 : rowsJ2 48 49 43 360 ≤ 728938555562 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_507 c22250R_48_23 (by norm_num)

theorem c22250R_48_21 : rowsJ2 48 49 42 360 ≤ 746016030498 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_506 c22250R_48_22 (by norm_num)

theorem c22250R_48_20 : rowsJ2 48 49 41 360 ≤ 769086782702 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_505 c22250R_48_21 (by norm_num)

theorem c22250R_48_19 : rowsJ2 48 49 40 360 ≤ 803186150524 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_504 c22250R_48_20 (by norm_num)

theorem c22250R_48_18 : rowsJ2 48 49 39 360 ≤ 847312451580 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_503 c22250R_48_19 (by norm_num)

theorem c22250R_48_17 : rowsJ2 48 49 38 360 ≤ 906473842846 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_502 c22250R_48_18 (by norm_num)

theorem c22250R_48_16 : rowsJ2 48 49 37 360 ≤ 979193326852 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_501 c22250R_48_17 (by norm_num)

theorem c22250R_48_15 : rowsJ2 48 49 36 360 ≤ 1072737147381 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_500 c22250R_48_16 (by norm_num)

theorem c22250R_48_14 : rowsJ2 48 49 35 360 ≤ 1184187350941 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_499 c22250R_48_15 (by norm_num)

theorem c22250R_48_13 : rowsJ2 48 49 34 360 ≤ 1319302329988 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_498 c22250R_48_14 (by norm_num)

theorem c22250R_48_12 : rowsJ2 48 49 33 360 ≤ 1471412768307 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_497 c22250R_48_13 (by norm_num)

theorem c22250R_48_11 : rowsJ2 48 49 32 360 ≤ 1642575169467 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_496 c22250R_48_12 (by norm_num)

theorem c22250R_48_10 : rowsJ2 48 49 31 360 ≤ 1819914998729 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_495 c22250R_48_11 (by norm_num)

theorem c22250R_48_9 : rowsJ2 48 49 30 360 ≤ 2000466261562 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_494 c22250R_48_10 (by norm_num)

theorem c22250R_48_8 : rowsJ2 48 49 29 360 ≤ 2189329609789 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_493 c22250R_48_9 (by norm_num)

theorem c22250R_48_7 : rowsJ2 48 49 28 360 ≤ 2398301324838 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_492 c22250R_48_8 (by norm_num)

theorem c22250R_48_6 : rowsJ2 48 49 27 360 ≤ 2632807641345 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_491 c22250R_48_7 (by norm_num)

theorem c22250R_48_5 : rowsJ2 48 49 26 360 ≤ 2900888542878 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_490 c22250R_48_6 (by norm_num)

theorem c22250R_48_4 : rowsJ2 48 49 24 360 ≤ 3543915447726 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_489 c22250R_48_5 (by norm_num)

theorem c22250R_48_3 : rowsJ2 48 49 21 360 ≤ 4818991397905 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_488 c22250R_48_4 (by norm_num)

theorem c22250R_48_2 : rowsJ2 48 49 18 360 ≤ 6443318404382 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_487 c22250R_48_3 (by norm_num)

theorem c22250R_48_1 : rowsJ2 48 49 14 360 ≤ 8666122913293 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_486 c22250R_48_2 (by norm_num)

theorem c22250R_48_0 : rowsJ2 48 49 0 360 ≤ 9835329262374 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22250R_485 c22250R_48_1 (by norm_num)

theorem hr22250R_48 : rows2 48 49 ≤ 9835329262374 := rows2_le_of_rowsJ2 48 49 c22250R_48_0

theorem c22250R_49_27 : rowsJ2 49 50 48 360 ≤ 1607053608427 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_540 rows22250R_541 (by norm_num)

theorem c22250R_49_26 : rowsJ2 49 50 47 360 ≤ 1734627087096 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_539 c22250R_49_27 (by norm_num)

theorem c22250R_49_25 : rowsJ2 49 50 46 360 ≤ 1737711282275 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_538 c22250R_49_26 (by norm_num)

theorem c22250R_49_24 : rowsJ2 49 50 45 360 ≤ 1741294618789 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_537 c22250R_49_25 (by norm_num)

theorem c22250R_49_23 : rowsJ2 49 50 44 360 ≤ 1745381901468 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_536 c22250R_49_24 (by norm_num)

theorem c22250R_49_22 : rowsJ2 49 50 43 360 ≤ 1751408143139 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_535 c22250R_49_23 (by norm_num)

theorem c22250R_49_21 : rowsJ2 49 50 42 360 ≤ 1759390677254 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_534 c22250R_49_22 (by norm_num)

theorem c22250R_49_20 : rowsJ2 49 50 41 360 ≤ 1773345351729 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_533 c22250R_49_21 (by norm_num)

theorem c22250R_49_19 : rowsJ2 49 50 40 360 ≤ 1793307351893 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_532 c22250R_49_20 (by norm_num)

theorem c22250R_49_18 : rowsJ2 49 50 39 360 ≤ 1823256155182 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_531 c22250R_49_19 (by norm_num)

theorem c22250R_49_17 : rowsJ2 49 50 38 360 ≤ 1863254562261 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_530 c22250R_49_18 (by norm_num)

theorem c22250R_49_16 : rowsJ2 49 50 37 360 ≤ 1916749805298 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_529 c22250R_49_17 (by norm_num)

theorem c22250R_49_15 : rowsJ2 49 50 36 360 ≤ 1983837063670 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_528 c22250R_49_16 (by norm_num)

theorem c22250R_49_14 : rowsJ2 49 50 35 360 ≤ 2069728985511 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_527 c22250R_49_15 (by norm_num)

theorem c22250R_49_13 : rowsJ2 49 50 34 360 ≤ 2173070385951 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_526 c22250R_49_14 (by norm_num)

theorem c22250R_49_12 : rowsJ2 49 50 33 360 ≤ 2297123622739 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_525 c22250R_49_13 (by norm_num)

theorem c22250R_49_11 : rowsJ2 49 50 32 360 ≤ 2436904344928 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_524 c22250R_49_12 (by norm_num)

theorem c22250R_49_10 : rowsJ2 49 50 31 360 ≤ 2591162284519 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_523 c22250R_49_11 (by norm_num)

theorem c22250R_49_9 : rowsJ2 49 50 30 360 ≤ 2748300676133 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_522 c22250R_49_10 (by norm_num)

theorem c22250R_49_8 : rowsJ2 49 50 29 360 ≤ 2913756396968 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_521 c22250R_49_9 (by norm_num)

theorem c22250R_49_7 : rowsJ2 49 50 28 360 ≤ 3094721964747 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_520 c22250R_49_8 (by norm_num)

theorem c22250R_49_6 : rowsJ2 49 50 27 360 ≤ 3301050144128 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_519 c22250R_49_7 (by norm_num)

theorem c22250R_49_5 : rowsJ2 49 50 26 360 ≤ 3536245372712 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_518 c22250R_49_6 (by norm_num)

theorem c22250R_49_4 : rowsJ2 49 50 24 360 ≤ 4108222304301 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_517 c22250R_49_5 (by norm_num)

theorem c22250R_49_3 : rowsJ2 49 50 21 360 ≤ 5258584957589 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_516 c22250R_49_4 (by norm_num)

theorem c22250R_49_2 : rowsJ2 49 50 18 360 ≤ 6762864887122 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_515 c22250R_49_3 (by norm_num)

theorem c22250R_49_1 : rowsJ2 49 50 14 360 ≤ 8904738368268 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_514 c22250R_49_2 (by norm_num)

theorem c22250R_49_0 : rowsJ2 49 50 0 360 ≤ 10150240426495 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22250R_513 c22250R_49_1 (by norm_num)

theorem hr22250R_49 : rows2 49 50 ≤ 10150240426495 := rows2_le_of_rowsJ2 49 50 c22250R_49_0

theorem c22250R_50_28 : rowsJ2 50 51 49 360 ≤ 2587082090361 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_570 rows22250R_571 (by norm_num)

theorem c22250R_50_27 : rowsJ2 50 51 48 360 ≤ 3142722350974 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_569 c22250R_50_28 (by norm_num)

theorem c22250R_50_26 : rowsJ2 50 51 47 360 ≤ 3267496340488 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_568 c22250R_50_27 (by norm_num)

theorem c22250R_50_25 : rowsJ2 50 51 46 360 ≤ 3269033401110 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_567 c22250R_50_26 (by norm_num)

theorem c22250R_50_24 : rowsJ2 50 51 45 360 ≤ 3270565625724 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_566 c22250R_50_25 (by norm_num)

theorem c22250R_50_23 : rowsJ2 50 51 44 360 ≤ 3272602316361 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_565 c22250R_50_24 (by norm_num)

theorem c22250R_50_22 : rowsJ2 50 51 43 360 ≤ 3274633609014 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_564 c22250R_50_23 (by norm_num)

theorem c22250R_50_21 : rowsJ2 50 51 42 360 ≤ 3278611034861 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_563 c22250R_50_22 (by norm_num)

theorem c22250R_50_20 : rowsJ2 50 51 41 360 ≤ 3283495914659 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_562 c22250R_50_21 (by norm_num)

theorem c22250R_50_19 : rowsJ2 50 51 40 360 ≤ 3294366406714 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_561 c22250R_50_20 (by norm_num)

theorem c22250R_50_18 : rowsJ2 50 51 39 360 ≤ 3310207326718 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_560 c22250R_50_19 (by norm_num)

theorem c22250R_50_17 : rowsJ2 50 51 38 360 ≤ 3336056835880 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_559 c22250R_50_18 (by norm_num)

theorem c22250R_50_16 : rowsJ2 50 51 37 360 ≤ 3370426153733 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_558 c22250R_50_17 (by norm_num)

theorem c22250R_50_15 : rowsJ2 50 51 36 360 ≤ 3418324912845 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_557 c22250R_50_16 (by norm_num)

theorem c22250R_50_14 : rowsJ2 50 51 35 360 ≤ 3478302318877 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_556 c22250R_50_15 (by norm_num)

theorem c22250R_50_13 : rowsJ2 50 51 34 360 ≤ 3556629942629 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_555 c22250R_50_14 (by norm_num)

theorem c22250R_50_12 : rowsJ2 50 51 33 360 ≤ 3650880137240 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_554 c22250R_50_13 (by norm_num)

theorem c22250R_50_11 : rowsJ2 50 51 32 360 ≤ 3764587360735 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_553 c22250R_50_12 (by norm_num)

theorem c22250R_50_10 : rowsJ2 50 51 31 360 ≤ 3891732121201 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_552 c22250R_50_11 (by norm_num)

theorem c22250R_50_9 : rowsJ2 50 51 30 360 ≤ 4030103578555 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_551 c22250R_50_10 (by norm_num)

theorem c22250R_50_8 : rowsJ2 50 51 29 360 ≤ 4172261102872 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_550 c22250R_50_9 (by norm_num)

theorem c22250R_50_7 : rowsJ2 50 51 28 360 ≤ 4329859194195 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_549 c22250R_50_8 (by norm_num)

theorem c22250R_50_6 : rowsJ2 50 51 27 360 ≤ 4508154591099 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_548 c22250R_50_7 (by norm_num)

theorem c22250R_50_5 : rowsJ2 50 51 26 360 ≤ 4715110105170 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_547 c22250R_50_6 (by norm_num)

theorem c22250R_50_4 : rowsJ2 50 51 24 360 ≤ 5220889568502 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_546 c22250R_50_5 (by norm_num)

theorem c22250R_50_3 : rowsJ2 50 51 22 360 ≤ 5868469699412 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_545 c22250R_50_4 (by norm_num)

theorem c22250R_50_2 : rowsJ2 50 51 18 360 ≤ 7640935859836 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_544 c22250R_50_3 (by norm_num)

theorem c22250R_50_1 : rowsJ2 50 51 14 360 ≤ 9693073389773 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_543 c22250R_50_2 (by norm_num)

theorem c22250R_50_0 : rowsJ2 50 51 0 360 ≤ 11006593409176 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22250R_542 c22250R_50_1 (by norm_num)

theorem hr22250R_50 : rows2 50 51 ≤ 11006593409176 := rows2_le_of_rowsJ2 50 51 c22250R_50_0

theorem c22250R_51_29 : rowsJ2 51 52 50 360 ≤ 3751655769445 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_601 rows22250R_602 (by norm_num)

theorem c22250R_51_28 : rowsJ2 51 52 49 360 ≤ 4774162969083 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_600 c22250R_51_29 (by norm_num)

theorem c22250R_51_27 : rowsJ2 51 52 48 360 ≤ 5323269019703 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_599 c22250R_51_28 (by norm_num)

theorem c22250R_51_26 : rowsJ2 51 52 47 360 ≤ 5445787043406 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_598 c22250R_51_27 (by norm_num)

theorem c22250R_51_25 : rowsJ2 51 52 46 360 ≤ 5445787043406 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_597 c22250R_51_26 (by norm_num)

theorem c22250R_51_24 : rowsJ2 51 52 45 360 ≤ 5445787043406 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_596 c22250R_51_25 (by norm_num)

theorem c22250R_51_23 : rowsJ2 51 52 44 360 ≤ 5445787043406 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_595 c22250R_51_24 (by norm_num)

theorem c22250R_51_22 : rowsJ2 51 52 43 360 ≤ 5445787043406 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_594 c22250R_51_23 (by norm_num)

theorem c22250R_51_21 : rowsJ2 51 52 42 360 ≤ 5445787043406 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_593 c22250R_51_22 (by norm_num)

theorem c22250R_51_20 : rowsJ2 51 52 41 360 ≤ 5446694479778 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_592 c22250R_51_21 (by norm_num)

theorem c22250R_51_19 : rowsJ2 51 52 40 360 ≤ 5448517296166 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_591 c22250R_51_20 (by norm_num)

theorem c22250R_51_18 : rowsJ2 51 52 39 360 ≤ 5455298649576 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_590 c22250R_51_19 (by norm_num)

theorem c22250R_51_17 : rowsJ2 51 52 38 360 ≤ 5467065198282 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_589 c22250R_51_18 (by norm_num)

theorem c22250R_51_16 : rowsJ2 51 52 37 360 ≤ 5487325011583 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_588 c22250R_51_17 (by norm_num)

theorem c22250R_51_15 : rowsJ2 51 52 36 360 ≤ 5516128591480 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_587 c22250R_51_16 (by norm_num)

theorem c22250R_51_14 : rowsJ2 51 52 35 360 ≤ 5556962208579 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_586 c22250R_51_15 (by norm_num)

theorem c22250R_51_13 : rowsJ2 51 52 34 360 ≤ 5609909224422 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_585 c22250R_51_14 (by norm_num)

theorem c22250R_51_12 : rowsJ2 51 52 33 360 ≤ 5679693066744 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_584 c22250R_51_13 (by norm_num)

theorem c22250R_51_11 : rowsJ2 51 52 32 360 ≤ 5765556123063 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_583 c22250R_51_12 (by norm_num)

theorem c22250R_51_10 : rowsJ2 51 52 31 360 ≤ 5868611644806 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_582 c22250R_51_11 (by norm_num)

theorem c22250R_51_9 : rowsJ2 51 52 30 360 ≤ 5984135585125 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_581 c22250R_51_10 (by norm_num)

theorem c22250R_51_8 : rowsJ2 51 52 29 360 ≤ 6107644962584 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_580 c22250R_51_9 (by norm_num)

theorem c22250R_51_7 : rowsJ2 51 52 28 360 ≤ 6241978548855 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_579 c22250R_51_8 (by norm_num)

theorem c22250R_51_6 : rowsJ2 51 52 27 360 ≤ 6396886908993 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_578 c22250R_51_7 (by norm_num)

theorem c22250R_51_5 : rowsJ2 51 52 26 360 ≤ 6575742365507 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_577 c22250R_51_6 (by norm_num)

theorem c22250R_51_4 : rowsJ2 51 52 24 360 ≤ 7020160198531 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_576 c22250R_51_5 (by norm_num)

theorem c22250R_51_3 : rowsJ2 51 52 22 360 ≤ 7596304037485 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_575 c22250R_51_4 (by norm_num)

theorem c22250R_51_2 : rowsJ2 51 52 19 360 ≤ 8753304769412 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_574 c22250R_51_3 (by norm_num)

theorem c22250R_51_1 : rowsJ2 51 52 15 360 ≤ 10694330844820 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_573 c22250R_51_2 (by norm_num)

theorem c22250R_51_0 : rowsJ2 51 52 0 360 ≤ 12545746353560 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22250R_572 c22250R_51_1 (by norm_num)

theorem hr22250R_51 : rows2 51 52 ≤ 12545746353560 := rows2_le_of_rowsJ2 51 52 c22250R_51_0

theorem c22250R_52_30 : rowsJ2 52 53 51 360 ≤ 5333661593623 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_633 rows22250R_634 (by norm_num)

theorem c22250R_52_29 : rowsJ2 52 53 50 360 ≤ 6856435575157 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_632 c22250R_52_30 (by norm_num)

theorem c22250R_52_28 : rowsJ2 52 53 49 360 ≤ 7868898375751 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_631 c22250R_52_29 (by norm_num)

theorem c22250R_52_27 : rowsJ2 52 53 48 360 ≤ 8412610390718 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_630 c22250R_52_28 (by norm_num)

theorem c22250R_52_26 : rowsJ2 52 53 47 360 ≤ 8533924882631 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_629 c22250R_52_27 (by norm_num)

theorem c22250R_52_25 : rowsJ2 52 53 46 360 ≤ 8533924882631 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_628 c22250R_52_26 (by norm_num)

theorem c22250R_52_24 : rowsJ2 52 53 45 360 ≤ 8533924882631 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_627 c22250R_52_25 (by norm_num)

theorem c22250R_52_23 : rowsJ2 52 53 44 360 ≤ 8533924882631 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_626 c22250R_52_24 (by norm_num)

theorem c22250R_52_22 : rowsJ2 52 53 43 360 ≤ 8533924882631 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_625 c22250R_52_23 (by norm_num)

theorem c22250R_52_21 : rowsJ2 52 53 42 360 ≤ 8533924882631 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_624 c22250R_52_22 (by norm_num)

theorem c22250R_52_20 : rowsJ2 52 53 41 360 ≤ 8533924882631 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_623 c22250R_52_21 (by norm_num)

theorem c22250R_52_19 : rowsJ2 52 53 40 360 ≤ 8534833410937 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_622 c22250R_52_20 (by norm_num)

theorem c22250R_52_18 : rowsJ2 52 53 39 360 ≤ 8536658647099 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_621 c22250R_52_19 (by norm_num)

theorem c22250R_52_17 : rowsJ2 52 53 38 360 ≤ 8543449863963 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_620 c22250R_52_18 (by norm_num)

theorem c22250R_52_16 : rowsJ2 52 53 37 360 ≤ 8554738929113 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_619 c22250R_52_17 (by norm_num)

theorem c22250R_52_15 : rowsJ2 52 53 36 360 ≤ 8574538337225 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_618 c22250R_52_16 (by norm_num)

theorem c22250R_52_14 : rowsJ2 52 53 35 360 ≤ 8602406535006 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_617 c22250R_52_15 (by norm_num)

theorem c22250R_52_13 : rowsJ2 52 53 34 360 ≤ 8642334072373 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_616 c22250R_52_14 (by norm_num)

theorem c22250R_52_12 : rowsJ2 52 53 33 360 ≤ 8693449454313 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_615 c22250R_52_13 (by norm_num)

theorem c22250R_52_11 : rowsJ2 52 53 32 360 ≤ 8761449593391 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_614 c22250R_52_12 (by norm_num)

theorem c22250R_52_10 : rowsJ2 52 53 31 360 ≤ 8842813642231 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_613 c22250R_52_11 (by norm_num)

theorem c22250R_52_9 : rowsJ2 52 53 30 360 ≤ 8940069985153 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_612 c22250R_52_10 (by norm_num)

theorem c22250R_52_8 : rowsJ2 52 53 29 360 ≤ 9044999467128 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_611 c22250R_52_9 (by norm_num)

theorem c22250R_52_7 : rowsJ2 52 53 28 360 ≤ 9160725556826 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_610 c22250R_52_8 (by norm_num)

theorem c22250R_52_6 : rowsJ2 52 53 27 360 ≤ 9292344574149 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_609 c22250R_52_7 (by norm_num)

theorem c22250R_52_5 : rowsJ2 52 53 26 360 ≤ 9447754826485 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_608 c22250R_52_6 (by norm_num)

theorem c22250R_52_4 : rowsJ2 52 53 25 360 ≤ 9627220998334 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_607 c22250R_52_5 (by norm_num)

theorem c22250R_52_3 : rowsJ2 52 53 23 360 ≤ 10073279687407 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_606 c22250R_52_4 (by norm_num)

theorem c22250R_52_2 : rowsJ2 52 53 19 360 ≤ 11384781974384 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_605 c22250R_52_3 (by norm_num)

theorem c22250R_52_1 : rowsJ2 52 53 15 360 ≤ 13201189017686 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_604 c22250R_52_2 (by norm_num)

theorem c22250R_52_0 : rowsJ2 52 53 0 360 ≤ 15098884253798 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22250R_603 c22250R_52_1 (by norm_num)

theorem hr22250R_52 : rows2 52 53 ≤ 15098884253798 := rows2_le_of_rowsJ2 52 53 c22250R_52_0

theorem c22250R_53_31 : rowsJ2 53 54 52 360 ≤ 7186822236906 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_666 rows22250R_667 (by norm_num)

theorem c22250R_53_30 : rowsJ2 53 54 51 360 ≤ 9357526878222 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_665 c22250R_53_31 (by norm_num)

theorem c22250R_53_29 : rowsJ2 53 54 50 360 ≤ 10865487702190 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_664 c22250R_53_30 (by norm_num)

theorem c22250R_53_28 : rowsJ2 53 54 49 360 ≤ 11868101522455 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_663 c22250R_53_29 (by norm_num)

theorem c22250R_53_27 : rowsJ2 53 54 48 360 ≤ 12406524445379 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_662 c22250R_53_28 (by norm_num)

theorem c22250R_53_26 : rowsJ2 53 54 47 360 ≤ 12526658820804 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_661 c22250R_53_27 (by norm_num)

theorem c22250R_53_25 : rowsJ2 53 54 46 360 ≤ 12526658820804 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_660 c22250R_53_26 (by norm_num)

theorem c22250R_53_24 : rowsJ2 53 54 45 360 ≤ 12526658820804 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_659 c22250R_53_25 (by norm_num)

theorem c22250R_53_23 : rowsJ2 53 54 44 360 ≤ 12526658820804 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_658 c22250R_53_24 (by norm_num)

theorem c22250R_53_22 : rowsJ2 53 54 43 360 ≤ 12526658820804 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_657 c22250R_53_23 (by norm_num)

theorem c22250R_53_21 : rowsJ2 53 54 42 360 ≤ 12526658820804 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_656 c22250R_53_22 (by norm_num)

theorem c22250R_53_20 : rowsJ2 53 54 41 360 ≤ 12526658820804 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_655 c22250R_53_21 (by norm_num)

theorem c22250R_53_19 : rowsJ2 53 54 40 360 ≤ 12526658820804 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_654 c22250R_53_20 (by norm_num)

theorem c22250R_53_18 : rowsJ2 53 54 39 360 ≤ 12527568642970 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_653 c22250R_53_19 (by norm_num)

theorem c22250R_53_17 : rowsJ2 53 54 38 360 ≤ 12529396710336 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_652 c22250R_53_18 (by norm_num)

theorem c22250R_53_16 : rowsJ2 53 54 37 360 ≤ 12535708043225 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_651 c22250R_53_17 (by norm_num)

theorem c22250R_53_15 : rowsJ2 53 54 36 360 ≤ 12546527205456 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_650 c22250R_53_16 (by norm_num)

theorem c22250R_53_14 : rowsJ2 53 54 35 360 ≤ 12565386075195 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_649 c22250R_53_15 (by norm_num)

theorem c22250R_53_13 : rowsJ2 53 54 34 360 ≤ 12592334655965 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_648 c22250R_53_14 (by norm_num)

theorem c22250R_53_12 : rowsJ2 53 54 33 360 ≤ 12630425534984 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_647 c22250R_53_13 (by norm_num)

theorem c22250R_53_11 : rowsJ2 53 54 32 360 ≤ 12679738461837 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_646 c22250R_53_12 (by norm_num)

theorem c22250R_53_10 : rowsJ2 53 54 31 360 ≤ 12744138586167 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_645 c22250R_53_11 (by norm_num)

theorem c22250R_53_9 : rowsJ2 53 54 30 360 ≤ 12820602858462 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_644 c22250R_53_10 (by norm_num)

theorem c22250R_53_8 : rowsJ2 53 54 29 360 ≤ 12909918819791 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_643 c22250R_53_9 (by norm_num)

theorem c22250R_53_7 : rowsJ2 53 54 28 360 ≤ 13007100414812 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_642 c22250R_53_8 (by norm_num)

theorem c22250R_53_6 : rowsJ2 53 54 27 360 ≤ 13120096434458 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_641 c22250R_53_7 (by norm_num)

theorem c22250R_53_5 : rowsJ2 53 54 26 360 ≤ 13252154631404 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_640 c22250R_53_6 (by norm_num)

theorem c22250R_53_4 : rowsJ2 53 54 25 360 ≤ 13408110593005 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_639 c22250R_53_5 (by norm_num)

theorem c22250R_53_3 : rowsJ2 53 54 23 360 ≤ 13797434665751 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_638 c22250R_53_4 (by norm_num)

theorem c22250R_53_2 : rowsJ2 53 54 20 360 ≤ 14617086127674 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_637 c22250R_53_3 (by norm_num)

theorem c22250R_53_1 : rowsJ2 53 54 15 360 ≤ 16653920506210 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_636 c22250R_53_2 (by norm_num)

theorem c22250R_53_0 : rowsJ2 53 54 0 360 ≤ 18585584019712 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22250R_635 c22250R_53_1 (by norm_num)

theorem hr22250R_53 : rows2 53 54 ≤ 18585584019712 := rows2_le_of_rowsJ2 53 54 c22250R_53_0

theorem c22250R_54_32 : rowsJ2 54 55 53 360 ≤ 9049834992953 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_700 rows22250R_701 (by norm_num)

theorem c22250R_54_31 : rowsJ2 54 55 52 360 ≤ 12130935284210 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_699 c22250R_54_32 (by norm_num)

theorem c22250R_54_30 : rowsJ2 54 55 51 360 ≤ 14280727296214 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_698 c22250R_54_31 (by norm_num)

theorem c22250R_54_29 : rowsJ2 54 55 50 360 ≤ 15774160383373 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_697 c22250R_54_30 (by norm_num)

theorem c22250R_54_28 : rowsJ2 54 55 49 360 ≤ 16767114994011 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_696 c22250R_54_29 (by norm_num)

theorem c22250R_54_27 : rowsJ2 54 55 48 360 ≤ 17300350735415 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_695 c22250R_54_28 (by norm_num)

theorem c22250R_54_26 : rowsJ2 54 55 47 360 ≤ 17419327732902 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_694 c22250R_54_27 (by norm_num)

theorem c22250R_54_25 : rowsJ2 54 55 46 360 ≤ 17419327732902 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_693 c22250R_54_26 (by norm_num)

theorem c22250R_54_24 : rowsJ2 54 55 45 360 ≤ 17419327732902 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_692 c22250R_54_25 (by norm_num)

theorem c22250R_54_23 : rowsJ2 54 55 44 360 ≤ 17419327732902 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_691 c22250R_54_24 (by norm_num)

theorem c22250R_54_22 : rowsJ2 54 55 43 360 ≤ 17419327732902 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_690 c22250R_54_23 (by norm_num)

theorem c22250R_54_21 : rowsJ2 54 55 42 360 ≤ 17419327732902 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_689 c22250R_54_22 (by norm_num)

theorem c22250R_54_20 : rowsJ2 54 55 41 360 ≤ 17419327732902 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_688 c22250R_54_21 (by norm_num)

theorem c22250R_54_19 : rowsJ2 54 55 40 360 ≤ 17419327732902 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_687 c22250R_54_20 (by norm_num)

theorem c22250R_54_18 : rowsJ2 54 55 39 360 ≤ 17419327732902 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_686 c22250R_54_19 (by norm_num)

theorem c22250R_54_17 : rowsJ2 54 55 38 360 ≤ 17420239052570 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_685 c22250R_54_18 (by norm_num)

theorem c22250R_54_16 : rowsJ2 54 55 37 360 ≤ 17421583798975 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_684 c22250R_54_17 (by norm_num)

theorem c22250R_54_15 : rowsJ2 54 55 36 360 ≤ 17427421521778 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_683 c22250R_54_16 (by norm_num)

theorem c22250R_54_14 : rowsJ2 54 55 35 360 ≤ 17437293091726 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_682 c22250R_54_15 (by norm_num)

theorem c22250R_54_13 : rowsJ2 54 55 34 360 ≤ 17455224728366 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_681 c22250R_54_14 (by norm_num)

theorem c22250R_54_12 : rowsJ2 54 55 33 360 ≤ 17480328787696 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_680 c22250R_54_13 (by norm_num)

theorem c22250R_54_11 : rowsJ2 54 55 32 360 ≤ 17516608382972 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_679 c22250R_54_12 (by norm_num)

theorem c22250R_54_10 : rowsJ2 54 55 31 360 ≤ 17563208488290 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_678 c22250R_54_11 (by norm_num)

theorem c22250R_54_9 : rowsJ2 54 55 30 360 ≤ 17623610408568 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_677 c22250R_54_10 (by norm_num)

theorem c22250R_54_8 : rowsJ2 54 55 29 360 ≤ 17694758315581 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_676 c22250R_54_9 (by norm_num)

theorem c22250R_54_7 : rowsJ2 54 55 28 360 ≤ 17776365690407 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_675 c22250R_54_8 (by norm_num)

theorem c22250R_54_6 : rowsJ2 54 55 27 360 ≤ 17870797549992 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_674 c22250R_54_7 (by norm_num)

theorem c22250R_54_5 : rowsJ2 54 55 26 360 ≤ 17984181338389 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_673 c22250R_54_6 (by norm_num)

theorem c22250R_54_4 : rowsJ2 54 55 25 360 ≤ 18116715787539 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_672 c22250R_54_5 (by norm_num)

theorem c22250R_54_3 : rowsJ2 54 55 23 360 ≤ 18454105847606 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_671 c22250R_54_4 (by norm_num)

theorem c22250R_54_2 : rowsJ2 54 55 20 360 ≤ 19178144653914 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_670 c22250R_54_3 (by norm_num)

theorem c22250R_54_1 : rowsJ2 54 55 15 360 ≤ 21047373013664 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_669 c22250R_54_2 (by norm_num)

theorem c22250R_54_0 : rowsJ2 54 55 0 360 ≤ 23004945161482 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22250R_668 c22250R_54_1 (by norm_num)

theorem hr22250R_54 : rows2 54 55 ≤ 23004945161482 := rows2_le_of_rowsJ2 54 55 c22250R_54_0

theorem c22250R_55_33 : rowsJ2 55 56 54 360 ≤ 11097033486946 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_735 rows22250R_736 (by norm_num)

theorem c22250R_55_32 : rowsJ2 55 56 53 360 ≤ 15095000856262 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_734 c22250R_55_33 (by norm_num)

theorem c22250R_55_31 : rowsJ2 55 56 52 360 ≤ 18146700983026 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_733 c22250R_55_32 (by norm_num)

theorem c22250R_55_30 : rowsJ2 55 56 51 360 ≤ 20275979466483 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_732 c22250R_55_31 (by norm_num)

theorem c22250R_55_29 : rowsJ2 55 56 50 360 ≤ 21755162067035 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_731 c22250R_55_30 (by norm_num)

theorem c22250R_55_28 : rowsJ2 55 56 49 360 ≤ 22738641806320 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_730 c22250R_55_29 (by norm_num)

theorem c22250R_55_27 : rowsJ2 55 56 48 360 ≤ 23266789359407 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_729 c22250R_55_28 (by norm_num)

theorem c22250R_55_26 : rowsJ2 55 56 47 360 ≤ 23384631066587 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_728 c22250R_55_27 (by norm_num)

theorem c22250R_55_25 : rowsJ2 55 56 46 360 ≤ 23384631066587 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_727 c22250R_55_26 (by norm_num)

theorem c22250R_55_24 : rowsJ2 55 56 45 360 ≤ 23384631066587 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_726 c22250R_55_25 (by norm_num)

theorem c22250R_55_23 : rowsJ2 55 56 44 360 ≤ 23384631066587 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_725 c22250R_55_24 (by norm_num)

theorem c22250R_55_22 : rowsJ2 55 56 43 360 ≤ 23384631066587 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_724 c22250R_55_23 (by norm_num)

theorem c22250R_55_21 : rowsJ2 55 56 42 360 ≤ 23384631066587 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_723 c22250R_55_22 (by norm_num)

theorem c22250R_55_20 : rowsJ2 55 56 41 360 ≤ 23384631066587 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_722 c22250R_55_21 (by norm_num)

theorem c22250R_55_19 : rowsJ2 55 56 40 360 ≤ 23384631066587 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_721 c22250R_55_20 (by norm_num)

theorem c22250R_55_18 : rowsJ2 55 56 39 360 ≤ 23384631066587 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_720 c22250R_55_19 (by norm_num)

theorem c22250R_55_17 : rowsJ2 55 56 38 360 ≤ 23384631066587 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_719 c22250R_55_18 (by norm_num)

theorem c22250R_55_16 : rowsJ2 55 56 37 360 ≤ 23385062164874 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_718 c22250R_55_17 (by norm_num)

theorem c22250R_55_15 : rowsJ2 55 56 36 360 ≤ 23385928579890 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_717 c22250R_55_16 (by norm_num)

theorem c22250R_55_14 : rowsJ2 55 56 35 360 ≤ 23390818319542 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_716 c22250R_55_15 (by norm_num)

theorem c22250R_55_13 : rowsJ2 55 56 34 360 ≤ 23399753184046 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_715 c22250R_55_14 (by norm_num)

theorem c22250R_55_12 : rowsJ2 55 56 33 360 ≤ 23415839183317 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_714 c22250R_55_13 (by norm_num)

theorem c22250R_55_11 : rowsJ2 55 56 32 360 ≤ 23439120356745 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_713 c22250R_55_12 (by norm_num)

theorem c22250R_55_10 : rowsJ2 55 56 31 360 ≤ 23472683438640 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_712 c22250R_55_11 (by norm_num)

theorem c22250R_55_9 : rowsJ2 55 56 30 360 ≤ 23516175057056 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_711 c22250R_55_10 (by norm_num)

theorem c22250R_55_8 : rowsJ2 55 56 29 360 ≤ 23572165739561 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_710 c22250R_55_9 (by norm_num)

theorem c22250R_55_7 : rowsJ2 55 56 28 360 ≤ 23638236132506 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_709 c22250R_55_8 (by norm_num)

theorem c22250R_55_6 : rowsJ2 55 56 27 360 ≤ 23717079837947 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_708 c22250R_55_7 (by norm_num)

theorem c22250R_55_5 : rowsJ2 55 56 26 360 ≤ 23811844555143 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_707 c22250R_55_6 (by norm_num)

theorem c22250R_55_4 : rowsJ2 55 56 25 360 ≤ 23925647811297 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_706 c22250R_55_5 (by norm_num)

theorem c22250R_55_3 : rowsJ2 55 56 23 360 ≤ 24215878835106 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_705 c22250R_55_4 (by norm_num)

theorem c22250R_55_2 : rowsJ2 55 56 20 360 ≤ 24849281506163 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_704 c22250R_55_3 (by norm_num)

theorem c22250R_55_1 : rowsJ2 55 56 15 360 ≤ 26553955861908 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_703 c22250R_55_2 (by norm_num)

theorem c22250R_55_0 : rowsJ2 55 56 0 360 ≤ 28525934301465 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22250R_702 c22250R_55_1 (by norm_num)

theorem hr22250R_55 : rows2 55 56 ≤ 28525934301465 := rows2_le_of_rowsJ2 55 56 c22250R_55_0

theorem c22250R_56_34 : rowsJ2 56 57 55 360 ≤ 13557597931989 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_771 rows22250R_772 (by norm_num)

theorem c22250R_56_33 : rowsJ2 56 57 54 360 ≤ 18476177558250 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_770 c22250R_56_34 (by norm_num)

theorem c22250R_56_32 : rowsJ2 56 57 53 360 ≤ 22436356507351 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_769 c22250R_56_33 (by norm_num)

theorem c22250R_56_31 : rowsJ2 56 57 52 360 ≤ 25459212244928 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_768 c22250R_56_32 (by norm_num)

theorem c22250R_56_30 : rowsJ2 56 57 51 360 ≤ 27568364983808 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_767 c22250R_56_31 (by norm_num)

theorem c22250R_56_29 : rowsJ2 56 57 50 360 ≤ 29033566486338 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_766 c22250R_56_30 (by norm_num)

theorem c22250R_56_28 : rowsJ2 56 57 49 360 ≤ 30007750465495 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_765 c22250R_56_29 (by norm_num)

theorem c22250R_56_27 : rowsJ2 56 57 48 360 ≤ 30530906016440 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_764 c22250R_56_28 (by norm_num)

theorem c22250R_56_26 : rowsJ2 56 57 47 360 ≤ 30647633894631 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_763 c22250R_56_27 (by norm_num)

theorem c22250R_56_25 : rowsJ2 56 57 46 360 ≤ 30647633894631 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_762 c22250R_56_26 (by norm_num)

theorem c22250R_56_24 : rowsJ2 56 57 45 360 ≤ 30647633894631 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_761 c22250R_56_25 (by norm_num)

theorem c22250R_56_23 : rowsJ2 56 57 44 360 ≤ 30647633894631 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_760 c22250R_56_24 (by norm_num)

theorem c22250R_56_22 : rowsJ2 56 57 43 360 ≤ 30647633894631 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_759 c22250R_56_23 (by norm_num)

theorem c22250R_56_21 : rowsJ2 56 57 42 360 ≤ 30647633894631 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_758 c22250R_56_22 (by norm_num)

theorem c22250R_56_20 : rowsJ2 56 57 41 360 ≤ 30647633894631 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_757 c22250R_56_21 (by norm_num)

theorem c22250R_56_19 : rowsJ2 56 57 40 360 ≤ 30647633894631 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_756 c22250R_56_20 (by norm_num)

theorem c22250R_56_18 : rowsJ2 56 57 39 360 ≤ 30647633894631 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_755 c22250R_56_19 (by norm_num)

theorem c22250R_56_17 : rowsJ2 56 57 38 360 ≤ 30647633894631 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_754 c22250R_56_18 (by norm_num)

theorem c22250R_56_16 : rowsJ2 56 57 37 360 ≤ 30647633894631 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_753 c22250R_56_17 (by norm_num)

theorem c22250R_56_15 : rowsJ2 56 57 36 360 ≤ 30648065895255 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_752 c22250R_56_16 (by norm_num)

theorem c22250R_56_14 : rowsJ2 56 57 35 360 ≤ 30648934241732 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_751 c22250R_56_15 (by norm_num)

theorem c22250R_56_13 : rowsJ2 56 57 34 360 ≤ 30653835563476 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_750 c22250R_56_14 (by norm_num)

theorem c22250R_56_12 : rowsJ2 56 57 33 360 ≤ 30662345214070 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_749 c22250R_56_13 (by norm_num)

theorem c22250R_56_11 : rowsJ2 56 57 32 360 ≤ 30678026896840 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_748 c22250R_56_12 (by norm_num)

theorem c22250R_56_10 : rowsJ2 56 57 31 360 ≤ 30700480253433 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_747 c22250R_56_11 (by norm_num)

theorem c22250R_56_9 : rowsJ2 56 57 30 360 ≤ 30733250202302 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_746 c22250R_56_10 (by norm_num)

theorem c22250R_56_8 : rowsJ2 56 57 29 360 ≤ 30774675220150 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_745 c22250R_56_9 (by norm_num)

theorem c22250R_56_7 : rowsJ2 56 57 28 360 ≤ 30828208346490 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_744 c22250R_56_8 (by norm_num)

theorem c22250R_56_6 : rowsJ2 56 57 27 360 ≤ 30891497694283 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_743 c22250R_56_7 (by norm_num)

theorem c22250R_56_5 : rowsJ2 56 57 26 360 ≤ 30970626516331 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_742 c22250R_56_6 (by norm_num)

theorem c22250R_56_4 : rowsJ2 56 57 25 360 ≤ 31065750480498 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_741 c22250R_56_5 (by norm_num)

theorem c22250R_56_3 : rowsJ2 56 57 23 360 ≤ 31313606909356 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_740 c22250R_56_4 (by norm_num)

theorem c22250R_56_2 : rowsJ2 56 57 20 360 ≤ 31865909423491 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_739 c22250R_56_3 (by norm_num)

theorem c22250R_56_1 : rowsJ2 56 57 15 360 ≤ 33407338671901 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_738 c22250R_56_2 (by norm_num)

theorem c22250R_56_0 : rowsJ2 56 57 0 360 ≤ 35383260214206 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22250R_737 c22250R_56_1 (by norm_num)

theorem hr22250R_56 : rows2 56 57 ≤ 35383260214206 := rows2_le_of_rowsJ2 56 57 c22250R_56_0

theorem c22250R_57_35 : rowsJ2 57 58 56 360 ≤ 16293124990284 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_808 rows22250R_809 (by norm_num)

theorem c22250R_57_34 : rowsJ2 57 58 55 360 ≤ 22309821448054 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_807 c22250R_57_35 (by norm_num)

theorem c22250R_57_33 : rowsJ2 57 58 54 360 ≤ 27182346416035 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_806 c22250R_57_34 (by norm_num)

theorem c22250R_57_32 : rowsJ2 57 58 53 360 ≤ 31105444601566 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_805 c22250R_57_33 (by norm_num)

theorem c22250R_57_31 : rowsJ2 57 58 52 360 ≤ 34099996113405 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_804 c22250R_57_32 (by norm_num)

theorem c22250R_57_30 : rowsJ2 57 58 51 360 ≤ 36189399998746 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_803 c22250R_57_31 (by norm_num)

theorem c22250R_57_29 : rowsJ2 57 58 50 360 ≤ 37640882224647 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_802 c22250R_57_30 (by norm_num)

theorem c22250R_57_28 : rowsJ2 57 58 49 360 ≤ 38605944523628 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_801 c22250R_57_29 (by norm_num)

theorem c22250R_57_27 : rowsJ2 57 58 48 360 ≤ 39124201556715 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_800 c22250R_57_28 (by norm_num)

theorem c22250R_57_26 : rowsJ2 57 58 47 360 ≤ 39239836464385 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_799 c22250R_57_27 (by norm_num)

theorem c22250R_57_25 : rowsJ2 57 58 46 360 ≤ 39239836464385 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_798 c22250R_57_26 (by norm_num)

theorem c22250R_57_24 : rowsJ2 57 58 45 360 ≤ 39239836464385 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_797 c22250R_57_25 (by norm_num)

theorem c22250R_57_23 : rowsJ2 57 58 44 360 ≤ 39239836464385 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_796 c22250R_57_24 (by norm_num)

theorem c22250R_57_22 : rowsJ2 57 58 43 360 ≤ 39239836464385 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_795 c22250R_57_23 (by norm_num)

theorem c22250R_57_21 : rowsJ2 57 58 42 360 ≤ 39239836464385 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_794 c22250R_57_22 (by norm_num)

theorem c22250R_57_20 : rowsJ2 57 58 41 360 ≤ 39239836464385 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_793 c22250R_57_21 (by norm_num)

theorem c22250R_57_19 : rowsJ2 57 58 40 360 ≤ 39239836464385 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_792 c22250R_57_20 (by norm_num)

theorem c22250R_57_18 : rowsJ2 57 58 39 360 ≤ 39239836464385 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_791 c22250R_57_19 (by norm_num)

theorem c22250R_57_17 : rowsJ2 57 58 38 360 ≤ 39239836464385 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_790 c22250R_57_18 (by norm_num)

theorem c22250R_57_16 : rowsJ2 57 58 37 360 ≤ 39239836464385 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_789 c22250R_57_17 (by norm_num)

theorem c22250R_57_15 : rowsJ2 57 58 36 360 ≤ 39239836464385 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_788 c22250R_57_16 (by norm_num)

theorem c22250R_57_14 : rowsJ2 57 58 35 360 ≤ 39240269466733 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_787 c22250R_57_15 (by norm_num)

theorem c22250R_57_13 : rowsJ2 57 58 34 360 ≤ 39241139947789 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_786 c22250R_57_14 (by norm_num)

theorem c22250R_57_12 : rowsJ2 57 58 33 360 ≤ 39245610556301 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_785 c22250R_57_13 (by norm_num)

theorem c22250R_57_11 : rowsJ2 57 58 32 360 ≤ 39253700703385 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_784 c22250R_57_12 (by norm_num)

theorem c22250R_57_10 : rowsJ2 57 58 31 360 ≤ 39268543001681 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_783 c22250R_57_11 (by norm_num)

theorem c22250R_57_9 : rowsJ2 57 58 30 360 ≤ 39290180696543 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_782 c22250R_57_10 (by norm_num)

theorem c22250R_57_8 : rowsJ2 57 58 29 360 ≤ 39321299339866 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_781 c22250R_57_9 (by norm_num)

theorem c22250R_57_7 : rowsJ2 57 58 28 360 ≤ 39360672214534 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_780 c22250R_57_8 (by norm_num)

theorem c22250R_57_6 : rowsJ2 57 58 27 360 ≤ 39411414062917 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_779 c22250R_57_7 (by norm_num)

theorem c22250R_57_5 : rowsJ2 57 58 26 360 ≤ 39474937954389 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_778 c22250R_57_6 (by norm_num)

theorem c22250R_57_4 : rowsJ2 57 58 25 360 ≤ 39554373845419 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_777 c22250R_57_5 (by norm_num)

theorem c22250R_57_3 : rowsJ2 57 58 23 360 ≤ 39764624072053 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_776 c22250R_57_4 (by norm_num)

theorem c22250R_57_2 : rowsJ2 57 58 20 360 ≤ 40240732046471 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_775 c22250R_57_3 (by norm_num)

theorem c22250R_57_1 : rowsJ2 57 58 15 360 ≤ 41624710248950 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_774 c22250R_57_2 (by norm_num)

theorem c22250R_57_0 : rowsJ2 57 58 0 360 ≤ 43592930086466 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22250R_773 c22250R_57_1 (by norm_num)

theorem hr22250R_57 : rows2 57 58 ≤ 43592930086466 := rows2_le_of_rowsJ2 57 58 c22250R_57_0

theorem c22250R_58_36 : rowsJ2 58 59 57 360 ≤ 18975861878399 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_846 rows22250R_847 (by norm_num)

theorem c22250R_58_35 : rowsJ2 58 59 56 360 ≤ 26321042152487 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_845 c22250R_58_36 (by norm_num)

theorem c22250R_58_34 : rowsJ2 58 59 55 360 ≤ 32281924448840 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_844 c22250R_58_35 (by norm_num)

theorem c22250R_58_33 : rowsJ2 58 59 54 360 ≤ 37109249214855 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_843 c22250R_58_34 (by norm_num)

theorem c22250R_58_32 : rowsJ2 58 59 53 360 ≤ 40995954599630 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_842 c22250R_58_33 (by norm_num)

theorem c22250R_58_31 : rowsJ2 58 59 52 360 ≤ 43962727016643 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_841 c22250R_58_32 (by norm_num)

theorem c22250R_58_30 : rowsJ2 58 59 51 360 ≤ 46032748450746 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_840 c22250R_58_31 (by norm_num)

theorem c22250R_58_29 : rowsJ2 58 59 50 360 ≤ 47470765935022 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_839 c22250R_58_30 (by norm_num)

theorem c22250R_58_28 : rowsJ2 58 59 49 360 ≤ 48426875789203 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_838 c22250R_58_29 (by norm_num)

theorem c22250R_58_27 : rowsJ2 58 59 48 360 ≤ 48940325187087 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_837 c22250R_58_28 (by norm_num)

theorem c22250R_58_26 : rowsJ2 58 59 47 360 ≤ 49054887402218 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_836 c22250R_58_27 (by norm_num)

theorem c22250R_58_25 : rowsJ2 58 59 46 360 ≤ 49054887402218 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_835 c22250R_58_26 (by norm_num)

theorem c22250R_58_24 : rowsJ2 58 59 45 360 ≤ 49054887402218 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_834 c22250R_58_25 (by norm_num)

theorem c22250R_58_23 : rowsJ2 58 59 44 360 ≤ 49054887402218 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_833 c22250R_58_24 (by norm_num)

theorem c22250R_58_22 : rowsJ2 58 59 43 360 ≤ 49054887402218 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_832 c22250R_58_23 (by norm_num)

theorem c22250R_58_21 : rowsJ2 58 59 42 360 ≤ 49054887402218 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_831 c22250R_58_22 (by norm_num)

theorem c22250R_58_20 : rowsJ2 58 59 41 360 ≤ 49054887402218 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_830 c22250R_58_21 (by norm_num)

theorem c22250R_58_19 : rowsJ2 58 59 40 360 ≤ 49054887402218 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_829 c22250R_58_20 (by norm_num)

theorem c22250R_58_18 : rowsJ2 58 59 39 360 ≤ 49054887402218 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_828 c22250R_58_19 (by norm_num)

theorem c22250R_58_17 : rowsJ2 58 59 38 360 ≤ 49054887402218 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_827 c22250R_58_18 (by norm_num)

theorem c22250R_58_16 : rowsJ2 58 59 37 360 ≤ 49054887402218 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_826 c22250R_58_17 (by norm_num)

theorem c22250R_58_15 : rowsJ2 58 59 36 360 ≤ 49054887402218 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_825 c22250R_58_16 (by norm_num)

theorem c22250R_58_14 : rowsJ2 58 59 35 360 ≤ 49054887402218 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_824 c22250R_58_15 (by norm_num)

theorem c22250R_58_13 : rowsJ2 58 59 34 360 ≤ 49055321507037 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_823 c22250R_58_14 (by norm_num)

theorem c22250R_58_12 : rowsJ2 58 59 33 360 ≤ 49055754981015 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_822 c22250R_58_13 (by norm_num)

theorem c22250R_58_11 : rowsJ2 58 59 32 360 ≤ 49059799491226 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_821 c22250R_58_12 (by norm_num)

theorem c22250R_58_10 : rowsJ2 58 59 31 360 ≤ 49067037179552 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_820 c22250R_58_11 (by norm_num)

theorem c22250R_58_9 : rowsJ2 58 59 30 360 ≤ 49081050103768 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_819 c22250R_58_10 (by norm_num)

theorem c22250R_58_8 : rowsJ2 58 59 29 360 ≤ 49101445913126 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_818 c22250R_58_9 (by norm_num)

theorem c22250R_58_7 : rowsJ2 58 59 28 360 ≤ 49130927110857 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_817 c22250R_58_8 (by norm_num)

theorem c22250R_58_6 : rowsJ2 58 59 27 360 ≤ 49169136042754 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_816 c22250R_58_7 (by norm_num)

theorem c22250R_58_5 : rowsJ2 58 59 26 360 ≤ 49220070400685 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_815 c22250R_58_6 (by norm_num)

theorem c22250R_58_4 : rowsJ2 58 59 25 360 ≤ 49283846395771 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_814 c22250R_58_5 (by norm_num)

theorem c22250R_58_3 : rowsJ2 58 59 24 360 ≤ 49363611796381 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_813 c22250R_58_4 (by norm_num)

theorem c22250R_58_2 : rowsJ2 58 59 21 360 ≤ 49709621393252 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_812 c22250R_58_3 (by norm_num)

theorem c22250R_58_1 : rowsJ2 58 59 16 360 ≤ 50792236663938 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_811 c22250R_58_2 (by norm_num)

theorem c22250R_58_0 : rowsJ2 58 59 0 360 ≤ 53051882646399 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22250R_810 c22250R_58_1 (by norm_num)

theorem hr22250R_58 : rows2 58 59 ≤ 53051882646399 := rows2_le_of_rowsJ2 58 59 c22250R_58_0

theorem c22250R_59_37 : rowsJ2 59 60 58 360 ≤ 21289356853065 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_885 rows22250R_886 (by norm_num)

theorem c22250R_59_36 : rowsJ2 59 60 57 360 ≤ 30005303763533 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_884 c22250R_59_37 (by norm_num)

theorem c22250R_59_35 : rowsJ2 59 60 56 360 ≤ 37282972409707 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_883 c22250R_59_36 (by norm_num)

theorem c22250R_59_34 : rowsJ2 59 60 55 360 ≤ 43189066552111 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_882 c22250R_59_35 (by norm_num)

theorem c22250R_59_33 : rowsJ2 59 60 54 360 ≤ 47972022011826 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_881 c22250R_59_34 (by norm_num)

theorem c22250R_59_32 : rowsJ2 59 60 53 360 ≤ 51823003588886 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_880 c22250R_59_33 (by norm_num)

theorem c22250R_59_31 : rowsJ2 59 60 52 360 ≤ 54762507562098 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_879 c22250R_59_32 (by norm_num)

theorem c22250R_59_30 : rowsJ2 59 60 51 360 ≤ 56813502844140 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_878 c22250R_59_31 (by norm_num)

theorem c22250R_59_29 : rowsJ2 59 60 50 360 ≤ 58238303103280 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_877 c22250R_59_30 (by norm_num)

theorem c22250R_59_28 : rowsJ2 59 60 49 360 ≤ 59185625081559 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_876 c22250R_59_29 (by norm_num)

theorem c22250R_59_27 : rowsJ2 59 60 48 360 ≤ 59694355220907 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_875 c22250R_59_28 (by norm_num)

theorem c22250R_59_26 : rowsJ2 59 60 47 360 ≤ 59807864462339 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_874 c22250R_59_27 (by norm_num)

theorem c22250R_59_25 : rowsJ2 59 60 46 360 ≤ 59807864462339 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_873 c22250R_59_26 (by norm_num)

theorem c22250R_59_24 : rowsJ2 59 60 45 360 ≤ 59807864462339 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_872 c22250R_59_25 (by norm_num)

theorem c22250R_59_23 : rowsJ2 59 60 44 360 ≤ 59807864462339 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_871 c22250R_59_24 (by norm_num)

theorem c22250R_59_22 : rowsJ2 59 60 43 360 ≤ 59807864462339 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_870 c22250R_59_23 (by norm_num)

theorem c22250R_59_21 : rowsJ2 59 60 42 360 ≤ 59807864462339 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_869 c22250R_59_22 (by norm_num)

theorem c22250R_59_20 : rowsJ2 59 60 41 360 ≤ 59807864462339 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_868 c22250R_59_21 (by norm_num)

theorem c22250R_59_19 : rowsJ2 59 60 40 360 ≤ 59807864462339 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_867 c22250R_59_20 (by norm_num)

theorem c22250R_59_18 : rowsJ2 59 60 39 360 ≤ 59807864462339 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_866 c22250R_59_19 (by norm_num)

theorem c22250R_59_17 : rowsJ2 59 60 38 360 ≤ 59807864462339 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_865 c22250R_59_18 (by norm_num)

theorem c22250R_59_16 : rowsJ2 59 60 37 360 ≤ 59807864462339 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_864 c22250R_59_17 (by norm_num)

theorem c22250R_59_15 : rowsJ2 59 60 36 360 ≤ 59807864462339 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_863 c22250R_59_16 (by norm_num)

theorem c22250R_59_14 : rowsJ2 59 60 35 360 ≤ 59807864462339 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_862 c22250R_59_15 (by norm_num)

theorem c22250R_59_13 : rowsJ2 59 60 34 360 ≤ 59807864462339 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_861 c22250R_59_14 (by norm_num)

theorem c22250R_59_12 : rowsJ2 59 60 33 360 ≤ 59807864462339 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_860 c22250R_59_13 (by norm_num)

theorem c22250R_59_11 : rowsJ2 59 60 32 360 ≤ 59807864462339 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_859 c22250R_59_12 (by norm_num)

theorem c22250R_59_10 : rowsJ2 59 60 31 360 ≤ 59811052843543 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_858 c22250R_59_11 (by norm_num)

theorem c22250R_59_9 : rowsJ2 59 60 30 360 ≤ 59817445965009 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_857 c22250R_59_10 (by norm_num)

theorem c22250R_59_8 : rowsJ2 59 60 29 360 ≤ 59830205150319 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_856 c22250R_59_9 (by norm_num)

theorem c22250R_59_7 : rowsJ2 59 60 28 360 ≤ 59849372324906 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_855 c22250R_59_8 (by norm_num)

theorem c22250R_59_6 : rowsJ2 59 60 27 360 ≤ 59878096089496 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_854 c22250R_59_7 (by norm_num)

theorem c22250R_59_5 : rowsJ2 59 60 26 360 ≤ 59916453283097 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_853 c22250R_59_6 (by norm_num)

theorem c22250R_59_4 : rowsJ2 59 60 25 360 ≤ 59967594182181 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_852 c22250R_59_5 (by norm_num)

theorem c22250R_59_3 : rowsJ2 59 60 24 360 ≤ 60031640239163 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_851 c22250R_59_4 (by norm_num)

theorem c22250R_59_2 : rowsJ2 59 60 21 360 ≤ 60323936717026 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_850 c22250R_59_3 (by norm_num)

theorem c22250R_59_1 : rowsJ2 59 60 16 360 ≤ 61266351093142 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_849 c22250R_59_2 (by norm_num)

theorem c22250R_59_0 : rowsJ2 59 60 0 360 ≤ 63467420678488 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22250R_848 c22250R_59_1 (by norm_num)

theorem hr22250R_59 : rows2 59 60 ≤ 63467420678488 := rows2_le_of_rowsJ2 59 60 c22250R_59_0

theorem c22250R_60_38 : rowsJ2 60 61 59 360 ≤ 23317640877651 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_925 rows22250R_926 (by norm_num)

theorem c22250R_60_37 : rowsJ2 60 61 58 360 ≤ 33160311321759 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_924 c22250R_60_38 (by norm_num)

theorem c22250R_60_36 : rowsJ2 60 61 57 360 ≤ 41759318573526 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_923 c22250R_60_37 (by norm_num)

theorem c22250R_60_35 : rowsJ2 60 61 56 360 ≤ 48970705325855 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_922 c22250R_60_36 (by norm_num)

theorem c22250R_60_34 : rowsJ2 60 61 55 360 ≤ 54823009288466 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_921 c22250R_60_35 (by norm_num)

theorem c22250R_60_33 : rowsJ2 60 61 54 360 ≤ 59562403635210 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_920 c22250R_60_34 (by norm_num)

theorem c22250R_60_32 : rowsJ2 60 61 53 360 ≤ 63378312118880 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_919 c22250R_60_33 (by norm_num)

theorem c22250R_60_31 : rowsJ2 60 61 52 360 ≤ 66291044346938 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_918 c22250R_60_32 (by norm_num)

theorem c22250R_60_30 : rowsJ2 60 61 51 360 ≤ 68323360041027 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_917 c22250R_60_31 (by norm_num)

theorem c22250R_60_29 : rowsJ2 60 61 50 360 ≤ 69735183828700 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_916 c22250R_60_30 (by norm_num)

theorem c22250R_60_28 : rowsJ2 60 61 49 360 ≤ 70673878003508 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_915 c22250R_60_29 (by norm_num)

theorem c22250R_60_27 : rowsJ2 60 61 48 360 ≤ 71177974846298 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_914 c22250R_60_28 (by norm_num)

theorem c22250R_60_26 : rowsJ2 60 61 47 360 ≤ 71290450294098 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_913 c22250R_60_27 (by norm_num)

theorem c22250R_60_25 : rowsJ2 60 61 46 360 ≤ 71290450294098 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_912 c22250R_60_26 (by norm_num)

theorem c22250R_60_24 : rowsJ2 60 61 45 360 ≤ 71290450294098 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_911 c22250R_60_25 (by norm_num)

theorem c22250R_60_23 : rowsJ2 60 61 44 360 ≤ 71290450294098 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_910 c22250R_60_24 (by norm_num)

theorem c22250R_60_22 : rowsJ2 60 61 43 360 ≤ 71290450294098 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_909 c22250R_60_23 (by norm_num)

theorem c22250R_60_21 : rowsJ2 60 61 42 360 ≤ 71290450294098 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_908 c22250R_60_22 (by norm_num)

theorem c22250R_60_20 : rowsJ2 60 61 41 360 ≤ 71290450294098 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_907 c22250R_60_21 (by norm_num)

theorem c22250R_60_19 : rowsJ2 60 61 40 360 ≤ 71290450294098 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_906 c22250R_60_20 (by norm_num)

theorem c22250R_60_18 : rowsJ2 60 61 39 360 ≤ 71290450294098 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_905 c22250R_60_19 (by norm_num)

theorem c22250R_60_17 : rowsJ2 60 61 38 360 ≤ 71290450294098 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_904 c22250R_60_18 (by norm_num)

theorem c22250R_60_16 : rowsJ2 60 61 37 360 ≤ 71290450294098 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_903 c22250R_60_17 (by norm_num)

theorem c22250R_60_15 : rowsJ2 60 61 36 360 ≤ 71290450294098 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_902 c22250R_60_16 (by norm_num)

theorem c22250R_60_14 : rowsJ2 60 61 35 360 ≤ 71290450294098 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_901 c22250R_60_15 (by norm_num)

theorem c22250R_60_13 : rowsJ2 60 61 34 360 ≤ 71290450294098 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_900 c22250R_60_14 (by norm_num)

theorem c22250R_60_12 : rowsJ2 60 61 33 360 ≤ 71290450294098 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_899 c22250R_60_13 (by norm_num)

theorem c22250R_60_11 : rowsJ2 60 61 32 360 ≤ 71290450294098 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_898 c22250R_60_12 (by norm_num)

theorem c22250R_60_10 : rowsJ2 60 61 31 360 ≤ 71290450294098 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_897 c22250R_60_11 (by norm_num)

theorem c22250R_60_9 : rowsJ2 60 61 30 360 ≤ 71293649228274 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_896 c22250R_60_10 (by norm_num)

theorem c22250R_60_8 : rowsJ2 60 61 29 360 ≤ 71300064517283 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_895 c22250R_60_9 (by norm_num)

theorem c22250R_60_7 : rowsJ2 60 61 28 360 ≤ 71312870006187 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_894 c22250R_60_8 (by norm_num)

theorem c22250R_60_6 : rowsJ2 60 61 27 360 ≤ 71332109917978 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_893 c22250R_60_7 (by norm_num)

theorem c22250R_60_5 : rowsJ2 60 61 26 360 ≤ 71360947575277 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_892 c22250R_60_6 (by norm_num)

theorem c22250R_60_4 : rowsJ2 60 61 25 360 ≤ 71399463562872 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_891 c22250R_60_5 (by norm_num)

theorem c22250R_60_3 : rowsJ2 60 61 24 360 ≤ 71450825359081 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_890 c22250R_60_4 (by norm_num)

theorem c22250R_60_2 : rowsJ2 60 61 21 360 ≤ 71692490887090 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_889 c22250R_60_3 (by norm_num)

theorem c22250R_60_1 : rowsJ2 60 61 16 360 ≤ 72509212983767 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_888 c22250R_60_2 (by norm_num)

theorem c22250R_60_0 : rowsJ2 60 61 0 360 ≤ 74640465507534 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22250R_887 c22250R_60_1 (by norm_num)

theorem hr22250R_60 : rows2 60 61 ≤ 74640465507534 := rows2_le_of_rowsJ2 60 61 c22250R_60_0

theorem c22250R_61_39 : rowsJ2 61 62 60 360 ≤ 24930254003675 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_966 rows22250R_967 (by norm_num)

theorem c22250R_61_38 : rowsJ2 61 62 59 360 ≤ 35697897450582 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_965 c22250R_61_39 (by norm_num)

theorem c22250R_61_37 : rowsJ2 61 62 58 360 ≤ 45336834704247 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_964 c22250R_61_38 (by norm_num)

theorem c22250R_61_36 : rowsJ2 61 62 57 360 ≤ 53820306228533 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_963 c22250R_61_37 (by norm_num)

theorem c22250R_61_35 : rowsJ2 61 62 56 360 ≤ 60966607524659 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_962 c22250R_61_36 (by norm_num)

theorem c22250R_61_34 : rowsJ2 61 62 55 360 ≤ 66766092260353 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_961 c22250R_61_35 (by norm_num)

theorem c22250R_61_33 : rowsJ2 61 62 54 360 ≤ 71462711804723 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_960 c22250R_61_34 (by norm_num)

theorem c22250R_61_32 : rowsJ2 61 62 53 360 ≤ 75244180290509 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_959 c22250R_61_33 (by norm_num)

theorem c22250R_61_31 : rowsJ2 61 62 52 360 ≤ 78130624023389 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_958 c22250R_61_32 (by norm_num)

theorem c22250R_61_30 : rowsJ2 61 62 51 360 ≤ 80144597310030 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_957 c22250R_61_31 (by norm_num)

theorem c22250R_61_29 : rowsJ2 61 62 50 360 ≤ 81543678861230 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_956 c22250R_61_30 (by norm_num)

theorem c22250R_61_28 : rowsJ2 61 62 49 360 ≤ 82473900970859 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_955 c22250R_61_29 (by norm_num)

theorem c22250R_61_27 : rowsJ2 61 62 48 360 ≤ 82973448151551 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_954 c22250R_61_28 (by norm_num)

theorem c22250R_61_26 : rowsJ2 61 62 47 360 ≤ 83084908466467 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_953 c22250R_61_27 (by norm_num)

theorem c22250R_61_25 : rowsJ2 61 62 46 360 ≤ 83084908466467 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_952 c22250R_61_26 (by norm_num)

theorem c22250R_61_24 : rowsJ2 61 62 45 360 ≤ 83084908466467 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_951 c22250R_61_25 (by norm_num)

theorem c22250R_61_23 : rowsJ2 61 62 44 360 ≤ 83084908466467 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_950 c22250R_61_24 (by norm_num)

theorem c22250R_61_22 : rowsJ2 61 62 43 360 ≤ 83084908466467 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_949 c22250R_61_23 (by norm_num)

theorem c22250R_61_21 : rowsJ2 61 62 42 360 ≤ 83084908466467 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_948 c22250R_61_22 (by norm_num)

theorem c22250R_61_20 : rowsJ2 61 62 41 360 ≤ 83084908466467 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_947 c22250R_61_21 (by norm_num)

theorem c22250R_61_19 : rowsJ2 61 62 40 360 ≤ 83084908466467 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_946 c22250R_61_20 (by norm_num)

theorem c22250R_61_18 : rowsJ2 61 62 39 360 ≤ 83084908466467 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_945 c22250R_61_19 (by norm_num)

theorem c22250R_61_17 : rowsJ2 61 62 38 360 ≤ 83084908466467 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_944 c22250R_61_18 (by norm_num)

theorem c22250R_61_16 : rowsJ2 61 62 37 360 ≤ 83084908466467 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_943 c22250R_61_17 (by norm_num)

theorem c22250R_61_15 : rowsJ2 61 62 36 360 ≤ 83084908466467 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_942 c22250R_61_16 (by norm_num)

theorem c22250R_61_14 : rowsJ2 61 62 35 360 ≤ 83084908466467 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_941 c22250R_61_15 (by norm_num)

theorem c22250R_61_13 : rowsJ2 61 62 34 360 ≤ 83084908466467 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_940 c22250R_61_14 (by norm_num)

theorem c22250R_61_12 : rowsJ2 61 62 33 360 ≤ 83084908466467 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_939 c22250R_61_13 (by norm_num)

theorem c22250R_61_11 : rowsJ2 61 62 32 360 ≤ 83084908466467 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_938 c22250R_61_12 (by norm_num)

theorem c22250R_61_10 : rowsJ2 61 62 31 360 ≤ 83084908466467 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_937 c22250R_61_11 (by norm_num)

theorem c22250R_61_9 : rowsJ2 61 62 30 360 ≤ 83084908466467 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_936 c22250R_61_10 (by norm_num)

theorem c22250R_61_8 : rowsJ2 61 62 29 360 ≤ 83088118758931 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_935 c22250R_61_9 (by norm_num)

theorem c22250R_61_7 : rowsJ2 61 62 28 360 ≤ 83094557863388 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_934 c22250R_61_8 (by norm_num)

theorem c22250R_61_6 : rowsJ2 61 62 27 360 ≤ 83107413013942 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_933 c22250R_61_7 (by norm_num)

theorem c22250R_61_5 : rowsJ2 61 62 26 360 ≤ 83126730816350 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_932 c22250R_61_6 (by norm_num)

theorem c22250R_61_4 : rowsJ2 61 62 25 360 ≤ 83155690260076 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_931 c22250R_61_5 (by norm_num)

theorem c22250R_61_3 : rowsJ2 61 62 24 360 ≤ 83194375821854 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_930 c22250R_61_4 (by norm_num)

theorem c22250R_61_2 : rowsJ2 61 62 22 360 ≤ 83310615040855 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_929 c22250R_61_3 (by norm_num)

theorem c22250R_61_1 : rowsJ2 61 62 17 360 ≤ 83904880183371 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_928 c22250R_61_2 (by norm_num)

theorem c22250R_61_0 : rowsJ2 61 62 0 360 ≤ 86143553604306 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22250R_927 c22250R_61_1 (by norm_num)

theorem hr22250R_61 : rows2 61 62 ≤ 86143553604306 := rows2_le_of_rowsJ2 61 62 c22250R_61_0

theorem c22250R_62_40 : rowsJ2 62 63 61 360 ≤ 25880461809321 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_1008 rows22250R_1009 (by norm_num)

theorem c22250R_62_39 : rowsJ2 62 63 60 360 ≤ 37483535910392 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_1007 c22250R_62_40 (by norm_num)

theorem c22250R_62_38 : rowsJ2 62 63 59 360 ≤ 47959386467987 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_1006 c22250R_62_39 (by norm_num)

theorem c22250R_62_37 : rowsJ2 62 63 58 360 ≤ 57396030242110 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_1005 c22250R_62_38 (by norm_num)

theorem c22250R_62_36 : rowsJ2 62 63 57 360 ≤ 65727369635382 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_1004 c22250R_62_37 (by norm_num)

theorem c22250R_62_35 : rowsJ2 62 63 56 360 ≤ 72809749807835 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_1003 c22250R_62_36 (by norm_num)

theorem c22250R_62_34 : rowsJ2 62 63 55 360 ≤ 78557360215019 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_1002 c22250R_62_35 (by norm_num)

theorem c22250R_62_33 : rowsJ2 62 63 54 360 ≤ 83211970167806 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_1001 c22250R_62_34 (by norm_num)

theorem c22250R_62_32 : rowsJ2 62 63 53 360 ≤ 86959614762781 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_1000 c22250R_62_33 (by norm_num)

theorem c22250R_62_31 : rowsJ2 62 63 52 360 ≤ 89820240282969 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_999 c22250R_62_32 (by norm_num)

theorem c22250R_62_30 : rowsJ2 62 63 51 360 ≤ 91816199294780 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_998 c22250R_62_31 (by norm_num)

theorem c22250R_62_29 : rowsJ2 62 63 50 360 ≤ 93202766559057 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_997 c22250R_62_30 (by norm_num)

theorem c22250R_62_28 : rowsJ2 62 63 49 360 ≤ 94124668162728 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_996 c22250R_62_29 (by norm_num)

theorem c22250R_62_27 : rowsJ2 62 63 48 360 ≤ 94619747071541 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_995 c22250R_62_28 (by norm_num)

theorem c22250R_62_26 : rowsJ2 62 63 47 360 ≤ 94730210413579 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_994 c22250R_62_27 (by norm_num)

theorem c22250R_62_25 : rowsJ2 62 63 46 360 ≤ 94730210413579 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_993 c22250R_62_26 (by norm_num)

theorem c22250R_62_24 : rowsJ2 62 63 45 360 ≤ 94730210413579 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_992 c22250R_62_25 (by norm_num)

theorem c22250R_62_23 : rowsJ2 62 63 44 360 ≤ 94730210413579 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_991 c22250R_62_24 (by norm_num)

theorem c22250R_62_22 : rowsJ2 62 63 43 360 ≤ 94730210413579 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_990 c22250R_62_23 (by norm_num)

theorem c22250R_62_21 : rowsJ2 62 63 42 360 ≤ 94730210413579 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_989 c22250R_62_22 (by norm_num)

theorem c22250R_62_20 : rowsJ2 62 63 41 360 ≤ 94730210413579 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_988 c22250R_62_21 (by norm_num)

theorem c22250R_62_19 : rowsJ2 62 63 40 360 ≤ 94730210413579 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_987 c22250R_62_20 (by norm_num)

theorem c22250R_62_18 : rowsJ2 62 63 39 360 ≤ 94730210413579 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_986 c22250R_62_19 (by norm_num)

theorem c22250R_62_17 : rowsJ2 62 63 38 360 ≤ 94730210413579 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_985 c22250R_62_18 (by norm_num)

theorem c22250R_62_16 : rowsJ2 62 63 37 360 ≤ 94730210413579 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_984 c22250R_62_17 (by norm_num)

theorem c22250R_62_15 : rowsJ2 62 63 36 360 ≤ 94730210413579 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_983 c22250R_62_16 (by norm_num)

theorem c22250R_62_14 : rowsJ2 62 63 35 360 ≤ 94730210413579 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_982 c22250R_62_15 (by norm_num)

theorem c22250R_62_13 : rowsJ2 62 63 34 360 ≤ 94730210413579 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_981 c22250R_62_14 (by norm_num)

theorem c22250R_62_12 : rowsJ2 62 63 33 360 ≤ 94730210413579 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_980 c22250R_62_13 (by norm_num)

theorem c22250R_62_11 : rowsJ2 62 63 32 360 ≤ 94730210413579 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_979 c22250R_62_12 (by norm_num)

theorem c22250R_62_10 : rowsJ2 62 63 31 360 ≤ 94730210413579 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_978 c22250R_62_11 (by norm_num)

theorem c22250R_62_9 : rowsJ2 62 63 30 360 ≤ 94730210413579 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_977 c22250R_62_10 (by norm_num)

theorem c22250R_62_8 : rowsJ2 62 63 29 360 ≤ 94730210413579 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_976 c22250R_62_9 (by norm_num)

theorem c22250R_62_7 : rowsJ2 62 63 28 360 ≤ 94733432886093 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_975 c22250R_62_8 (by norm_num)

theorem c22250R_62_6 : rowsJ2 62 63 27 360 ≤ 94739897488976 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_974 c22250R_62_7 (by norm_num)

theorem c22250R_62_5 : rowsJ2 62 63 26 360 ≤ 94752805733633 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_973 c22250R_62_6 (by norm_num)

theorem c22250R_62_4 : rowsJ2 62 63 25 360 ≤ 94772206698821 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_972 c22250R_62_5 (by norm_num)

theorem c22250R_62_3 : rowsJ2 62 63 24 360 ≤ 94801296011712 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_971 c22250R_62_4 (by norm_num)

theorem c22250R_62_2 : rowsJ2 62 63 22 360 ≤ 94892010287393 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_970 c22250R_62_3 (by norm_num)

theorem c22250R_62_1 : rowsJ2 62 63 17 360 ≤ 95391646814608 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_969 c22250R_62_2 (by norm_num)

theorem c22250R_62_0 : rowsJ2 62 63 0 360 ≤ 97514913128870 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22250R_968 c22250R_62_1 (by norm_num)

theorem hr22250R_62 : rows2 62 63 ≤ 97514913128870 := rows2_le_of_rowsJ2 62 63 c22250R_62_0

theorem c22250R_63_41 : rowsJ2 63 64 62 360 ≤ 26277325446902 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1051 rows22250R_1052 (by norm_num)

theorem c22250R_63_40 : rowsJ2 63 64 61 360 ≤ 38385721600692 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1050 c22250R_63_41 (by norm_num)

theorem c22250R_63_39 : rowsJ2 63 64 60 360 ≤ 49606268461724 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1049 c22250R_63_40 (by norm_num)

theorem c22250R_63_38 : rowsJ2 63 64 59 360 ≤ 59791673141581 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1048 c22250R_63_39 (by norm_num)

theorem c22250R_63_37 : rowsJ2 63 64 58 360 ≤ 68989026728350 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1047 c22250R_63_38 (by norm_num)

theorem c22250R_63_36 : rowsJ2 63 64 57 360 ≤ 77169475191080 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1046 c22250R_63_37 (by norm_num)

theorem c22250R_63_35 : rowsJ2 63 64 56 360 ≤ 84151106018709 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1045 c22250R_63_36 (by norm_num)

theorem c22250R_63_34 : rowsJ2 63 64 55 360 ≤ 89847761865236 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1044 c22250R_63_35 (by norm_num)

theorem c22250R_63_33 : rowsJ2 63 64 54 360 ≤ 94461107085652 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1043 c22250R_63_34 (by norm_num)

theorem c22250R_63_32 : rowsJ2 63 64 53 360 ≤ 98175527510870 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1042 c22250R_63_33 (by norm_num)

theorem c22250R_63_31 : rowsJ2 63 64 52 360 ≤ 101010792593194 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1041 c22250R_63_32 (by norm_num)

theorem c22250R_63_30 : rowsJ2 63 64 51 360 ≤ 102989056735776 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1040 c22250R_63_31 (by norm_num)

theorem c22250R_63_29 : rowsJ2 63 64 50 360 ≤ 104363331600121 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1039 c22250R_63_30 (by norm_num)

theorem c22250R_63_28 : rowsJ2 63 64 49 360 ≤ 105277060226179 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1038 c22250R_63_29 (by norm_num)

theorem c22250R_63_27 : rowsJ2 63 64 48 360 ≤ 105767750088676 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1037 c22250R_63_28 (by norm_num)

theorem c22250R_63_26 : rowsJ2 63 64 47 360 ≤ 105877234134857 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1036 c22250R_63_27 (by norm_num)

theorem c22250R_63_25 : rowsJ2 63 64 46 360 ≤ 105877234134857 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1035 c22250R_63_26 (by norm_num)

theorem c22250R_63_24 : rowsJ2 63 64 45 360 ≤ 105877234134857 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1034 c22250R_63_25 (by norm_num)

theorem c22250R_63_23 : rowsJ2 63 64 44 360 ≤ 105877234134857 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1033 c22250R_63_24 (by norm_num)

theorem c22250R_63_22 : rowsJ2 63 64 43 360 ≤ 105877234134857 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1032 c22250R_63_23 (by norm_num)

theorem c22250R_63_21 : rowsJ2 63 64 42 360 ≤ 105877234134857 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1031 c22250R_63_22 (by norm_num)

theorem c22250R_63_20 : rowsJ2 63 64 41 360 ≤ 105877234134857 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1030 c22250R_63_21 (by norm_num)

theorem c22250R_63_19 : rowsJ2 63 64 40 360 ≤ 105877234134857 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1029 c22250R_63_20 (by norm_num)

theorem c22250R_63_18 : rowsJ2 63 64 39 360 ≤ 105877234134857 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1028 c22250R_63_19 (by norm_num)

theorem c22250R_63_17 : rowsJ2 63 64 38 360 ≤ 105877234134857 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1027 c22250R_63_18 (by norm_num)

theorem c22250R_63_16 : rowsJ2 63 64 37 360 ≤ 105877234134857 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1026 c22250R_63_17 (by norm_num)

theorem c22250R_63_15 : rowsJ2 63 64 36 360 ≤ 105877234134857 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1025 c22250R_63_16 (by norm_num)

theorem c22250R_63_14 : rowsJ2 63 64 35 360 ≤ 105877234134857 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1024 c22250R_63_15 (by norm_num)

theorem c22250R_63_13 : rowsJ2 63 64 34 360 ≤ 105877234134857 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1023 c22250R_63_14 (by norm_num)

theorem c22250R_63_12 : rowsJ2 63 64 33 360 ≤ 105877234134857 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1022 c22250R_63_13 (by norm_num)

theorem c22250R_63_11 : rowsJ2 63 64 32 360 ≤ 105877234134857 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1021 c22250R_63_12 (by norm_num)

theorem c22250R_63_10 : rowsJ2 63 64 31 360 ≤ 105877234134857 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1020 c22250R_63_11 (by norm_num)

theorem c22250R_63_9 : rowsJ2 63 64 30 360 ≤ 105877234134857 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1019 c22250R_63_10 (by norm_num)

theorem c22250R_63_8 : rowsJ2 63 64 29 360 ≤ 105877234134857 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1018 c22250R_63_9 (by norm_num)

theorem c22250R_63_7 : rowsJ2 63 64 28 360 ≤ 105877234134857 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1017 c22250R_63_8 (by norm_num)

theorem c22250R_63_6 : rowsJ2 63 64 27 360 ≤ 105880469627007 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1016 c22250R_63_7 (by norm_num)

theorem c22250R_63_5 : rowsJ2 63 64 26 360 ≤ 105886961449260 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1015 c22250R_63_6 (by norm_num)

theorem c22250R_63_4 : rowsJ2 63 64 25 360 ≤ 105899926300944 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1014 c22250R_63_5 (by norm_num)

theorem c22250R_63_3 : rowsJ2 63 64 24 360 ≤ 105919415829416 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1013 c22250R_63_4 (by norm_num)

theorem c22250R_63_2 : rowsJ2 63 64 22 360 ≤ 105987701442602 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1012 c22250R_63_3 (by norm_num)

theorem c22250R_63_1 : rowsJ2 63 64 17 360 ≤ 106403727839596 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1011 c22250R_63_2 (by norm_num)

theorem c22250R_63_0 : rowsJ2 63 64 0 360 ≤ 108404179492160 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22250R_1010 c22250R_63_1 (by norm_num)

theorem hr22250R_63 : rows2 63 64 ≤ 108404179492160 := rows2_le_of_rowsJ2 63 64 c22250R_63_0

theorem c22250R_64_42 : rowsJ2 64 65 63 360 ≤ 25178469082413 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1095 rows22250R_1096 (by norm_num)

theorem c22250R_64_41 : rowsJ2 64 65 62 360 ≤ 37456716111243 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1094 c22250R_64_42 (by norm_num)

theorem c22250R_64_40 : rowsJ2 64 65 61 360 ≤ 49090863225949 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1093 c22250R_64_41 (by norm_num)

theorem c22250R_64_39 : rowsJ2 64 65 60 360 ≤ 59930017991075 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1092 c22250R_64_40 (by norm_num)

theorem c22250R_64_38 : rowsJ2 64 65 59 360 ≤ 69787428228878 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1091 c22250R_64_39 (by norm_num)

theorem c22250R_64_37 : rowsJ2 64 65 58 360 ≤ 78746665708547 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1090 c22250R_64_38 (by norm_num)

theorem c22250R_64_36 : rowsJ2 64 65 57 360 ≤ 86739036640720 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1089 c22250R_64_37 (by norm_num)

theorem c22250R_64_35 : rowsJ2 64 65 56 360 ≤ 93620967255500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1088 c22250R_64_36 (by norm_num)

theorem c22250R_64_34 : rowsJ2 64 65 55 360 ≤ 99267564061987 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1087 c22250R_64_35 (by norm_num)

theorem c22250R_64_33 : rowsJ2 64 65 54 360 ≤ 103840369773028 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1086 c22250R_64_34 (by norm_num)

theorem c22250R_64_32 : rowsJ2 64 65 53 360 ≤ 107522149939504 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1085 c22250R_64_33 (by norm_num)

theorem c22250R_64_31 : rowsJ2 64 65 52 360 ≤ 110332500290778 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1084 c22250R_64_32 (by norm_num)

theorem c22250R_64_30 : rowsJ2 64 65 51 360 ≤ 112293380549446 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1083 c22250R_64_31 (by norm_num)

theorem c22250R_64_29 : rowsJ2 64 65 50 360 ≤ 113655579051394 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1082 c22250R_64_30 (by norm_num)

theorem c22250R_64_28 : rowsJ2 64 65 49 360 ≤ 114561278338994 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1081 c22250R_64_29 (by norm_num)

theorem c22250R_64_27 : rowsJ2 64 65 48 360 ≤ 115047656292163 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1080 c22250R_64_28 (by norm_num)

theorem c22250R_64_26 : rowsJ2 64 65 47 360 ≤ 115156178253500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1079 c22250R_64_27 (by norm_num)

theorem c22250R_64_25 : rowsJ2 64 65 46 360 ≤ 115156178253500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1078 c22250R_64_26 (by norm_num)

theorem c22250R_64_24 : rowsJ2 64 65 45 360 ≤ 115156178253500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1077 c22250R_64_25 (by norm_num)

theorem c22250R_64_23 : rowsJ2 64 65 44 360 ≤ 115156178253500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1076 c22250R_64_24 (by norm_num)

theorem c22250R_64_22 : rowsJ2 64 65 43 360 ≤ 115156178253500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1075 c22250R_64_23 (by norm_num)

theorem c22250R_64_21 : rowsJ2 64 65 42 360 ≤ 115156178253500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1074 c22250R_64_22 (by norm_num)

theorem c22250R_64_20 : rowsJ2 64 65 41 360 ≤ 115156178253500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1073 c22250R_64_21 (by norm_num)

theorem c22250R_64_19 : rowsJ2 64 65 40 360 ≤ 115156178253500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1072 c22250R_64_20 (by norm_num)

theorem c22250R_64_18 : rowsJ2 64 65 39 360 ≤ 115156178253500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1071 c22250R_64_19 (by norm_num)

theorem c22250R_64_17 : rowsJ2 64 65 38 360 ≤ 115156178253500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1070 c22250R_64_18 (by norm_num)

theorem c22250R_64_16 : rowsJ2 64 65 37 360 ≤ 115156178253500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1069 c22250R_64_17 (by norm_num)

theorem c22250R_64_15 : rowsJ2 64 65 36 360 ≤ 115156178253500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1068 c22250R_64_16 (by norm_num)

theorem c22250R_64_14 : rowsJ2 64 65 35 360 ≤ 115156178253500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1067 c22250R_64_15 (by norm_num)

theorem c22250R_64_13 : rowsJ2 64 65 34 360 ≤ 115156178253500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1066 c22250R_64_14 (by norm_num)

theorem c22250R_64_12 : rowsJ2 64 65 33 360 ≤ 115156178253500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1065 c22250R_64_13 (by norm_num)

theorem c22250R_64_11 : rowsJ2 64 65 32 360 ≤ 115156178253500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1064 c22250R_64_12 (by norm_num)

theorem c22250R_64_10 : rowsJ2 64 65 31 360 ≤ 115156178253500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1063 c22250R_64_11 (by norm_num)

theorem c22250R_64_9 : rowsJ2 64 65 30 360 ≤ 115156178253500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1062 c22250R_64_10 (by norm_num)

theorem c22250R_64_8 : rowsJ2 64 65 29 360 ≤ 115156178253500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1061 c22250R_64_9 (by norm_num)

theorem c22250R_64_7 : rowsJ2 64 65 28 360 ≤ 115156178253500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1060 c22250R_64_8 (by norm_num)

theorem c22250R_64_6 : rowsJ2 64 65 27 360 ≤ 115156178253500 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1059 c22250R_64_7 (by norm_num)

theorem c22250R_64_5 : rowsJ2 64 65 26 360 ≤ 115159427624153 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1058 c22250R_64_6 (by norm_num)

theorem c22250R_64_4 : rowsJ2 64 65 25 360 ≤ 115165948427746 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1057 c22250R_64_5 (by norm_num)

theorem c22250R_64_3 : rowsJ2 64 65 24 360 ≤ 115178973486257 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1056 c22250R_64_4 (by norm_num)

theorem c22250R_64_2 : rowsJ2 64 65 22 360 ≤ 115227931248983 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1055 c22250R_64_3 (by norm_num)

theorem c22250R_64_1 : rowsJ2 64 65 17 360 ≤ 115566546394944 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1054 c22250R_64_2 (by norm_num)

theorem c22250R_64_0 : rowsJ2 64 65 0 360 ≤ 117443354054041 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22250R_1053 c22250R_64_1 (by norm_num)

theorem hr22250R_64 : rows2 64 65 ≤ 117443354054041 := rows2_le_of_rowsJ2 64 65 c22250R_64_0

theorem c22250R_65_43 : rowsJ2 65 66 64 360 ≤ 21864771255252 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1140 rows22250R_1141 (by norm_num)

theorem c22250R_65_42 : rowsJ2 65 66 63 360 ≤ 33569580420269 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1139 c22250R_65_43 (by norm_num)

theorem c22250R_65_41 : rowsJ2 65 66 62 360 ≤ 45280386909115 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1138 c22250R_65_42 (by norm_num)

theorem c22250R_65_40 : rowsJ2 65 66 61 360 ≤ 56441041233823 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1137 c22250R_65_41 (by norm_num)

theorem c22250R_65_39 : rowsJ2 65 66 60 360 ≤ 66860559379965 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1136 c22250R_65_40 (by norm_num)

theorem c22250R_65_38 : rowsJ2 65 66 59 360 ≤ 76390948922678 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1135 c22250R_65_39 (by norm_num)

theorem c22250R_65_37 : rowsJ2 65 66 58 360 ≤ 85074358892778 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1134 c22250R_65_38 (by norm_num)

theorem c22250R_65_36 : rowsJ2 65 66 57 360 ≤ 92879676868773 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1133 c22250R_65_37 (by norm_num)

theorem c22250R_65_35 : rowsJ2 65 66 56 360 ≤ 99624529997960 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1132 c22250R_65_36 (by norm_num)

theorem c22250R_65_34 : rowsJ2 65 66 55 360 ≤ 105221939882656 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1131 c22250R_65_35 (by norm_num)

theorem c22250R_65_33 : rowsJ2 65 66 54 360 ≤ 109754912355278 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1130 c22250R_65_34 (by norm_num)

theorem c22250R_65_32 : rowsJ2 65 66 53 360 ≤ 113404620914857 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1129 c22250R_65_33 (by norm_num)

theorem c22250R_65_31 : rowsJ2 65 66 52 360 ≤ 116190490594386 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1128 c22250R_65_32 (by norm_num)

theorem c22250R_65_30 : rowsJ2 65 66 51 360 ≤ 118134289827575 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1127 c22250R_65_31 (by norm_num)

theorem c22250R_65_29 : rowsJ2 65 66 50 360 ≤ 119484622359012 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1126 c22250R_65_30 (by norm_num)

theorem c22250R_65_28 : rowsJ2 65 66 49 360 ≤ 120382432193625 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1125 c22250R_65_29 (by norm_num)

theorem c22250R_65_27 : rowsJ2 65 66 48 360 ≤ 120864573358662 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1124 c22250R_65_28 (by norm_num)

theorem c22250R_65_26 : rowsJ2 65 66 47 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1123 c22250R_65_27 (by norm_num)

theorem c22250R_65_25 : rowsJ2 65 66 46 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1122 c22250R_65_26 (by norm_num)

theorem c22250R_65_24 : rowsJ2 65 66 45 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1121 c22250R_65_25 (by norm_num)

theorem c22250R_65_23 : rowsJ2 65 66 44 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1120 c22250R_65_24 (by norm_num)

theorem c22250R_65_22 : rowsJ2 65 66 43 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1119 c22250R_65_23 (by norm_num)

theorem c22250R_65_21 : rowsJ2 65 66 42 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1118 c22250R_65_22 (by norm_num)

theorem c22250R_65_20 : rowsJ2 65 66 41 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1117 c22250R_65_21 (by norm_num)

theorem c22250R_65_19 : rowsJ2 65 66 40 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1116 c22250R_65_20 (by norm_num)

theorem c22250R_65_18 : rowsJ2 65 66 39 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1115 c22250R_65_19 (by norm_num)

theorem c22250R_65_17 : rowsJ2 65 66 38 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1114 c22250R_65_18 (by norm_num)

theorem c22250R_65_16 : rowsJ2 65 66 37 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1113 c22250R_65_17 (by norm_num)

theorem c22250R_65_15 : rowsJ2 65 66 36 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1112 c22250R_65_16 (by norm_num)

theorem c22250R_65_14 : rowsJ2 65 66 35 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1111 c22250R_65_15 (by norm_num)

theorem c22250R_65_13 : rowsJ2 65 66 34 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1110 c22250R_65_14 (by norm_num)

theorem c22250R_65_12 : rowsJ2 65 66 33 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1109 c22250R_65_13 (by norm_num)

theorem c22250R_65_11 : rowsJ2 65 66 32 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1108 c22250R_65_12 (by norm_num)

theorem c22250R_65_10 : rowsJ2 65 66 31 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1107 c22250R_65_11 (by norm_num)

theorem c22250R_65_9 : rowsJ2 65 66 30 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1106 c22250R_65_10 (by norm_num)

theorem c22250R_65_8 : rowsJ2 65 66 29 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1105 c22250R_65_9 (by norm_num)

theorem c22250R_65_7 : rowsJ2 65 66 28 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1104 c22250R_65_8 (by norm_num)

theorem c22250R_65_6 : rowsJ2 65 66 27 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1103 c22250R_65_7 (by norm_num)

theorem c22250R_65_5 : rowsJ2 65 66 26 360 ≤ 120972149996398 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1102 c22250R_65_6 (by norm_num)

theorem c22250R_65_4 : rowsJ2 65 66 25 360 ≤ 120975414125218 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1101 c22250R_65_5 (by norm_num)

theorem c22250R_65_3 : rowsJ2 65 66 24 360 ≤ 120981965716353 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1100 c22250R_65_4 (by norm_num)

theorem c22250R_65_2 : rowsJ2 65 66 22 360 ≤ 121014738096167 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1099 c22250R_65_3 (by norm_num)

theorem c22250R_65_1 : rowsJ2 65 66 18 360 ≤ 121202510249988 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1098 c22250R_65_2 (by norm_num)

theorem c22250R_65_0 : rowsJ2 65 66 0 360 ≤ 123035634227695 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22250R_1097 c22250R_65_1 (by norm_num)

theorem hr22250R_65 : rows2 65 66 ≤ 123035634227695 := rows2_le_of_rowsJ2 65 66 c22250R_65_0

theorem c22250R_66_44 : rowsJ2 66 67 65 360 ≤ 18818229237008 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1186 rows22250R_1187 (by norm_num)

theorem c22250R_66_43 : rowsJ2 66 67 64 360 ≤ 28981869969339 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1185 c22250R_66_44 (by norm_num)

theorem c22250R_66_42 : rowsJ2 66 67 63 360 ≤ 39612590936275 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1184 c22250R_66_43 (by norm_num)

theorem c22250R_66_41 : rowsJ2 66 67 62 360 ≤ 50756155026810 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1183 c22250R_66_42 (by norm_num)

theorem c22250R_66_40 : rowsJ2 66 67 61 360 ≤ 61404183542593 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1182 c22250R_66_41 (by norm_num)

theorem c22250R_66_39 : rowsJ2 66 67 60 360 ≤ 71404712174779 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1181 c22250R_66_40 (by norm_num)

theorem c22250R_66_38 : rowsJ2 66 67 59 360 ≤ 80569687308854 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1180 c22250R_66_39 (by norm_num)

theorem c22250R_66_37 : rowsJ2 66 67 58 360 ≤ 88978122354747 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1179 c22250R_66_38 (by norm_num)

theorem c22250R_66_36 : rowsJ2 66 67 57 360 ≤ 96558528863384 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1178 c22250R_66_37 (by norm_num)

theorem c22250R_66_35 : rowsJ2 66 67 56 360 ≤ 103167184346650 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1177 c22250R_66_36 (by norm_num)

theorem c22250R_66_34 : rowsJ2 66 67 55 360 ≤ 108677846992581 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1176 c22250R_66_35 (by norm_num)

theorem c22250R_66_33 : rowsJ2 66 67 54 360 ≤ 113171674200373 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1175 c22250R_66_34 (by norm_num)

theorem c22250R_66_32 : rowsJ2 66 67 53 360 ≤ 116789865072832 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1174 c22250R_66_33 (by norm_num)

theorem c22250R_66_31 : rowsJ2 66 67 52 360 ≤ 119551676894729 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1173 c22250R_66_32 (by norm_num)

theorem c22250R_66_30 : rowsJ2 66 67 51 360 ≤ 121478690114718 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1172 c22250R_66_31 (by norm_num)

theorem c22250R_66_29 : rowsJ2 66 67 50 360 ≤ 122817361616915 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1171 c22250R_66_30 (by norm_num)

theorem c22250R_66_28 : rowsJ2 66 67 49 360 ≤ 123707418260006 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1170 c22250R_66_29 (by norm_num)

theorem c22250R_66_27 : rowsJ2 66 67 48 360 ≤ 124185395811937 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1169 c22250R_66_28 (by norm_num)

theorem c22250R_66_26 : rowsJ2 66 67 47 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1168 c22250R_66_27 (by norm_num)

theorem c22250R_66_25 : rowsJ2 66 67 46 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1167 c22250R_66_26 (by norm_num)

theorem c22250R_66_24 : rowsJ2 66 67 45 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1166 c22250R_66_25 (by norm_num)

theorem c22250R_66_23 : rowsJ2 66 67 44 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1165 c22250R_66_24 (by norm_num)

theorem c22250R_66_22 : rowsJ2 66 67 43 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1164 c22250R_66_23 (by norm_num)

theorem c22250R_66_21 : rowsJ2 66 67 42 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1163 c22250R_66_22 (by norm_num)

theorem c22250R_66_20 : rowsJ2 66 67 41 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1162 c22250R_66_21 (by norm_num)

theorem c22250R_66_19 : rowsJ2 66 67 40 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1161 c22250R_66_20 (by norm_num)

theorem c22250R_66_18 : rowsJ2 66 67 39 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1160 c22250R_66_19 (by norm_num)

theorem c22250R_66_17 : rowsJ2 66 67 38 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1159 c22250R_66_18 (by norm_num)

theorem c22250R_66_16 : rowsJ2 66 67 37 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1158 c22250R_66_17 (by norm_num)

theorem c22250R_66_15 : rowsJ2 66 67 36 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1157 c22250R_66_16 (by norm_num)

theorem c22250R_66_14 : rowsJ2 66 67 35 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1156 c22250R_66_15 (by norm_num)

theorem c22250R_66_13 : rowsJ2 66 67 34 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1155 c22250R_66_14 (by norm_num)

theorem c22250R_66_12 : rowsJ2 66 67 33 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1154 c22250R_66_13 (by norm_num)

theorem c22250R_66_11 : rowsJ2 66 67 32 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1153 c22250R_66_12 (by norm_num)

theorem c22250R_66_10 : rowsJ2 66 67 31 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1152 c22250R_66_11 (by norm_num)

theorem c22250R_66_9 : rowsJ2 66 67 30 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1151 c22250R_66_10 (by norm_num)

theorem c22250R_66_8 : rowsJ2 66 67 29 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1150 c22250R_66_9 (by norm_num)

theorem c22250R_66_7 : rowsJ2 66 67 28 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1149 c22250R_66_8 (by norm_num)

theorem c22250R_66_6 : rowsJ2 66 67 27 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1148 c22250R_66_7 (by norm_num)

theorem c22250R_66_5 : rowsJ2 66 67 26 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1147 c22250R_66_6 (by norm_num)

theorem c22250R_66_4 : rowsJ2 66 67 25 360 ≤ 124292043453082 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1146 c22250R_66_5 (by norm_num)

theorem c22250R_66_3 : rowsJ2 66 67 24 360 ≤ 124295323242139 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1145 c22250R_66_4 (by norm_num)

theorem c22250R_66_2 : rowsJ2 66 67 22 360 ≤ 124315064127815 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1144 c22250R_66_3 (by norm_num)

theorem c22250R_66_1 : rowsJ2 66 67 18 360 ≤ 124457262817571 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1143 c22250R_66_2 (by norm_num)

theorem c22250R_66_0 : rowsJ2 66 67 0 360 ≤ 126147913812543 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22250R_1142 c22250R_66_1 (by norm_num)

theorem hr22250R_66 : rows2 66 67 ≤ 126147913812543 := rows2_le_of_rowsJ2 66 67 c22250R_66_0

theorem c22250R_67_45 : rowsJ2 67 68 66 360 ≤ 16089337176514 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1233 rows22250R_1234 (by norm_num)

theorem c22250R_67_44 : rowsJ2 67 68 65 360 ≤ 24814594624500 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1232 c22250R_67_45 (by norm_num)

theorem c22250R_67_43 : rowsJ2 67 68 64 360 ≤ 34013637306543 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1231 c22250R_67_44 (by norm_num)

theorem c22250R_67_42 : rowsJ2 67 68 63 360 ≤ 43676174283769 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1230 c22250R_67_43 (by norm_num)

theorem c22250R_67_41 : rowsJ2 67 68 62 360 ≤ 53807315117290 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1229 c22250R_67_42 (by norm_num)

theorem c22250R_67_40 : rowsJ2 67 68 61 360 ≤ 63942864319319 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1228 c22250R_67_41 (by norm_num)

theorem c22250R_67_39 : rowsJ2 67 68 60 360 ≤ 73485174863793 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1227 c22250R_67_40 (by norm_num)

theorem c22250R_67_38 : rowsJ2 67 68 59 360 ≤ 82285277127491 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1226 c22250R_67_39 (by norm_num)

theorem c22250R_67_37 : rowsJ2 67 68 58 360 ≤ 90380226396010 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1225 c22250R_67_38 (by norm_num)

theorem c22250R_67_36 : rowsJ2 67 68 57 360 ≤ 97736473583508 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1224 c22250R_67_37 (by norm_num)

theorem c22250R_67_35 : rowsJ2 67 68 56 360 ≤ 104170923391493 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1223 c22250R_67_36 (by norm_num)

theorem c22250R_67_34 : rowsJ2 67 68 55 360 ≤ 109595586931518 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1222 c22250R_67_35 (by norm_num)

theorem c22250R_67_33 : rowsJ2 67 68 54 360 ≤ 114050939177324 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1221 c22250R_67_34 (by norm_num)

theorem c22250R_67_32 : rowsJ2 67 68 53 360 ≤ 117638152054890 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1220 c22250R_67_33 (by norm_num)

theorem c22250R_67_31 : rowsJ2 67 68 52 360 ≤ 120376317973205 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1219 c22250R_67_32 (by norm_num)

theorem c22250R_67_30 : rowsJ2 67 68 51 360 ≤ 122286832614823 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1218 c22250R_67_31 (by norm_num)

theorem c22250R_67_29 : rowsJ2 67 68 50 360 ≤ 123614042765085 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1217 c22250R_67_30 (by norm_num)

theorem c22250R_67_28 : rowsJ2 67 68 49 360 ≤ 124496478978212 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1216 c22250R_67_29 (by norm_num)

theorem c22250R_67_27 : rowsJ2 67 68 48 360 ≤ 124970364212552 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1215 c22250R_67_28 (by norm_num)

theorem c22250R_67_26 : rowsJ2 67 68 47 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1214 c22250R_67_27 (by norm_num)

theorem c22250R_67_25 : rowsJ2 67 68 46 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1213 c22250R_67_26 (by norm_num)

theorem c22250R_67_24 : rowsJ2 67 68 45 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1212 c22250R_67_25 (by norm_num)

theorem c22250R_67_23 : rowsJ2 67 68 44 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1211 c22250R_67_24 (by norm_num)

theorem c22250R_67_22 : rowsJ2 67 68 43 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1210 c22250R_67_23 (by norm_num)

theorem c22250R_67_21 : rowsJ2 67 68 42 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1209 c22250R_67_22 (by norm_num)

theorem c22250R_67_20 : rowsJ2 67 68 41 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1208 c22250R_67_21 (by norm_num)

theorem c22250R_67_19 : rowsJ2 67 68 40 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1207 c22250R_67_20 (by norm_num)

theorem c22250R_67_18 : rowsJ2 67 68 39 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1206 c22250R_67_19 (by norm_num)

theorem c22250R_67_17 : rowsJ2 67 68 38 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1205 c22250R_67_18 (by norm_num)

theorem c22250R_67_16 : rowsJ2 67 68 37 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1204 c22250R_67_17 (by norm_num)

theorem c22250R_67_15 : rowsJ2 67 68 36 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1203 c22250R_67_16 (by norm_num)

theorem c22250R_67_14 : rowsJ2 67 68 35 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1202 c22250R_67_15 (by norm_num)

theorem c22250R_67_13 : rowsJ2 67 68 34 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1201 c22250R_67_14 (by norm_num)

theorem c22250R_67_12 : rowsJ2 67 68 33 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1200 c22250R_67_13 (by norm_num)

theorem c22250R_67_11 : rowsJ2 67 68 32 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1199 c22250R_67_12 (by norm_num)

theorem c22250R_67_10 : rowsJ2 67 68 31 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1198 c22250R_67_11 (by norm_num)

theorem c22250R_67_9 : rowsJ2 67 68 30 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1197 c22250R_67_10 (by norm_num)

theorem c22250R_67_8 : rowsJ2 67 68 29 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1196 c22250R_67_9 (by norm_num)

theorem c22250R_67_7 : rowsJ2 67 68 28 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1195 c22250R_67_8 (by norm_num)

theorem c22250R_67_6 : rowsJ2 67 68 27 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1194 c22250R_67_7 (by norm_num)

theorem c22250R_67_5 : rowsJ2 67 68 26 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1193 c22250R_67_6 (by norm_num)

theorem c22250R_67_4 : rowsJ2 67 68 25 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1192 c22250R_67_5 (by norm_num)

theorem c22250R_67_3 : rowsJ2 67 68 24 360 ≤ 125076098764753 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1191 c22250R_67_4 (by norm_num)

theorem c22250R_67_2 : rowsJ2 67 68 22 360 ≤ 125086013919121 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1190 c22250R_67_3 (by norm_num)

theorem c22250R_67_1 : rowsJ2 67 68 18 360 ≤ 125188956476040 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1189 c22250R_67_2 (by norm_num)

theorem c22250R_67_0 : rowsJ2 67 68 0 360 ≤ 126741137544706 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22250R_1188 c22250R_67_1 (by norm_num)

theorem hr22250R_67 : rows2 67 68 ≤ 126741137544706 := rows2_le_of_rowsJ2 67 68 c22250R_67_0

theorem c22250R_68_47 : rowsJ2 68 69 67 360 ≤ 13561419075860 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1282 rows22250R_1283 (by norm_num)

theorem c22250R_68_46 : rowsJ2 68 69 66 360 ≤ 20949833979125 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1281 c22250R_68_47 (by norm_num)

theorem c22250R_68_45 : rowsJ2 68 69 65 360 ≤ 28762781122287 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1280 c22250R_68_46 (by norm_num)

theorem c22250R_68_44 : rowsJ2 68 69 64 360 ≤ 37046070187516 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1279 c22250R_68_45 (by norm_num)

theorem c22250R_68_43 : rowsJ2 68 69 63 360 ≤ 45748737534772 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1278 c22250R_68_44 (by norm_num)

theorem c22250R_68_42 : rowsJ2 68 69 62 360 ≤ 54916374970484 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1277 c22250R_68_43 (by norm_num)

theorem c22250R_68_41 : rowsJ2 68 69 61 360 ≤ 64499180436704 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1276 c22250R_68_42 (by norm_num)

theorem c22250R_68_40 : rowsJ2 68 69 60 360 ≤ 73583368743409 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1275 c22250R_68_41 (by norm_num)

theorem c22250R_68_39 : rowsJ2 68 69 59 360 ≤ 81979270274652 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1274 c22250R_68_40 (by norm_num)

theorem c22250R_68_38 : rowsJ2 68 69 58 360 ≤ 89761206214803 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1273 c22250R_68_39 (by norm_num)

theorem c22250R_68_37 : rowsJ2 68 69 57 360 ≤ 96854679176942 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1272 c22250R_68_38 (by norm_num)

theorem c22250R_68_36 : rowsJ2 68 69 56 360 ≤ 103115578141516 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1271 c22250R_68_37 (by norm_num)

theorem c22250R_68_35 : rowsJ2 68 69 55 360 ≤ 108416090679930 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1270 c22250R_68_36 (by norm_num)

theorem c22250R_68_34 : rowsJ2 68 69 54 360 ≤ 112833621195878 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1269 c22250R_68_35 (by norm_num)

theorem c22250R_68_33 : rowsJ2 68 69 53 360 ≤ 116390382026354 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1268 c22250R_68_34 (by norm_num)

theorem c22250R_68_32 : rowsJ2 68 69 52 360 ≤ 119105303503835 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1267 c22250R_68_33 (by norm_num)

theorem c22250R_68_31 : rowsJ2 68 69 51 360 ≤ 120999599681747 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1266 c22250R_68_32 (by norm_num)

theorem c22250R_68_30 : rowsJ2 68 69 50 360 ≤ 122315543072167 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1265 c22250R_68_31 (by norm_num)

theorem c22250R_68_29 : rowsJ2 68 69 49 360 ≤ 123190488235827 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1264 c22250R_68_30 (by norm_num)

theorem c22250R_68_28 : rowsJ2 68 69 48 360 ≤ 123660350632390 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1263 c22250R_68_29 (by norm_num)

theorem c22250R_68_27 : rowsJ2 68 69 47 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1262 c22250R_68_28 (by norm_num)

theorem c22250R_68_26 : rowsJ2 68 69 46 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1261 c22250R_68_27 (by norm_num)

theorem c22250R_68_25 : rowsJ2 68 69 45 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1260 c22250R_68_26 (by norm_num)

theorem c22250R_68_24 : rowsJ2 68 69 44 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1259 c22250R_68_25 (by norm_num)

theorem c22250R_68_23 : rowsJ2 68 69 43 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1258 c22250R_68_24 (by norm_num)

theorem c22250R_68_22 : rowsJ2 68 69 42 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1257 c22250R_68_23 (by norm_num)

theorem c22250R_68_21 : rowsJ2 68 69 41 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1256 c22250R_68_22 (by norm_num)

theorem c22250R_68_20 : rowsJ2 68 69 40 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1255 c22250R_68_21 (by norm_num)

theorem c22250R_68_19 : rowsJ2 68 69 39 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1254 c22250R_68_20 (by norm_num)

theorem c22250R_68_18 : rowsJ2 68 69 38 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1253 c22250R_68_19 (by norm_num)

theorem c22250R_68_17 : rowsJ2 68 69 37 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1252 c22250R_68_18 (by norm_num)

theorem c22250R_68_16 : rowsJ2 68 69 36 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1251 c22250R_68_17 (by norm_num)

theorem c22250R_68_15 : rowsJ2 68 69 35 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1250 c22250R_68_16 (by norm_num)

theorem c22250R_68_14 : rowsJ2 68 69 34 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1249 c22250R_68_15 (by norm_num)

theorem c22250R_68_13 : rowsJ2 68 69 33 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1248 c22250R_68_14 (by norm_num)

theorem c22250R_68_12 : rowsJ2 68 69 32 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1247 c22250R_68_13 (by norm_num)

theorem c22250R_68_11 : rowsJ2 68 69 31 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1246 c22250R_68_12 (by norm_num)

theorem c22250R_68_10 : rowsJ2 68 69 30 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1245 c22250R_68_11 (by norm_num)

theorem c22250R_68_9 : rowsJ2 68 69 29 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1244 c22250R_68_10 (by norm_num)

theorem c22250R_68_8 : rowsJ2 68 69 28 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1243 c22250R_68_9 (by norm_num)

theorem c22250R_68_7 : rowsJ2 68 69 27 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1242 c22250R_68_8 (by norm_num)

theorem c22250R_68_6 : rowsJ2 68 69 26 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1241 c22250R_68_7 (by norm_num)

theorem c22250R_68_5 : rowsJ2 68 69 25 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1240 c22250R_68_6 (by norm_num)

theorem c22250R_68_4 : rowsJ2 68 69 24 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1239 c22250R_68_5 (by norm_num)

theorem c22250R_68_3 : rowsJ2 68 69 23 360 ≤ 123765187598172 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1238 c22250R_68_4 (by norm_num)

theorem c22250R_68_2 : rowsJ2 68 69 22 360 ≤ 123768501512106 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1237 c22250R_68_3 (by norm_num)

theorem c22250R_68_1 : rowsJ2 68 69 18 360 ≤ 123838530119181 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1236 c22250R_68_2 (by norm_num)

theorem c22250R_68_0 : rowsJ2 68 69 0 360 ≤ 125255471302531 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22250R_1235 c22250R_68_1 (by norm_num)

theorem hr22250R_68 : rows2 68 69 ≤ 125255471302531 := rows2_le_of_rowsJ2 68 69 c22250R_68_0

theorem c22250R_69_48 : rowsJ2 69 70 68 360 ≤ 11231740177155 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1332 rows22250R_1333 (by norm_num)

theorem c22250R_69_47 : rowsJ2 69 70 67 360 ≤ 17383347326870 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1331 c22250R_69_48 (by norm_num)

theorem c22250R_69_46 : rowsJ2 69 70 66 360 ≤ 23910903836423 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1330 c22250R_69_47 (by norm_num)

theorem c22250R_69_45 : rowsJ2 69 70 65 360 ≤ 30860149122944 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1329 c22250R_69_46 (by norm_num)

theorem c22250R_69_44 : rowsJ2 69 70 64 360 ≤ 38235223663946 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1328 c22250R_69_45 (by norm_num)

theorem c22250R_69_43 : rowsJ2 69 70 63 360 ≤ 46026660469783 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1327 c22250R_69_44 (by norm_num)

theorem c22250R_69_42 : rowsJ2 69 70 62 360 ≤ 54238888030977 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1326 c22250R_69_43 (by norm_num)

theorem c22250R_69_41 : rowsJ2 69 70 61 360 ≤ 62863063053707 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1325 c22250R_69_42 (by norm_num)

theorem c22250R_69_40 : rowsJ2 69 70 60 360 ≤ 71448821953678 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1324 c22250R_69_41 (by norm_num)

theorem c22250R_69_39 : rowsJ2 69 70 59 360 ≤ 79440569406235 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1323 c22250R_69_40 (by norm_num)

theorem c22250R_69_38 : rowsJ2 69 70 58 360 ≤ 86870093241166 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1322 c22250R_69_39 (by norm_num)

theorem c22250R_69_37 : rowsJ2 69 70 57 360 ≤ 93701213427664 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1321 c22250R_69_38 (by norm_num)

theorem c22250R_69_36 : rowsJ2 69 70 56 360 ≤ 99749838560488 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1320 c22250R_69_37 (by norm_num)

theorem c22250R_69_35 : rowsJ2 69 70 55 360 ≤ 104926768668290 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1319 c22250R_69_36 (by norm_num)

theorem c22250R_69_34 : rowsJ2 69 70 54 360 ≤ 109268210533423 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1318 c22250R_69_35 (by norm_num)

theorem c22250R_69_33 : rowsJ2 69 70 53 360 ≤ 112795031982959 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1317 c22250R_69_34 (by norm_num)

theorem c22250R_69_32 : rowsJ2 69 70 52 360 ≤ 115487100344303 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1316 c22250R_69_33 (by norm_num)

theorem c22250R_69_31 : rowsJ2 69 70 51 360 ≤ 117365451099519 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1315 c22250R_69_32 (by norm_num)

theorem c22250R_69_30 : rowsJ2 69 70 50 360 ≤ 118670317408193 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1314 c22250R_69_31 (by norm_num)

theorem c22250R_69_29 : rowsJ2 69 70 49 360 ≤ 119537897635663 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1313 c22250R_69_30 (by norm_num)

theorem c22250R_69_28 : rowsJ2 69 70 48 360 ≤ 120003804919709 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1312 c22250R_69_29 (by norm_num)

theorem c22250R_69_27 : rowsJ2 69 70 47 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1311 c22250R_69_28 (by norm_num)

theorem c22250R_69_26 : rowsJ2 69 70 46 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1310 c22250R_69_27 (by norm_num)

theorem c22250R_69_25 : rowsJ2 69 70 45 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1309 c22250R_69_26 (by norm_num)

theorem c22250R_69_24 : rowsJ2 69 70 44 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1308 c22250R_69_25 (by norm_num)

theorem c22250R_69_23 : rowsJ2 69 70 43 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1307 c22250R_69_24 (by norm_num)

theorem c22250R_69_22 : rowsJ2 69 70 42 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1306 c22250R_69_23 (by norm_num)

theorem c22250R_69_21 : rowsJ2 69 70 41 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1305 c22250R_69_22 (by norm_num)

theorem c22250R_69_20 : rowsJ2 69 70 40 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1304 c22250R_69_21 (by norm_num)

theorem c22250R_69_19 : rowsJ2 69 70 39 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1303 c22250R_69_20 (by norm_num)

theorem c22250R_69_18 : rowsJ2 69 70 38 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1302 c22250R_69_19 (by norm_num)

theorem c22250R_69_17 : rowsJ2 69 70 37 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1301 c22250R_69_18 (by norm_num)

theorem c22250R_69_16 : rowsJ2 69 70 36 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1300 c22250R_69_17 (by norm_num)

theorem c22250R_69_15 : rowsJ2 69 70 35 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1299 c22250R_69_16 (by norm_num)

theorem c22250R_69_14 : rowsJ2 69 70 34 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1298 c22250R_69_15 (by norm_num)

theorem c22250R_69_13 : rowsJ2 69 70 33 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1297 c22250R_69_14 (by norm_num)

theorem c22250R_69_12 : rowsJ2 69 70 32 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1296 c22250R_69_13 (by norm_num)

theorem c22250R_69_11 : rowsJ2 69 70 31 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1295 c22250R_69_12 (by norm_num)

theorem c22250R_69_10 : rowsJ2 69 70 30 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1294 c22250R_69_11 (by norm_num)

theorem c22250R_69_9 : rowsJ2 69 70 29 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1293 c22250R_69_10 (by norm_num)

theorem c22250R_69_8 : rowsJ2 69 70 28 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1292 c22250R_69_9 (by norm_num)

theorem c22250R_69_7 : rowsJ2 69 70 27 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1291 c22250R_69_8 (by norm_num)

theorem c22250R_69_6 : rowsJ2 69 70 26 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1290 c22250R_69_7 (by norm_num)

theorem c22250R_69_5 : rowsJ2 69 70 25 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1289 c22250R_69_6 (by norm_num)

theorem c22250R_69_4 : rowsJ2 69 70 24 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1288 c22250R_69_5 (by norm_num)

theorem c22250R_69_3 : rowsJ2 69 70 23 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1287 c22250R_69_4 (by norm_num)

theorem c22250R_69_2 : rowsJ2 69 70 22 360 ≤ 120107759410113 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1286 c22250R_69_3 (by norm_num)

theorem c22250R_69_1 : rowsJ2 69 70 18 360 ≤ 120151312135328 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1285 c22250R_69_2 (by norm_num)

theorem c22250R_69_0 : rowsJ2 69 70 0 360 ≤ 121434339852337 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22250R_1284 c22250R_69_1 (by norm_num)

theorem hr22250R_69 : rows2 69 70 ≤ 121434339852337 := rows2_le_of_rowsJ2 69 70 c22250R_69_0

theorem c22250R_70_49 : rowsJ2 70 71 69 360 ≤ 9097935937087 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1383 rows22250R_1384 (by norm_num)

theorem c22250R_70_48 : rowsJ2 70 71 68 360 ≤ 14111450739958 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1382 c22250R_70_49 (by norm_num)

theorem c22250R_70_47 : rowsJ2 70 71 67 360 ≤ 19452909428598 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1381 c22250R_70_48 (by norm_num)

theorem c22250R_70_46 : rowsJ2 70 71 66 360 ≤ 25168046309724 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1380 c22250R_70_47 (by norm_num)

theorem c22250R_70_45 : rowsJ2 70 71 65 360 ≤ 31260385948020 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1379 c22250R_70_46 (by norm_num)

theorem c22250R_70_44 : rowsJ2 70 71 64 360 ≤ 37775670023798 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1378 c22250R_70_45 (by norm_num)

theorem c22250R_70_43 : rowsJ2 70 71 63 360 ≤ 44663207681808 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1377 c22250R_70_44 (by norm_num)

theorem c22250R_70_42 : rowsJ2 70 71 62 360 ≤ 51968472088728 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1376 c22250R_70_43 (by norm_num)

theorem c22250R_70_41 : rowsJ2 70 71 61 360 ≤ 59641888540470 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1375 c22250R_70_42 (by norm_num)

theorem c22250R_70_40 : rowsJ2 70 71 60 360 ≤ 67728694609319 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1374 c22250R_70_41 (by norm_num)

theorem c22250R_70_39 : rowsJ2 70 71 59 360 ≤ 75275932210207 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1373 c22250R_70_40 (by norm_num)

theorem c22250R_70_38 : rowsJ2 70 71 58 360 ≤ 82353074229966 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1372 c22250R_70_39 (by norm_num)

theorem c22250R_70_37 : rowsJ2 70 71 57 360 ≤ 88882382444956 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1371 c22250R_70_38 (by norm_num)

theorem c22250R_70_36 : rowsJ2 70 71 56 360 ≤ 94719105679676 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1370 c22250R_70_37 (by norm_num)

theorem c22250R_70_35 : rowsJ2 70 71 55 360 ≤ 99733625992733 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1369 c22250R_70_36 (by norm_num)

theorem c22250R_70_34 : rowsJ2 70 71 54 360 ≤ 103999495259248 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1368 c22250R_70_35 (by norm_num)

theorem c22250R_70_33 : rowsJ2 70 71 53 360 ≤ 107496877155808 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1367 c22250R_70_34 (by norm_num)

theorem c22250R_70_32 : rowsJ2 70 71 52 360 ≤ 110166473926152 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1366 c22250R_70_33 (by norm_num)

theorem c22250R_70_31 : rowsJ2 70 71 51 360 ≤ 112029145462174 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1365 c22250R_70_32 (by norm_num)

theorem c22250R_70_30 : rowsJ2 70 71 50 360 ≤ 113323119617285 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1364 c22250R_70_31 (by norm_num)

theorem c22250R_70_29 : rowsJ2 70 71 49 360 ≤ 114183457863714 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1363 c22250R_70_30 (by norm_num)

theorem c22250R_70_28 : rowsJ2 70 71 48 360 ≤ 114645476064525 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1362 c22250R_70_29 (by norm_num)

theorem c22250R_70_27 : rowsJ2 70 71 47 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1361 c22250R_70_28 (by norm_num)

theorem c22250R_70_26 : rowsJ2 70 71 46 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1360 c22250R_70_27 (by norm_num)

theorem c22250R_70_25 : rowsJ2 70 71 45 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1359 c22250R_70_26 (by norm_num)

theorem c22250R_70_24 : rowsJ2 70 71 44 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1358 c22250R_70_25 (by norm_num)

theorem c22250R_70_23 : rowsJ2 70 71 43 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1357 c22250R_70_24 (by norm_num)

theorem c22250R_70_22 : rowsJ2 70 71 42 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1356 c22250R_70_23 (by norm_num)

theorem c22250R_70_21 : rowsJ2 70 71 41 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1355 c22250R_70_22 (by norm_num)

theorem c22250R_70_20 : rowsJ2 70 71 40 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1354 c22250R_70_21 (by norm_num)

theorem c22250R_70_19 : rowsJ2 70 71 39 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1353 c22250R_70_20 (by norm_num)

theorem c22250R_70_18 : rowsJ2 70 71 38 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1352 c22250R_70_19 (by norm_num)

theorem c22250R_70_17 : rowsJ2 70 71 37 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1351 c22250R_70_18 (by norm_num)

theorem c22250R_70_16 : rowsJ2 70 71 36 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1350 c22250R_70_17 (by norm_num)

theorem c22250R_70_15 : rowsJ2 70 71 35 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1349 c22250R_70_16 (by norm_num)

theorem c22250R_70_14 : rowsJ2 70 71 34 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1348 c22250R_70_15 (by norm_num)

theorem c22250R_70_13 : rowsJ2 70 71 33 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1347 c22250R_70_14 (by norm_num)

theorem c22250R_70_12 : rowsJ2 70 71 32 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1346 c22250R_70_13 (by norm_num)

theorem c22250R_70_11 : rowsJ2 70 71 31 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1345 c22250R_70_12 (by norm_num)

theorem c22250R_70_10 : rowsJ2 70 71 30 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1344 c22250R_70_11 (by norm_num)

theorem c22250R_70_9 : rowsJ2 70 71 29 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1343 c22250R_70_10 (by norm_num)

theorem c22250R_70_8 : rowsJ2 70 71 28 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1342 c22250R_70_9 (by norm_num)

theorem c22250R_70_7 : rowsJ2 70 71 27 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1341 c22250R_70_8 (by norm_num)

theorem c22250R_70_6 : rowsJ2 70 71 26 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1340 c22250R_70_7 (by norm_num)

theorem c22250R_70_5 : rowsJ2 70 71 25 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1339 c22250R_70_6 (by norm_num)

theorem c22250R_70_4 : rowsJ2 70 71 24 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1338 c22250R_70_5 (by norm_num)

theorem c22250R_70_3 : rowsJ2 70 71 23 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1337 c22250R_70_4 (by norm_num)

theorem c22250R_70_2 : rowsJ2 70 71 22 360 ≤ 114748562812184 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1336 c22250R_70_3 (by norm_num)

theorem c22250R_70_1 : rowsJ2 70 71 19 360 ≤ 114758649191207 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1335 c22250R_70_2 (by norm_num)

theorem c22250R_70_0 : rowsJ2 70 71 0 360 ≤ 115928348995584 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22250R_1334 c22250R_70_1 (by norm_num)

theorem hr22250R_70 : rows2 70 71 ≤ 115928348995584 := rows2_le_of_rowsJ2 70 71 c22250R_70_0

theorem c22250R_71_50 : rowsJ2 71 72 70 360 ≤ 7104903050911 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1435 rows22250R_1436 (by norm_num)

theorem c22250R_71_49 : rowsJ2 71 72 69 360 ≤ 11077906095685 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1434 c22250R_71_50 (by norm_num)

theorem c22250R_71_48 : rowsJ2 71 72 68 360 ≤ 15331333110869 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1433 c22250R_71_49 (by norm_num)

theorem c22250R_71_47 : rowsJ2 71 72 67 360 ≤ 19910978331980 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1432 c22250R_71_48 (by norm_num)

theorem c22250R_71_46 : rowsJ2 71 72 66 360 ≤ 24819788056908 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1431 c22250R_71_47 (by norm_num)

theorem c22250R_71_45 : rowsJ2 71 72 65 360 ≤ 30103488679165 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1430 c22250R_71_46 (by norm_num)

theorem c22250R_71_44 : rowsJ2 71 72 64 360 ≤ 35765591046553 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1429 c22250R_71_45 (by norm_num)

theorem c22250R_71_43 : rowsJ2 71 72 63 360 ≤ 41797473738423 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1428 c22250R_71_44 (by norm_num)

theorem c22250R_71_42 : rowsJ2 71 72 62 360 ≤ 48202905129065 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1427 c22250R_71_43 (by norm_num)

theorem c22250R_71_41 : rowsJ2 71 72 61 360 ≤ 54973822532587 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1426 c22250R_71_42 (by norm_num)

theorem c22250R_71_40 : rowsJ2 71 72 60 360 ≤ 62114251890827 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1425 c22250R_71_41 (by norm_num)

theorem c22250R_71_39 : rowsJ2 71 72 59 360 ≤ 69216464333525 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1424 c22250R_71_40 (by norm_num)

theorem c22250R_71_38 : rowsJ2 71 72 58 360 ≤ 75900844944166 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1423 c22250R_71_39 (by norm_num)

theorem c22250R_71_37 : rowsJ2 71 72 57 360 ≤ 82128370615140 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1422 c22250R_71_38 (by norm_num)

theorem c22250R_71_36 : rowsJ2 71 72 56 360 ≤ 87713666666294 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1421 c22250R_71_37 (by norm_num)

theorem c22250R_71_35 : rowsJ2 71 72 55 360 ≤ 92566108713144 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1420 c22250R_71_36 (by norm_num)

theorem c22250R_71_34 : rowsJ2 71 72 54 360 ≤ 96717499481994 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1419 c22250R_71_35 (by norm_num)

theorem c22250R_71_33 : rowsJ2 71 72 53 360 ≤ 100185929240458 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1418 c22250R_71_34 (by norm_num)

theorem c22250R_71_32 : rowsJ2 71 72 52 360 ≤ 102833426469879 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1417 c22250R_71_33 (by norm_num)

theorem c22250R_71_31 : rowsJ2 71 72 51 360 ≤ 104680678379125 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1416 c22250R_71_32 (by norm_num)

theorem c22250R_71_30 : rowsJ2 71 72 50 360 ≤ 105963940716215 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1415 c22250R_71_31 (by norm_num)

theorem c22250R_71_29 : rowsJ2 71 72 49 360 ≤ 106817156883202 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1414 c22250R_71_30 (by norm_num)

theorem c22250R_71_28 : rowsJ2 71 72 48 360 ≤ 107275350390244 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1413 c22250R_71_29 (by norm_num)

theorem c22250R_71_27 : rowsJ2 71 72 47 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1412 c22250R_71_28 (by norm_num)

theorem c22250R_71_26 : rowsJ2 71 72 46 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1411 c22250R_71_27 (by norm_num)

theorem c22250R_71_25 : rowsJ2 71 72 45 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1410 c22250R_71_26 (by norm_num)

theorem c22250R_71_24 : rowsJ2 71 72 44 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1409 c22250R_71_25 (by norm_num)

theorem c22250R_71_23 : rowsJ2 71 72 43 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1408 c22250R_71_24 (by norm_num)

theorem c22250R_71_22 : rowsJ2 71 72 42 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1407 c22250R_71_23 (by norm_num)

theorem c22250R_71_21 : rowsJ2 71 72 41 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1406 c22250R_71_22 (by norm_num)

theorem c22250R_71_20 : rowsJ2 71 72 40 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1405 c22250R_71_21 (by norm_num)

theorem c22250R_71_19 : rowsJ2 71 72 39 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1404 c22250R_71_20 (by norm_num)

theorem c22250R_71_18 : rowsJ2 71 72 38 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1403 c22250R_71_19 (by norm_num)

theorem c22250R_71_17 : rowsJ2 71 72 37 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1402 c22250R_71_18 (by norm_num)

theorem c22250R_71_16 : rowsJ2 71 72 36 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1401 c22250R_71_17 (by norm_num)

theorem c22250R_71_15 : rowsJ2 71 72 35 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1400 c22250R_71_16 (by norm_num)

theorem c22250R_71_14 : rowsJ2 71 72 34 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1399 c22250R_71_15 (by norm_num)

theorem c22250R_71_13 : rowsJ2 71 72 33 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1398 c22250R_71_14 (by norm_num)

theorem c22250R_71_12 : rowsJ2 71 72 32 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1397 c22250R_71_13 (by norm_num)

theorem c22250R_71_11 : rowsJ2 71 72 31 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1396 c22250R_71_12 (by norm_num)

theorem c22250R_71_10 : rowsJ2 71 72 30 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1395 c22250R_71_11 (by norm_num)

theorem c22250R_71_9 : rowsJ2 71 72 29 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1394 c22250R_71_10 (by norm_num)

theorem c22250R_71_8 : rowsJ2 71 72 28 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1393 c22250R_71_9 (by norm_num)

theorem c22250R_71_7 : rowsJ2 71 72 27 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1392 c22250R_71_8 (by norm_num)

theorem c22250R_71_6 : rowsJ2 71 72 26 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1391 c22250R_71_7 (by norm_num)

theorem c22250R_71_5 : rowsJ2 71 72 25 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1390 c22250R_71_6 (by norm_num)

theorem c22250R_71_4 : rowsJ2 71 72 24 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1389 c22250R_71_5 (by norm_num)

theorem c22250R_71_3 : rowsJ2 71 72 23 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1388 c22250R_71_4 (by norm_num)

theorem c22250R_71_2 : rowsJ2 71 72 22 360 ≤ 107377583761909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1387 c22250R_71_3 (by norm_num)

theorem c22250R_71_1 : rowsJ2 71 72 19 360 ≤ 107380956291770 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1386 c22250R_71_2 (by norm_num)

theorem c22250R_71_0 : rowsJ2 71 72 0 360 ≤ 108421635103138 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22250R_1385 c22250R_71_1 (by norm_num)

theorem hr22250R_71 : rows2 71 72 ≤ 108421635103138 := rows2_le_of_rowsJ2 71 72 c22250R_71_0

theorem c22250R_72_49 : rowsJ2 72 73 71 360 ≤ 5364141658354 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1486 rows22250R_1487 (by norm_num)

theorem c22250R_72_48 : rowsJ2 72 73 70 360 ≤ 8448881980495 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1485 c22250R_72_49 (by norm_num)

theorem c22250R_72_47 : rowsJ2 72 73 69 360 ≤ 11766826748021 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1484 c22250R_72_48 (by norm_num)

theorem c22250R_72_46 : rowsJ2 72 73 68 360 ≤ 15363904939488 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1483 c22250R_72_47 (by norm_num)

theorem c22250R_72_45 : rowsJ2 72 73 67 360 ≤ 19242530642643 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1482 c22250R_72_46 (by norm_num)

theorem c22250R_72_44 : rowsJ2 72 73 66 360 ≤ 23448489978291 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1481 c22250R_72_45 (by norm_num)

theorem c22250R_72_43 : rowsJ2 72 73 65 360 ≤ 27984714959774 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1480 c22250R_72_44 (by norm_num)

theorem c22250R_72_42 : rowsJ2 72 73 64 360 ≤ 32896942081496 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1479 c22250R_72_43 (by norm_num)

theorem c22250R_72_41 : rowsJ2 72 73 63 360 ≤ 38134752588788 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1478 c22250R_72_42 (by norm_num)

theorem c22250R_72_40 : rowsJ2 72 73 62 360 ≤ 43743563028573 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1477 c22250R_72_41 (by norm_num)

theorem c22250R_72_39 : rowsJ2 72 73 61 360 ≤ 49674026150522 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1476 c22250R_72_40 (by norm_num)

theorem c22250R_72_38 : rowsJ2 72 73 60 360 ≤ 55971271710045 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1475 c22250R_72_39 (by norm_num)

theorem c22250R_72_37 : rowsJ2 72 73 59 360 ≤ 62586976006129 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1474 c22250R_72_38 (by norm_num)

theorem c22250R_72_36 : rowsJ2 72 73 58 360 ≤ 68878117284642 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1473 c22250R_72_37 (by norm_num)

theorem c22250R_72_35 : rowsJ2 72 73 57 360 ≤ 74763464921134 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1472 c22250R_72_36 (by norm_num)

theorem c22250R_72_34 : rowsJ2 72 73 56 360 ≤ 80097362180308 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1471 c22250R_72_35 (by norm_num)

theorem c22250R_72_33 : rowsJ2 72 73 55 360 ≤ 84748136363597 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1470 c22250R_72_34 (by norm_num)

theorem c22250R_72_32 : rowsJ2 72 73 54 360 ≤ 88785370543576 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1469 c22250R_72_33 (by norm_num)

theorem c22250R_72_31 : rowsJ2 72 73 53 360 ≤ 92185879965926 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1468 c22250R_72_32 (by norm_num)

theorem c22250R_72_30 : rowsJ2 72 73 52 360 ≤ 94811640540614 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1467 c22250R_72_31 (by norm_num)

theorem c22250R_72_29 : rowsJ2 72 73 51 360 ≤ 96643726021539 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1466 c22250R_72_30 (by norm_num)

theorem c22250R_72_28 : rowsJ2 72 73 50 360 ≤ 97916452434345 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1465 c22250R_72_29 (by norm_num)

theorem c22250R_72_27 : rowsJ2 72 73 49 360 ≤ 98762663470211 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1464 c22250R_72_28 (by norm_num)

theorem c22250R_72_26 : rowsJ2 72 73 48 360 ≤ 99217095086983 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1463 c22250R_72_27 (by norm_num)

theorem c22250R_72_25 : rowsJ2 72 73 47 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1462 c22250R_72_26 (by norm_num)

theorem c22250R_72_24 : rowsJ2 72 73 46 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1461 c22250R_72_25 (by norm_num)

theorem c22250R_72_23 : rowsJ2 72 73 45 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1460 c22250R_72_24 (by norm_num)

theorem c22250R_72_22 : rowsJ2 72 73 44 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1459 c22250R_72_23 (by norm_num)

theorem c22250R_72_21 : rowsJ2 72 73 43 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1458 c22250R_72_22 (by norm_num)

theorem c22250R_72_20 : rowsJ2 72 73 42 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1457 c22250R_72_21 (by norm_num)

theorem c22250R_72_19 : rowsJ2 72 73 40 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1456 c22250R_72_20 (by norm_num)

theorem c22250R_72_18 : rowsJ2 72 73 38 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1455 c22250R_72_19 (by norm_num)

theorem c22250R_72_17 : rowsJ2 72 73 37 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1454 c22250R_72_18 (by norm_num)

theorem c22250R_72_16 : rowsJ2 72 73 36 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1453 c22250R_72_17 (by norm_num)

theorem c22250R_72_15 : rowsJ2 72 73 35 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1452 c22250R_72_16 (by norm_num)

theorem c22250R_72_14 : rowsJ2 72 73 34 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1451 c22250R_72_15 (by norm_num)

theorem c22250R_72_13 : rowsJ2 72 73 33 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1450 c22250R_72_14 (by norm_num)

theorem c22250R_72_12 : rowsJ2 72 73 32 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1449 c22250R_72_13 (by norm_num)

theorem c22250R_72_11 : rowsJ2 72 73 31 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1448 c22250R_72_12 (by norm_num)

theorem c22250R_72_10 : rowsJ2 72 73 30 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1447 c22250R_72_11 (by norm_num)

theorem c22250R_72_9 : rowsJ2 72 73 29 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1446 c22250R_72_10 (by norm_num)

theorem c22250R_72_8 : rowsJ2 72 73 28 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1445 c22250R_72_9 (by norm_num)

theorem c22250R_72_7 : rowsJ2 72 73 27 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1444 c22250R_72_8 (by norm_num)

theorem c22250R_72_6 : rowsJ2 72 73 26 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1443 c22250R_72_7 (by norm_num)

theorem c22250R_72_5 : rowsJ2 72 73 25 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1442 c22250R_72_6 (by norm_num)

theorem c22250R_72_4 : rowsJ2 72 73 24 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1441 c22250R_72_5 (by norm_num)

theorem c22250R_72_3 : rowsJ2 72 73 23 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1440 c22250R_72_4 (by norm_num)

theorem c22250R_72_2 : rowsJ2 72 73 22 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1439 c22250R_72_3 (by norm_num)

theorem c22250R_72_1 : rowsJ2 72 73 19 360 ≤ 99318489095540 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1438 c22250R_72_2 (by norm_num)

theorem c22250R_72_0 : rowsJ2 72 73 0 360 ≤ 100237900255772 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22250R_1437 c22250R_72_1 (by norm_num)

theorem hr22250R_72 : rows2 72 73 ≤ 100237900255772 := rows2_le_of_rowsJ2 72 73 c22250R_72_0

theorem c22250R_73_49 : rowsJ2 73 74 72 360 ≤ 3872569845997 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1537 rows22250R_1538 (by norm_num)

theorem c22250R_73_48 : rowsJ2 73 74 71 360 ≤ 6167037179965 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1536 c22250R_73_49 (by norm_num)

theorem c22250R_73_47 : rowsJ2 73 74 70 360 ≤ 8699901872337 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1535 c22250R_73_48 (by norm_num)

theorem c22250R_73_46 : rowsJ2 73 74 69 360 ≤ 11465062002484 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1534 c22250R_73_47 (by norm_num)

theorem c22250R_73_45 : rowsJ2 73 74 68 360 ≤ 14464444758412 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1533 c22250R_73_46 (by norm_num)

theorem c22250R_73_44 : rowsJ2 73 74 67 360 ≤ 17743971286459 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1532 c22250R_73_45 (by norm_num)

theorem c22250R_73_43 : rowsJ2 73 74 66 360 ≤ 21306041311851 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1531 c22250R_73_44 (by norm_num)

theorem c22250R_73_42 : rowsJ2 73 74 65 360 ≤ 25196450533663 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1530 c22250R_73_43 (by norm_num)

theorem c22250R_73_41 : rowsJ2 73 74 64 360 ≤ 29418128283964 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1529 c22250R_73_42 (by norm_num)

theorem c22250R_73_40 : rowsJ2 73 74 63 360 ≤ 33963350215165 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1528 c22250R_73_41 (by norm_num)

theorem c22250R_73_39 : rowsJ2 73 74 62 360 ≤ 38835272723019 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1527 c22250R_73_40 (by norm_num)

theorem c22250R_73_38 : rowsJ2 73 74 61 360 ≤ 44026664768579 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1526 c22250R_73_39 (by norm_num)

theorem c22250R_73_37 : rowsJ2 73 74 60 360 ≤ 49540909148008 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1525 c22250R_73_38 (by norm_num)

theorem c22250R_73_36 : rowsJ2 73 74 59 360 ≤ 55371253780776 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1524 c22250R_73_37 (by norm_num)

theorem c22250R_73_35 : rowsJ2 73 74 58 360 ≤ 61227697244506 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1523 c22250R_73_36 (by norm_num)

theorem c22250R_73_34 : rowsJ2 73 74 57 360 ≤ 66770439236012 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1522 c22250R_73_35 (by norm_num)

theorem c22250R_73_33 : rowsJ2 73 74 56 360 ≤ 71812518974303 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1521 c22250R_73_34 (by norm_num)

theorem c22250R_73_32 : rowsJ2 73 74 55 360 ≤ 76261659829275 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1520 c22250R_73_33 (by norm_num)

theorem c22250R_73_31 : rowsJ2 73 74 54 360 ≤ 80145106437932 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1519 c22250R_73_32 (by norm_num)

theorem c22250R_73_30 : rowsJ2 73 74 53 360 ≤ 83478029332186 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1518 c22250R_73_31 (by norm_num)

theorem c22250R_73_29 : rowsJ2 73 74 52 360 ≤ 86082407272943 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1517 c22250R_73_30 (by norm_num)

theorem c22250R_73_28 : rowsJ2 73 74 51 360 ≤ 87899573338314 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1516 c22250R_73_29 (by norm_num)

theorem c22250R_73_27 : rowsJ2 73 74 50 360 ≤ 89161935423451 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1515 c22250R_73_28 (by norm_num)

theorem c22250R_73_26 : rowsJ2 73 74 49 360 ≤ 90001255419446 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1514 c22250R_73_27 (by norm_num)

theorem c22250R_73_25 : rowsJ2 73 74 48 360 ≤ 90451986415149 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1513 c22250R_73_26 (by norm_num)

theorem c22250R_73_24 : rowsJ2 73 74 47 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1512 c22250R_73_25 (by norm_num)

theorem c22250R_73_23 : rowsJ2 73 74 46 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1511 c22250R_73_24 (by norm_num)

theorem c22250R_73_22 : rowsJ2 73 74 45 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1510 c22250R_73_23 (by norm_num)

theorem c22250R_73_21 : rowsJ2 73 74 44 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1509 c22250R_73_22 (by norm_num)

theorem c22250R_73_20 : rowsJ2 73 74 43 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1508 c22250R_73_21 (by norm_num)

theorem c22250R_73_19 : rowsJ2 73 74 41 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1507 c22250R_73_20 (by norm_num)

theorem c22250R_73_18 : rowsJ2 73 74 39 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1506 c22250R_73_19 (by norm_num)

theorem c22250R_73_17 : rowsJ2 73 74 37 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1505 c22250R_73_18 (by norm_num)

theorem c22250R_73_16 : rowsJ2 73 74 36 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1504 c22250R_73_17 (by norm_num)

theorem c22250R_73_15 : rowsJ2 73 74 35 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1503 c22250R_73_16 (by norm_num)

theorem c22250R_73_14 : rowsJ2 73 74 34 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1502 c22250R_73_15 (by norm_num)

theorem c22250R_73_13 : rowsJ2 73 74 33 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1501 c22250R_73_14 (by norm_num)

theorem c22250R_73_12 : rowsJ2 73 74 32 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1500 c22250R_73_13 (by norm_num)

theorem c22250R_73_11 : rowsJ2 73 74 31 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1499 c22250R_73_12 (by norm_num)

theorem c22250R_73_10 : rowsJ2 73 74 30 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1498 c22250R_73_11 (by norm_num)

theorem c22250R_73_9 : rowsJ2 73 74 29 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1497 c22250R_73_10 (by norm_num)

theorem c22250R_73_8 : rowsJ2 73 74 28 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1496 c22250R_73_9 (by norm_num)

theorem c22250R_73_7 : rowsJ2 73 74 27 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1495 c22250R_73_8 (by norm_num)

theorem c22250R_73_6 : rowsJ2 73 74 26 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1494 c22250R_73_7 (by norm_num)

theorem c22250R_73_5 : rowsJ2 73 74 25 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1493 c22250R_73_6 (by norm_num)

theorem c22250R_73_4 : rowsJ2 73 74 24 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1492 c22250R_73_5 (by norm_num)

theorem c22250R_73_3 : rowsJ2 73 74 23 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1491 c22250R_73_4 (by norm_num)

theorem c22250R_73_2 : rowsJ2 73 74 21 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1490 c22250R_73_3 (by norm_num)

theorem c22250R_73_1 : rowsJ2 73 74 19 360 ≤ 90552554731147 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1489 c22250R_73_2 (by norm_num)

theorem c22250R_73_0 : rowsJ2 73 74 0 360 ≤ 91359248266423 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22250R_1488 c22250R_73_1 (by norm_num)

theorem hr22250R_73 : rows2 73 74 ≤ 91359248266423 := rows2_le_of_rowsJ2 73 74 c22250R_73_0

theorem c22250R_74_50 : rowsJ2 74 75 73 360 ≤ 2628717264380 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1589 rows22250R_1590 (by norm_num)

theorem c22250R_74_49 : rowsJ2 74 75 72 360 ≤ 4282595678936 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1588 c22250R_74_50 (by norm_num)

theorem c22250R_74_48 : rowsJ2 74 75 71 360 ≤ 6127183719646 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1587 c22250R_74_49 (by norm_num)

theorem c22250R_74_47 : rowsJ2 74 75 70 360 ≤ 8209166074569 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1586 c22250R_74_48 (by norm_num)

theorem c22250R_74_46 : rowsJ2 74 75 69 360 ≤ 10478208763291 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1585 c22250R_74_47 (by norm_num)

theorem c22250R_74_45 : rowsJ2 74 75 68 360 ≤ 12980443909390 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1584 c22250R_74_46 (by norm_num)

theorem c22250R_74_44 : rowsJ2 74 75 67 360 ≤ 15717784748862 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1583 c22250R_74_45 (by norm_num)

theorem c22250R_74_43 : rowsJ2 74 75 66 360 ≤ 18736161995501 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1582 c22250R_74_44 (by norm_num)

theorem c22250R_74_42 : rowsJ2 74 75 65 360 ≤ 22037972315718 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1581 c22250R_74_43 (by norm_num)

theorem c22250R_74_41 : rowsJ2 74 75 64 360 ≤ 25669038367848 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1580 c22250R_74_42 (by norm_num)

theorem c22250R_74_40 : rowsJ2 74 75 63 360 ≤ 29579241509574 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1579 c22250R_74_41 (by norm_num)

theorem c22250R_74_39 : rowsJ2 74 75 62 360 ≤ 33814031742399 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1578 c22250R_74_40 (by norm_num)

theorem c22250R_74_38 : rowsJ2 74 75 61 360 ≤ 38324317687830 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1577 c22250R_74_39 (by norm_num)

theorem c22250R_74_37 : rowsJ2 74 75 60 360 ≤ 43155210391285 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1576 c22250R_74_38 (by norm_num)

theorem c22250R_74_36 : rowsJ2 74 75 59 360 ≤ 48258597873443 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1575 c22250R_74_37 (by norm_num)

theorem c22250R_74_35 : rowsJ2 74 75 58 360 ≤ 53679286591895 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1574 c22250R_74_36 (by norm_num)

theorem c22250R_74_34 : rowsJ2 74 75 57 360 ≤ 58837994308978 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1573 c22250R_74_35 (by norm_num)

theorem c22250R_74_33 : rowsJ2 74 75 56 360 ≤ 63587877362746 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1572 c22250R_74_34 (by norm_num)

theorem c22250R_74_32 : rowsJ2 74 75 55 360 ≤ 67794942761448 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1571 c22250R_74_33 (by norm_num)

theorem c22250R_74_31 : rowsJ2 74 75 54 360 ≤ 71524670388190 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1570 c22250R_74_32 (by norm_num)

theorem c22250R_74_30 : rowsJ2 74 75 53 360 ≤ 74750348279942 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1569 c22250R_74_31 (by norm_num)

theorem c22250R_74_29 : rowsJ2 74 75 52 360 ≤ 77333689028627 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1568 c22250R_74_30 (by norm_num)

theorem c22250R_74_28 : rowsJ2 74 75 51 360 ≤ 79136176705371 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1567 c22250R_74_29 (by norm_num)

theorem c22250R_74_27 : rowsJ2 74 75 50 360 ≤ 80388341901174 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1566 c22250R_74_28 (by norm_num)

theorem c22250R_74_26 : rowsJ2 74 75 49 360 ≤ 81220882183792 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1565 c22250R_74_27 (by norm_num)

theorem c22250R_74_25 : rowsJ2 74 75 48 360 ≤ 81667972342893 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1564 c22250R_74_26 (by norm_num)

theorem c22250R_74_24 : rowsJ2 74 75 47 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1563 c22250R_74_25 (by norm_num)

theorem c22250R_74_23 : rowsJ2 74 75 46 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1562 c22250R_74_24 (by norm_num)

theorem c22250R_74_22 : rowsJ2 74 75 45 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1561 c22250R_74_23 (by norm_num)

theorem c22250R_74_21 : rowsJ2 74 75 44 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1560 c22250R_74_22 (by norm_num)

theorem c22250R_74_20 : rowsJ2 74 75 42 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1559 c22250R_74_21 (by norm_num)

theorem c22250R_74_19 : rowsJ2 74 75 40 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1558 c22250R_74_20 (by norm_num)

theorem c22250R_74_18 : rowsJ2 74 75 38 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1557 c22250R_74_19 (by norm_num)

theorem c22250R_74_17 : rowsJ2 74 75 36 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1556 c22250R_74_18 (by norm_num)

theorem c22250R_74_16 : rowsJ2 74 75 35 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1555 c22250R_74_17 (by norm_num)

theorem c22250R_74_15 : rowsJ2 74 75 34 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1554 c22250R_74_16 (by norm_num)

theorem c22250R_74_14 : rowsJ2 74 75 33 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1553 c22250R_74_15 (by norm_num)

theorem c22250R_74_13 : rowsJ2 74 75 32 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1552 c22250R_74_14 (by norm_num)

theorem c22250R_74_12 : rowsJ2 74 75 31 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1551 c22250R_74_13 (by norm_num)

theorem c22250R_74_11 : rowsJ2 74 75 30 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1550 c22250R_74_12 (by norm_num)

theorem c22250R_74_10 : rowsJ2 74 75 29 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1549 c22250R_74_11 (by norm_num)

theorem c22250R_74_9 : rowsJ2 74 75 28 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1548 c22250R_74_10 (by norm_num)

theorem c22250R_74_8 : rowsJ2 74 75 27 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1547 c22250R_74_9 (by norm_num)

theorem c22250R_74_7 : rowsJ2 74 75 26 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1546 c22250R_74_8 (by norm_num)

theorem c22250R_74_6 : rowsJ2 74 75 25 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1545 c22250R_74_7 (by norm_num)

theorem c22250R_74_5 : rowsJ2 74 75 24 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1544 c22250R_74_6 (by norm_num)

theorem c22250R_74_4 : rowsJ2 74 75 23 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1543 c22250R_74_5 (by norm_num)

theorem c22250R_74_3 : rowsJ2 74 75 22 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1542 c22250R_74_4 (by norm_num)

theorem c22250R_74_2 : rowsJ2 74 75 21 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1541 c22250R_74_3 (by norm_num)

theorem c22250R_74_1 : rowsJ2 74 75 19 360 ≤ 81767728305604 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1540 c22250R_74_2 (by norm_num)

theorem c22250R_74_0 : rowsJ2 74 75 0 360 ≤ 82472874562158 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22250R_1539 c22250R_74_1 (by norm_num)

theorem hr22250R_74 : rows2 74 75 ≤ 82472874562158 := rows2_le_of_rowsJ2 74 75 c22250R_74_0

theorem c22250R_75_51 : rowsJ2 75 76 74 360 ≤ 1630821020542 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1642 rows22250R_1643 (by norm_num)

theorem c22250R_75_50 : rowsJ2 75 76 73 360 ≤ 2740145155661 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1641 c22250R_75_51 (by norm_num)

theorem c22250R_75_49 : rowsJ2 75 76 72 360 ≤ 4044752385395 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1640 c22250R_75_50 (by norm_num)

theorem c22250R_75_48 : rowsJ2 75 76 71 360 ≤ 5539349043847 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1639 c22250R_75_49 (by norm_num)

theorem c22250R_75_47 : rowsJ2 75 76 70 360 ≤ 7225279653020 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1638 c22250R_75_48 (by norm_num)

theorem c22250R_75_46 : rowsJ2 75 76 69 360 ≤ 9097560398836 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1637 c22250R_75_47 (by norm_num)

theorem c22250R_75_45 : rowsJ2 75 76 68 360 ≤ 11157663374730 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1636 c22250R_75_46 (by norm_num)

theorem c22250R_75_44 : rowsJ2 75 76 67 360 ≤ 13451730772556 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1635 c22250R_75_45 (by norm_num)

theorem c22250R_75_43 : rowsJ2 75 76 66 360 ≤ 15981672903547 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1634 c22250R_75_44 (by norm_num)

theorem c22250R_75_42 : rowsJ2 75 76 65 360 ≤ 18793447124321 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1633 c22250R_75_43 (by norm_num)

theorem c22250R_75_41 : rowsJ2 75 76 64 360 ≤ 21889458033582 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1632 c22250R_75_42 (by norm_num)

theorem c22250R_75_40 : rowsJ2 75 76 63 360 ≤ 25262940905790 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1631 c22250R_75_41 (by norm_num)

theorem c22250R_75_39 : rowsJ2 75 76 62 360 ≤ 28916496655287 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1630 c22250R_75_40 (by norm_num)

theorem c22250R_75_38 : rowsJ2 75 76 61 360 ≤ 32843787600821 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1629 c22250R_75_39 (by norm_num)

theorem c22250R_75_37 : rowsJ2 75 76 60 360 ≤ 37047609849476 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1628 c22250R_75_38 (by norm_num)

theorem c22250R_75_36 : rowsJ2 75 76 59 360 ≤ 41522039744261 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1627 c22250R_75_37 (by norm_num)

theorem c22250R_75_35 : rowsJ2 75 76 58 360 ≤ 46270068955000 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1626 c22250R_75_36 (by norm_num)

theorem c22250R_75_34 : rowsJ2 75 76 57 360 ≤ 51043788357556 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1625 c22250R_75_35 (by norm_num)

theorem c22250R_75_33 : rowsJ2 75 76 56 360 ≤ 55460066882754 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1624 c22250R_75_34 (by norm_num)

theorem c22250R_75_32 : rowsJ2 75 76 55 360 ≤ 59424731346547 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1623 c22250R_75_33 (by norm_num)

theorem c22250R_75_31 : rowsJ2 75 76 54 360 ≤ 62960294538054 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1622 c22250R_75_32 (by norm_num)

theorem c22250R_75_30 : rowsJ2 75 76 53 360 ≤ 66078849275052 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1621 c22250R_75_31 (by norm_num)

theorem c22250R_75_29 : rowsJ2 75 76 52 360 ≤ 68601459491277 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1620 c22250R_75_30 (by norm_num)

theorem c22250R_75_28 : rowsJ2 75 76 51 360 ≤ 70389504012347 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1619 c22250R_75_29 (by norm_num)

theorem c22250R_75_27 : rowsJ2 75 76 50 360 ≤ 71631635732144 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1618 c22250R_75_28 (by norm_num)

theorem c22250R_75_26 : rowsJ2 75 76 49 360 ≤ 72457504951731 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1617 c22250R_75_27 (by norm_num)

theorem c22250R_75_25 : rowsJ2 75 76 48 360 ≤ 72901012621559 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1616 c22250R_75_26 (by norm_num)

theorem c22250R_75_24 : rowsJ2 75 76 47 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1615 c22250R_75_25 (by norm_num)

theorem c22250R_75_23 : rowsJ2 75 76 46 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1614 c22250R_75_24 (by norm_num)

theorem c22250R_75_22 : rowsJ2 75 76 45 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1613 c22250R_75_23 (by norm_num)

theorem c22250R_75_21 : rowsJ2 75 76 44 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1612 c22250R_75_22 (by norm_num)

theorem c22250R_75_20 : rowsJ2 75 76 43 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1611 c22250R_75_21 (by norm_num)

theorem c22250R_75_19 : rowsJ2 75 76 41 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1610 c22250R_75_20 (by norm_num)

theorem c22250R_75_18 : rowsJ2 75 76 39 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1609 c22250R_75_19 (by norm_num)

theorem c22250R_75_17 : rowsJ2 75 76 37 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1608 c22250R_75_18 (by norm_num)

theorem c22250R_75_16 : rowsJ2 75 76 35 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1607 c22250R_75_17 (by norm_num)

theorem c22250R_75_15 : rowsJ2 75 76 34 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1606 c22250R_75_16 (by norm_num)

theorem c22250R_75_14 : rowsJ2 75 76 33 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1605 c22250R_75_15 (by norm_num)

theorem c22250R_75_13 : rowsJ2 75 76 32 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1604 c22250R_75_14 (by norm_num)

theorem c22250R_75_12 : rowsJ2 75 76 31 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1603 c22250R_75_13 (by norm_num)

theorem c22250R_75_11 : rowsJ2 75 76 30 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1602 c22250R_75_12 (by norm_num)

theorem c22250R_75_10 : rowsJ2 75 76 29 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1601 c22250R_75_11 (by norm_num)

theorem c22250R_75_9 : rowsJ2 75 76 28 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1600 c22250R_75_10 (by norm_num)

theorem c22250R_75_8 : rowsJ2 75 76 27 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1599 c22250R_75_9 (by norm_num)

theorem c22250R_75_7 : rowsJ2 75 76 26 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1598 c22250R_75_8 (by norm_num)

theorem c22250R_75_6 : rowsJ2 75 76 25 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1597 c22250R_75_7 (by norm_num)

theorem c22250R_75_5 : rowsJ2 75 76 24 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1596 c22250R_75_6 (by norm_num)

theorem c22250R_75_4 : rowsJ2 75 76 23 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1595 c22250R_75_5 (by norm_num)

theorem c22250R_75_3 : rowsJ2 75 76 22 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1594 c22250R_75_4 (by norm_num)

theorem c22250R_75_2 : rowsJ2 75 76 21 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1593 c22250R_75_3 (by norm_num)

theorem c22250R_75_1 : rowsJ2 75 76 19 360 ≤ 72999969249597 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1592 c22250R_75_2 (by norm_num)

theorem c22250R_75_0 : rowsJ2 75 76 0 360 ≤ 73609471539874 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22250R_1591 c22250R_75_1 (by norm_num)

theorem hr22250R_75 : rows2 75 76 ≤ 73609471539874 := rows2_le_of_rowsJ2 75 76 c22250R_75_0

theorem c22250R_76_51 : rowsJ2 76 77 75 360 ≤ 775218826516 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1695 rows22250R_1696 (by norm_num)

theorem c22250R_76_50 : rowsJ2 76 77 74 360 ≤ 1436917262910 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1694 c22250R_76_51 (by norm_num)

theorem c22250R_76_49 : rowsJ2 76 77 73 360 ≤ 2245447972897 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1693 c22250R_76_50 (by norm_num)

theorem c22250R_76_48 : rowsJ2 76 77 72 360 ≤ 3248489888271 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1692 c22250R_76_49 (by norm_num)

theorem c22250R_76_47 : rowsJ2 76 77 71 360 ≤ 4395098423638 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1691 c22250R_76_48 (by norm_num)

theorem c22250R_76_46 : rowsJ2 76 77 70 360 ≤ 5732305130226 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1690 c22250R_76_47 (by norm_num)

theorem c22250R_76_45 : rowsJ2 76 77 69 360 ≤ 7210181396936 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1689 c22250R_76_46 (by norm_num)

theorem c22250R_76_44 : rowsJ2 76 77 68 360 ≤ 8875149034437 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1688 c22250R_76_45 (by norm_num)

theorem c22250R_76_43 : rowsJ2 76 77 67 360 ≤ 10728668601206 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1687 c22250R_76_44 (by norm_num)

theorem c22250R_76_42 : rowsJ2 76 77 66 360 ≤ 12816899991448 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1686 c22250R_76_43 (by norm_num)

theorem c22250R_76_41 : rowsJ2 76 77 65 360 ≤ 15141752217568 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1685 c22250R_76_42 (by norm_num)

theorem c22250R_76_40 : rowsJ2 76 77 64 360 ≤ 17749217074646 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1684 c22250R_76_41 (by norm_num)

theorem c22250R_76_39 : rowsJ2 76 77 63 360 ≤ 20589495795818 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1683 c22250R_76_40 (by norm_num)

theorem c22250R_76_38 : rowsJ2 76 77 62 360 ≤ 23708153334805 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1682 c22250R_76_39 (by norm_num)

theorem c22250R_76_37 : rowsJ2 76 77 61 360 ≤ 27056374189353 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1681 c22250R_76_38 (by norm_num)

theorem c22250R_76_36 : rowsJ2 76 77 60 360 ≤ 30679331001626 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1680 c22250R_76_37 (by norm_num)

theorem c22250R_76_35 : rowsJ2 76 77 59 360 ≤ 34529143944651 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1679 c22250R_76_36 (by norm_num)

theorem c22250R_76_34 : rowsJ2 76 77 58 360 ≤ 38650628252395 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1678 c22250R_76_35 (by norm_num)

theorem c22250R_76_33 : rowsJ2 76 77 57 360 ≤ 42996795087714 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1677 c22250R_76_34 (by norm_num)

theorem c22250R_76_32 : rowsJ2 76 77 56 360 ≤ 47078614319128 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1676 c22250R_76_33 (by norm_num)

theorem c22250R_76_31 : rowsJ2 76 77 55 360 ≤ 50759488661300 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1675 c22250R_76_32 (by norm_num)

theorem c22250R_76_30 : rowsJ2 76 77 54 360 ≤ 54100640716149 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1674 c22250R_76_31 (by norm_num)

theorem c22250R_76_29 : rowsJ2 76 77 53 360 ≤ 57071635099212 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1673 c22250R_76_30 (by norm_num)

theorem c22250R_76_28 : rowsJ2 76 77 52 360 ≤ 59533688441697 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1672 c22250R_76_29 (by norm_num)

theorem c22250R_76_27 : rowsJ2 76 77 51 360 ≤ 61307519430310 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1671 c22250R_76_28 (by norm_num)

theorem c22250R_76_26 : rowsJ2 76 77 50 360 ≤ 62539777190422 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1670 c22250R_76_27 (by norm_num)

theorem c22250R_76_25 : rowsJ2 76 77 49 360 ≤ 63359081406274 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1669 c22250R_76_26 (by norm_num)

theorem c22250R_76_24 : rowsJ2 76 77 48 360 ≤ 63799063542713 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1668 c22250R_76_25 (by norm_num)

theorem c22250R_76_23 : rowsJ2 76 77 47 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1667 c22250R_76_24 (by norm_num)

theorem c22250R_76_22 : rowsJ2 76 77 46 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1666 c22250R_76_23 (by norm_num)

theorem c22250R_76_21 : rowsJ2 76 77 45 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1665 c22250R_76_22 (by norm_num)

theorem c22250R_76_20 : rowsJ2 76 77 44 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1664 c22250R_76_21 (by norm_num)

theorem c22250R_76_19 : rowsJ2 76 77 42 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1663 c22250R_76_20 (by norm_num)

theorem c22250R_76_18 : rowsJ2 76 77 40 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1662 c22250R_76_19 (by norm_num)

theorem c22250R_76_17 : rowsJ2 76 77 38 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1661 c22250R_76_18 (by norm_num)

theorem c22250R_76_16 : rowsJ2 76 77 36 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1660 c22250R_76_17 (by norm_num)

theorem c22250R_76_15 : rowsJ2 76 77 34 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1659 c22250R_76_16 (by norm_num)

theorem c22250R_76_14 : rowsJ2 76 77 33 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1658 c22250R_76_15 (by norm_num)

theorem c22250R_76_13 : rowsJ2 76 77 32 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1657 c22250R_76_14 (by norm_num)

theorem c22250R_76_12 : rowsJ2 76 77 31 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1656 c22250R_76_13 (by norm_num)

theorem c22250R_76_11 : rowsJ2 76 77 30 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1655 c22250R_76_12 (by norm_num)

theorem c22250R_76_10 : rowsJ2 76 77 29 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1654 c22250R_76_11 (by norm_num)

theorem c22250R_76_9 : rowsJ2 76 77 28 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1653 c22250R_76_10 (by norm_num)

theorem c22250R_76_8 : rowsJ2 76 77 27 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1652 c22250R_76_9 (by norm_num)

theorem c22250R_76_7 : rowsJ2 76 77 26 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1651 c22250R_76_8 (by norm_num)

theorem c22250R_76_6 : rowsJ2 76 77 25 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1650 c22250R_76_7 (by norm_num)

theorem c22250R_76_5 : rowsJ2 76 77 24 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1649 c22250R_76_6 (by norm_num)

theorem c22250R_76_4 : rowsJ2 76 77 23 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1648 c22250R_76_5 (by norm_num)

theorem c22250R_76_3 : rowsJ2 76 77 22 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1647 c22250R_76_4 (by norm_num)

theorem c22250R_76_2 : rowsJ2 76 77 21 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1646 c22250R_76_3 (by norm_num)

theorem c22250R_76_1 : rowsJ2 76 77 19 360 ≤ 63897233544228 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1645 c22250R_76_2 (by norm_num)

theorem c22250R_76_0 : rowsJ2 76 77 0 360 ≤ 64423224142469 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22250R_1644 c22250R_76_1 (by norm_num)

theorem hr22250R_76 : rows2 76 77 ≤ 64423224142469 := rows2_le_of_rowsJ2 76 77 c22250R_76_0

theorem c22250R_77_52 : rowsJ2 77 78 76 360 ≤ 210155445679 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1749 rows22250R_1750 (by norm_num)

theorem c22250R_77_51 : rowsJ2 77 78 75 360 ≤ 468864337812 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1748 c22250R_77_52 (by norm_num)

theorem c22250R_77_50 : rowsJ2 77 78 74 360 ≤ 878285229884 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1747 c22250R_77_51 (by norm_num)

theorem c22250R_77_49 : rowsJ2 77 78 73 360 ≤ 1434111608863 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1746 c22250R_77_50 (by norm_num)

theorem c22250R_77_48 : rowsJ2 77 78 72 360 ≤ 2137192218476 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1745 c22250R_77_49 (by norm_num)

theorem c22250R_77_47 : rowsJ2 77 78 71 360 ≤ 2983468230864 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1744 c22250R_77_48 (by norm_num)

theorem c22250R_77_46 : rowsJ2 77 78 70 360 ≤ 3973889012492 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1743 c22250R_77_47 (by norm_num)

theorem c22250R_77_45 : rowsJ2 77 78 69 360 ≤ 5104632069869 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1742 c22250R_77_46 (by norm_num)

theorem c22250R_77_44 : rowsJ2 77 78 68 360 ≤ 6376744313269 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1741 c22250R_77_45 (by norm_num)

theorem c22250R_77_43 : rowsJ2 77 78 67 360 ≤ 7836656743436 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1740 c22250R_77_44 (by norm_num)

theorem c22250R_77_42 : rowsJ2 77 78 66 360 ≤ 9485819832704 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1739 c22250R_77_43 (by norm_num)

theorem c22250R_77_41 : rowsJ2 77 78 65 360 ≤ 11370418771849 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1738 c22250R_77_42 (by norm_num)

theorem c22250R_77_40 : rowsJ2 77 78 64 360 ≤ 13492362847511 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1737 c22250R_77_41 (by norm_num)

theorem c22250R_77_39 : rowsJ2 77 78 63 360 ≤ 15845884766922 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1736 c22250R_77_40 (by norm_num)

theorem c22250R_77_38 : rowsJ2 77 78 62 360 ≤ 18433059224275 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1735 c22250R_77_39 (by norm_num)

theorem c22250R_77_37 : rowsJ2 77 78 61 360 ≤ 21248478850930 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1734 c22250R_77_38 (by norm_num)

theorem c22250R_77_36 : rowsJ2 77 78 60 360 ≤ 24294382307159 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1733 c22250R_77_37 (by norm_num)

theorem c22250R_77_35 : rowsJ2 77 78 59 360 ≤ 27565710646163 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1732 c22250R_77_36 (by norm_num)

theorem c22250R_77_34 : rowsJ2 77 78 58 360 ≤ 31064866318678 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1731 c22250R_77_35 (by norm_num)

theorem c22250R_77_33 : rowsJ2 77 78 57 360 ≤ 34787129087966 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1730 c22250R_77_34 (by norm_num)

theorem c22250R_77_32 : rowsJ2 77 78 56 360 ≤ 38491991095531 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1729 c22250R_77_33 (by norm_num)

theorem c22250R_77_31 : rowsJ2 77 78 55 360 ≤ 41888323090320 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1728 c22250R_77_32 (by norm_num)

theorem c22250R_77_30 : rowsJ2 77 78 54 360 ≤ 44993710735492 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1727 c22250R_77_31 (by norm_num)

theorem c22250R_77_29 : rowsJ2 77 78 53 360 ≤ 47816993756372 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1726 c22250R_77_30 (by norm_num)

theorem c22250R_77_28 : rowsJ2 77 78 52 360 ≤ 50178052686793 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1725 c22250R_77_29 (by norm_num)

theorem c22250R_77_27 : rowsJ2 77 78 51 360 ≤ 51937894333377 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1724 c22250R_77_28 (by norm_num)

theorem c22250R_77_26 : rowsJ2 77 78 50 360 ≤ 53160433876031 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1723 c22250R_77_27 (by norm_num)

theorem c22250R_77_25 : rowsJ2 77 78 49 360 ≤ 53973276638125 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1722 c22250R_77_26 (by norm_num)

theorem c22250R_77_24 : rowsJ2 77 78 48 360 ≤ 54409788849507 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1721 c22250R_77_25 (by norm_num)

theorem c22250R_77_23 : rowsJ2 77 78 47 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1720 c22250R_77_24 (by norm_num)

theorem c22250R_77_22 : rowsJ2 77 78 46 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1719 c22250R_77_23 (by norm_num)

theorem c22250R_77_21 : rowsJ2 77 78 45 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1718 c22250R_77_22 (by norm_num)

theorem c22250R_77_20 : rowsJ2 77 78 44 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1717 c22250R_77_21 (by norm_num)

theorem c22250R_77_19 : rowsJ2 77 78 43 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1716 c22250R_77_20 (by norm_num)

theorem c22250R_77_18 : rowsJ2 77 78 41 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1715 c22250R_77_19 (by norm_num)

theorem c22250R_77_17 : rowsJ2 77 78 39 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1714 c22250R_77_18 (by norm_num)

theorem c22250R_77_16 : rowsJ2 77 78 37 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1713 c22250R_77_17 (by norm_num)

theorem c22250R_77_15 : rowsJ2 77 78 35 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1712 c22250R_77_16 (by norm_num)

theorem c22250R_77_14 : rowsJ2 77 78 33 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1711 c22250R_77_15 (by norm_num)

theorem c22250R_77_13 : rowsJ2 77 78 32 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1710 c22250R_77_14 (by norm_num)

theorem c22250R_77_12 : rowsJ2 77 78 31 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1709 c22250R_77_13 (by norm_num)

theorem c22250R_77_11 : rowsJ2 77 78 30 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1708 c22250R_77_12 (by norm_num)

theorem c22250R_77_10 : rowsJ2 77 78 29 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1707 c22250R_77_11 (by norm_num)

theorem c22250R_77_9 : rowsJ2 77 78 28 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1706 c22250R_77_10 (by norm_num)

theorem c22250R_77_8 : rowsJ2 77 78 27 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1705 c22250R_77_9 (by norm_num)

theorem c22250R_77_7 : rowsJ2 77 78 26 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1704 c22250R_77_8 (by norm_num)

theorem c22250R_77_6 : rowsJ2 77 78 25 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1703 c22250R_77_7 (by norm_num)

theorem c22250R_77_5 : rowsJ2 77 78 24 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1702 c22250R_77_6 (by norm_num)

theorem c22250R_77_4 : rowsJ2 77 78 23 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1701 c22250R_77_5 (by norm_num)

theorem c22250R_77_3 : rowsJ2 77 78 22 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1700 c22250R_77_4 (by norm_num)

theorem c22250R_77_2 : rowsJ2 77 78 21 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1699 c22250R_77_3 (by norm_num)

theorem c22250R_77_1 : rowsJ2 77 78 19 360 ≤ 54507184631980 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1698 c22250R_77_2 (by norm_num)

theorem c22250R_77_0 : rowsJ2 77 78 0 360 ≤ 54955597664860 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22250R_1697 c22250R_77_1 (by norm_num)

theorem hr22250R_77 : rows2 77 78 ≤ 54955597664860 := rows2_le_of_rowsJ2 77 78 c22250R_77_0

theorem c22250R_78_52 : rowsJ2 78 79 77 360 ≤ 0 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1803 rows22250R_1804 (by norm_num)

theorem c22250R_78_51 : rowsJ2 78 79 76 360 ≤ 52835399032 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1802 c22250R_78_52 (by norm_num)

theorem c22250R_78_50 : rowsJ2 78 79 75 360 ≤ 156919696171 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1801 c22250R_78_51 (by norm_num)

theorem c22250R_78_49 : rowsJ2 78 79 74 360 ≤ 362607221235 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1800 c22250R_78_50 (by norm_num)

theorem c22250R_78_48 : rowsJ2 78 79 73 360 ≤ 666962346626 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1799 c22250R_78_49 (by norm_num)

theorem c22250R_78_47 : rowsJ2 78 79 72 360 ≤ 1118134521196 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1798 c22250R_78_48 (by norm_num)

theorem c22250R_78_46 : rowsJ2 78 79 71 360 ≤ 1665624281795 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1797 c22250R_78_47 (by norm_num)

theorem c22250R_78_45 : rowsJ2 78 79 70 360 ≤ 2356872254882 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1796 c22250R_78_46 (by norm_num)

theorem c22250R_78_44 : rowsJ2 78 79 69 360 ≤ 3142350269878 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1795 c22250R_78_45 (by norm_num)

theorem c22250R_78_43 : rowsJ2 78 79 68 360 ≤ 4068830009627 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1794 c22250R_78_44 (by norm_num)

theorem c22250R_78_42 : rowsJ2 78 79 67 360 ≤ 5137339915845 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1793 c22250R_78_43 (by norm_num)

theorem c22250R_78_41 : rowsJ2 78 79 66 360 ≤ 6394327597616 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1792 c22250R_78_42 (by norm_num)

theorem c22250R_78_40 : rowsJ2 78 79 65 360 ≤ 7841234827373 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1791 c22250R_78_41 (by norm_num)

theorem c22250R_78_39 : rowsJ2 78 79 64 360 ≤ 9524279655564 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1790 c22250R_78_40 (by norm_num)

theorem c22250R_78_38 : rowsJ2 78 79 63 360 ≤ 11393977200506 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1789 c22250R_78_39 (by norm_num)

theorem c22250R_78_37 : rowsJ2 78 79 62 360 ≤ 13496063116245 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1788 c22250R_78_38 (by norm_num)

theorem c22250R_78_36 : rowsJ2 78 79 61 360 ≤ 15781992134914 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1787 c22250R_78_37 (by norm_num)

theorem c22250R_78_35 : rowsJ2 78 79 60 360 ≤ 18297053057190 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1786 c22250R_78_36 (by norm_num)

theorem c22250R_78_34 : rowsJ2 78 79 59 360 ≤ 20993592996731 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1785 c22250R_78_35 (by norm_num)

theorem c22250R_78_33 : rowsJ2 78 79 58 360 ≤ 23916489515871 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1784 c22250R_78_34 (by norm_num)

theorem c22250R_78_32 : rowsJ2 78 79 57 360 ≤ 27018937527201 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1783 c22250R_78_33 (by norm_num)

theorem c22250R_78_31 : rowsJ2 78 79 56 360 ≤ 30345439140612 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1782 c22250R_78_32 (by norm_num)

theorem c22250R_78_30 : rowsJ2 78 79 55 360 ≤ 33414793033526 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1781 c22250R_78_31 (by norm_num)

theorem c22250R_78_29 : rowsJ2 78 79 54 360 ≤ 36283788887539 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1780 c22250R_78_30 (by norm_num)

theorem c22250R_78_28 : rowsJ2 78 79 53 360 ≤ 38918052460642 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1779 c22250R_78_29 (by norm_num)

theorem c22250R_78_27 : rowsJ2 78 79 52 360 ≤ 41178058996099 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1778 c22250R_78_28 (by norm_num)

theorem c22250R_78_26 : rowsJ2 78 79 51 360 ≤ 42883464963594 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1777 c22250R_78_27 (by norm_num)

theorem c22250R_78_25 : rowsJ2 78 79 50 360 ≤ 44096438375071 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1776 c22250R_78_26 (by norm_num)

theorem c22250R_78_24 : rowsJ2 78 79 49 360 ≤ 44902920802616 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1775 c22250R_78_25 (by norm_num)

theorem c22250R_78_23 : rowsJ2 78 79 48 360 ≤ 45336017391902 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1774 c22250R_78_24 (by norm_num)

theorem c22250R_78_22 : rowsJ2 78 79 47 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1773 c22250R_78_23 (by norm_num)

theorem c22250R_78_21 : rowsJ2 78 79 46 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1772 c22250R_78_22 (by norm_num)

theorem c22250R_78_20 : rowsJ2 78 79 45 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1771 c22250R_78_21 (by norm_num)

theorem c22250R_78_19 : rowsJ2 78 79 44 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1770 c22250R_78_20 (by norm_num)

theorem c22250R_78_18 : rowsJ2 78 79 43 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1769 c22250R_78_19 (by norm_num)

theorem c22250R_78_17 : rowsJ2 78 79 41 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1768 c22250R_78_18 (by norm_num)

theorem c22250R_78_16 : rowsJ2 78 79 39 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1767 c22250R_78_17 (by norm_num)

theorem c22250R_78_15 : rowsJ2 78 79 37 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1766 c22250R_78_16 (by norm_num)

theorem c22250R_78_14 : rowsJ2 78 79 35 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1765 c22250R_78_15 (by norm_num)

theorem c22250R_78_13 : rowsJ2 78 79 33 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1764 c22250R_78_14 (by norm_num)

theorem c22250R_78_12 : rowsJ2 78 79 31 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1763 c22250R_78_13 (by norm_num)

theorem c22250R_78_11 : rowsJ2 78 79 30 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1762 c22250R_78_12 (by norm_num)

theorem c22250R_78_10 : rowsJ2 78 79 29 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1761 c22250R_78_11 (by norm_num)

theorem c22250R_78_9 : rowsJ2 78 79 28 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1760 c22250R_78_10 (by norm_num)

theorem c22250R_78_8 : rowsJ2 78 79 27 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1759 c22250R_78_9 (by norm_num)

theorem c22250R_78_7 : rowsJ2 78 79 26 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1758 c22250R_78_8 (by norm_num)

theorem c22250R_78_6 : rowsJ2 78 79 25 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1757 c22250R_78_7 (by norm_num)

theorem c22250R_78_5 : rowsJ2 78 79 24 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1756 c22250R_78_6 (by norm_num)

theorem c22250R_78_4 : rowsJ2 78 79 23 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1755 c22250R_78_5 (by norm_num)

theorem c22250R_78_3 : rowsJ2 78 79 22 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1754 c22250R_78_4 (by norm_num)

theorem c22250R_78_2 : rowsJ2 78 79 21 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1753 c22250R_78_3 (by norm_num)

theorem c22250R_78_1 : rowsJ2 78 79 18 360 ≤ 45432651071556 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1752 c22250R_78_2 (by norm_num)

theorem c22250R_78_0 : rowsJ2 78 79 0 360 ≤ 45809448780232 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22250R_1751 c22250R_78_1 (by norm_num)

theorem hr22250R_78 : rows2 78 79 ≤ 45809448780232 := rows2_le_of_rowsJ2 78 79 c22250R_78_0

theorem c22250R_79_51 : rowsJ2 79 80 77 360 ≤ 0 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1856 rows22250R_1857 (by norm_num)

theorem c22250R_79_50 : rowsJ2 79 80 76 360 ≤ 0 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1855 c22250R_79_51 (by norm_num)

theorem c22250R_79_49 : rowsJ2 79 80 75 360 ≤ 0 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1854 c22250R_79_50 (by norm_num)

theorem c22250R_79_48 : rowsJ2 79 80 74 360 ≤ 51452026427 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1853 c22250R_79_49 (by norm_num)

theorem c22250R_79_47 : rowsJ2 79 80 73 360 ≤ 152851000698 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1852 c22250R_79_48 (by norm_num)

theorem c22250R_79_46 : rowsJ2 79 80 72 360 ≤ 353303713267 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1851 c22250R_79_47 (by norm_num)

theorem c22250R_79_45 : rowsJ2 79 80 71 360 ≤ 650024907229 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1850 c22250R_79_46 (by norm_num)

theorem c22250R_79_44 : rowsJ2 79 80 70 360 ≤ 1043590207930 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1849 c22250R_79_45 (by norm_num)

theorem c22250R_79_43 : rowsJ2 79 80 69 360 ≤ 1531375358049 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1848 c22250R_79_44 (by norm_num)

theorem c22250R_79_42 : rowsJ2 79 80 68 360 ≤ 2114022930567 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1847 c22250R_79_43 (by norm_num)

theorem c22250R_79_41 : rowsJ2 79 80 67 360 ≤ 2838312943732 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1846 c22250R_79_42 (by norm_num)

theorem c22250R_79_40 : rowsJ2 79 80 66 360 ≤ 3705256591414 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1845 c22250R_79_41 (by norm_num)

theorem c22250R_79_39 : rowsJ2 79 80 65 360 ≤ 4761325468305 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1844 c22250R_79_40 (by norm_num)

theorem c22250R_79_38 : rowsJ2 79 80 64 360 ≤ 6007953974107 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1843 c22250R_79_39 (by norm_num)

theorem c22250R_79_37 : rowsJ2 79 80 63 360 ≤ 7440403633884 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1842 c22250R_79_38 (by norm_num)

theorem c22250R_79_36 : rowsJ2 79 80 62 360 ≤ 9060243181452 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1841 c22250R_79_37 (by norm_num)

theorem c22250R_79_35 : rowsJ2 79 80 61 360 ≤ 10863025974567 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1840 c22250R_79_36 (by norm_num)

theorem c22250R_79_34 : rowsJ2 79 80 60 360 ≤ 12850453431279 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1839 c22250R_79_35 (by norm_num)

theorem c22250R_79_33 : rowsJ2 79 80 59 360 ≤ 15018360919954 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1838 c22250R_79_34 (by norm_num)

theorem c22250R_79_32 : rowsJ2 79 80 58 360 ≤ 17368581928468 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1837 c22250R_79_33 (by norm_num)

theorem c22250R_79_31 : rowsJ2 79 80 57 360 ≤ 19897225476206 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1836 c22250R_79_32 (by norm_num)

theorem c22250R_79_30 : rowsJ2 79 80 56 360 ≤ 22606257526386 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1835 c22250R_79_31 (by norm_num)

theorem c22250R_79_29 : rowsJ2 79 80 55 360 ≤ 25347383200754 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1834 c22250R_79_30 (by norm_num)

theorem c22250R_79_28 : rowsJ2 79 80 54 360 ≤ 27937628133675 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1833 c22250R_79_29 (by norm_num)

theorem c22250R_79_27 : rowsJ2 79 80 53 360 ≤ 30382384354333 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1832 c22250R_79_28 (by norm_num)

theorem c22250R_79_26 : rowsJ2 79 80 52 360 ≤ 32500065730387 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1831 c22250R_79_27 (by norm_num)

theorem c22250R_79_25 : rowsJ2 79 80 51 360 ≤ 34151068632168 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1830 c22250R_79_26 (by norm_num)

theorem c22250R_79_24 : rowsJ2 79 80 50 360 ≤ 35354624456326 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1829 c22250R_79_25 (by norm_num)

theorem c22250R_79_23 : rowsJ2 79 80 49 360 ≤ 36154845313249 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1828 c22250R_79_24 (by norm_num)

theorem c22250R_79_22 : rowsJ2 79 80 48 360 ≤ 36584579318567 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1827 c22250R_79_23 (by norm_num)

theorem c22250R_79_21 : rowsJ2 79 80 47 360 ≤ 36680462729413 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1826 c22250R_79_22 (by norm_num)

theorem c22250R_79_20 : rowsJ2 79 80 46 360 ≤ 36680462729413 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1825 c22250R_79_21 (by norm_num)

theorem c22250R_79_19 : rowsJ2 79 80 45 360 ≤ 36680462729413 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1824 c22250R_79_20 (by norm_num)

theorem c22250R_79_18 : rowsJ2 79 80 44 360 ≤ 36680462729413 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1823 c22250R_79_19 (by norm_num)

theorem c22250R_79_17 : rowsJ2 79 80 42 360 ≤ 36680462729413 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1822 c22250R_79_18 (by norm_num)

theorem c22250R_79_16 : rowsJ2 79 80 40 360 ≤ 36680462729413 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1821 c22250R_79_17 (by norm_num)

theorem c22250R_79_15 : rowsJ2 79 80 38 360 ≤ 36680462729413 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1820 c22250R_79_16 (by norm_num)

theorem c22250R_79_14 : rowsJ2 79 80 36 360 ≤ 36680462729413 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1819 c22250R_79_15 (by norm_num)

theorem c22250R_79_13 : rowsJ2 79 80 34 360 ≤ 36680462729413 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1818 c22250R_79_14 (by norm_num)

theorem c22250R_79_12 : rowsJ2 79 80 32 360 ≤ 36680462729413 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1817 c22250R_79_13 (by norm_num)

theorem c22250R_79_11 : rowsJ2 79 80 30 360 ≤ 36680462729413 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1816 c22250R_79_12 (by norm_num)

theorem c22250R_79_10 : rowsJ2 79 80 29 360 ≤ 36680462729413 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1815 c22250R_79_11 (by norm_num)

theorem c22250R_79_9 : rowsJ2 79 80 28 360 ≤ 36680462729413 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1814 c22250R_79_10 (by norm_num)

theorem c22250R_79_8 : rowsJ2 79 80 27 360 ≤ 36680462729413 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1813 c22250R_79_9 (by norm_num)

theorem c22250R_79_7 : rowsJ2 79 80 26 360 ≤ 36681175630071 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1812 c22250R_79_8 (by norm_num)

theorem c22250R_79_6 : rowsJ2 79 80 25 360 ≤ 36681887246599 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1811 c22250R_79_7 (by norm_num)

theorem c22250R_79_5 : rowsJ2 79 80 24 360 ≤ 36683308329249 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1810 c22250R_79_6 (by norm_num)

theorem c22250R_79_4 : rowsJ2 79 80 23 360 ≤ 36684727838811 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1809 c22250R_79_5 (by norm_num)

theorem c22250R_79_3 : rowsJ2 79 80 22 360 ≤ 36686855217957 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1808 c22250R_79_4 (by norm_num)

theorem c22250R_79_2 : rowsJ2 79 80 21 360 ≤ 36688981732003 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1807 c22250R_79_3 (by norm_num)

theorem c22250R_79_1 : rowsJ2 79 80 18 360 ≤ 36690398156680 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1806 c22250R_79_2 (by norm_num)

theorem c22250R_79_0 : rowsJ2 79 80 0 360 ≤ 37002459505047 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22250R_1805 c22250R_79_1 (by norm_num)

theorem hr22250R_79 : rows2 79 80 ≤ 37002459505047 := rows2_le_of_rowsJ2 79 80 c22250R_79_0

theorem c22250R_80_50 : rowsJ2 80 81 78 360 ≤ 59275780916 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1908 rows22250R_1909 (by norm_num)

theorem c22250R_80_49 : rowsJ2 80 81 76 360 ≤ 59275780916 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1907 c22250R_80_50 (by norm_num)

theorem c22250R_80_48 : rowsJ2 80 81 75 360 ≤ 59275780916 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1906 c22250R_80_49 (by norm_num)

theorem c22250R_80_47 : rowsJ2 80 81 74 360 ≤ 59275780916 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1905 c22250R_80_48 (by norm_num)

theorem c22250R_80_46 : rowsJ2 80 81 73 360 ≤ 59275780916 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1904 c22250R_80_47 (by norm_num)

theorem c22250R_80_45 : rowsJ2 80 81 72 360 ≤ 109416720016 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1903 c22250R_80_46 (by norm_num)

theorem c22250R_80_44 : rowsJ2 80 81 71 360 ≤ 208270586817 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1902 c22250R_80_45 (by norm_num)

theorem c22250R_80_43 : rowsJ2 80 81 70 360 ≤ 403761857546 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1901 c22250R_80_44 (by norm_num)

theorem c22250R_80_42 : rowsJ2 80 81 69 360 ≤ 646769707227 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1900 c22250R_80_43 (by norm_num)

theorem c22250R_80_41 : rowsJ2 80 81 68 360 ≤ 984487886988 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1899 c22250R_80_42 (by norm_num)

theorem c22250R_80_40 : rowsJ2 80 81 67 360 ≤ 1417543497846 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1898 c22250R_80_41 (by norm_num)

theorem c22250R_80_39 : rowsJ2 80 81 66 360 ≤ 1992741918482 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1897 c22250R_80_40 (by norm_num)

theorem c22250R_80_38 : rowsJ2 80 81 65 360 ≤ 2711087941360 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1896 c22250R_80_39 (by norm_num)

theorem c22250R_80_37 : rowsJ2 80 81 64 360 ≤ 3619094081840 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1895 c22250R_80_38 (by norm_num)

theorem c22250R_80_36 : rowsJ2 80 81 63 360 ≤ 4667594103157 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1894 c22250R_80_37 (by norm_num)

theorem c22250R_80_35 : rowsJ2 80 81 62 360 ≤ 5902560834691 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1893 c22250R_80_36 (by norm_num)

theorem c22250R_80_34 : rowsJ2 80 81 61 360 ≤ 7275724074468 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1892 c22250R_80_35 (by norm_num)

theorem c22250R_80_33 : rowsJ2 80 81 60 360 ≤ 8832553761137 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1891 c22250R_80_34 (by norm_num)

theorem c22250R_80_32 : rowsJ2 80 81 59 360 ≤ 10525628983009 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1890 c22250R_80_33 (by norm_num)

theorem c22250R_80_31 : rowsJ2 80 81 58 360 ≤ 12399953343169 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1889 c22250R_80_32 (by norm_num)

theorem c22250R_80_30 : rowsJ2 80 81 57 360 ≤ 14408910867548 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1888 c22250R_80_31 (by norm_num)

theorem c22250R_80_29 : rowsJ2 80 81 56 360 ≤ 16597075241050 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1887 c22250R_80_30 (by norm_num)

theorem c22250R_80_28 : rowsJ2 80 81 55 360 ≤ 18966385070382 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1886 c22250R_80_29 (by norm_num)

theorem c22250R_80_27 : rowsJ2 80 81 54 360 ≤ 21276801540983 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1885 c22250R_80_28 (by norm_num)

theorem c22250R_80_26 : rowsJ2 80 81 53 360 ≤ 23489774857659 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1884 c22250R_80_27 (by norm_num)

theorem c22250R_80_25 : rowsJ2 80 81 52 360 ≤ 25464778704427 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1883 c22250R_80_26 (by norm_num)

theorem c22250R_80_24 : rowsJ2 80 81 51 360 ≤ 27020131431788 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1882 c22250R_80_25 (by norm_num)

theorem c22250R_80_23 : rowsJ2 80 81 50 360 ≤ 28214414779236 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1881 c22250R_80_24 (by norm_num)

theorem c22250R_80_22 : rowsJ2 80 81 49 360 ≤ 29008470546752 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1880 c22250R_80_23 (by norm_num)

theorem c22250R_80_21 : rowsJ2 80 81 48 360 ≤ 29434893780375 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1879 c22250R_80_22 (by norm_num)

theorem c22250R_80_20 : rowsJ2 80 81 47 360 ≤ 29530038482906 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1878 c22250R_80_21 (by norm_num)

theorem c22250R_80_19 : rowsJ2 80 81 46 360 ≤ 29530038482906 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1877 c22250R_80_20 (by norm_num)

theorem c22250R_80_18 : rowsJ2 80 81 45 360 ≤ 29530038482906 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1876 c22250R_80_19 (by norm_num)

theorem c22250R_80_17 : rowsJ2 80 81 44 360 ≤ 29530038482906 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1875 c22250R_80_18 (by norm_num)

theorem c22250R_80_16 : rowsJ2 80 81 42 360 ≤ 29530038482906 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1874 c22250R_80_17 (by norm_num)

theorem c22250R_80_15 : rowsJ2 80 81 40 360 ≤ 29530038482906 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1873 c22250R_80_16 (by norm_num)

theorem c22250R_80_14 : rowsJ2 80 81 38 360 ≤ 29530038482906 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1872 c22250R_80_15 (by norm_num)

theorem c22250R_80_13 : rowsJ2 80 81 35 360 ≤ 29530038482906 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1871 c22250R_80_14 (by norm_num)

theorem c22250R_80_12 : rowsJ2 80 81 33 360 ≤ 29530038482906 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1870 c22250R_80_13 (by norm_num)

theorem c22250R_80_11 : rowsJ2 80 81 31 360 ≤ 29530038482906 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1869 c22250R_80_12 (by norm_num)

theorem c22250R_80_10 : rowsJ2 80 81 29 360 ≤ 29530038482906 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1868 c22250R_80_11 (by norm_num)

theorem c22250R_80_9 : rowsJ2 80 81 28 360 ≤ 29530038482906 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1867 c22250R_80_10 (by norm_num)

theorem c22250R_80_8 : rowsJ2 80 81 27 360 ≤ 29530038482906 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1866 c22250R_80_9 (by norm_num)

theorem c22250R_80_7 : rowsJ2 80 81 26 360 ≤ 29530745891210 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1865 c22250R_80_8 (by norm_num)

theorem c22250R_80_6 : rowsJ2 80 81 25 360 ≤ 29532168891070 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1864 c22250R_80_7 (by norm_num)

theorem c22250R_80_5 : rowsJ2 80 81 24 360 ≤ 29534294727807 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1863 c22250R_80_6 (by norm_num)

theorem c22250R_80_4 : rowsJ2 80 81 23 360 ≤ 29537132805741 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1862 c22250R_80_5 (by norm_num)

theorem c22250R_80_3 : rowsJ2 80 81 22 360 ≤ 29540671986741 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1861 c22250R_80_4 (by norm_num)

theorem c22250R_80_2 : rowsJ2 80 81 20 360 ≤ 29547754833961 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1860 c22250R_80_3 (by norm_num)

theorem c22250R_80_1 : rowsJ2 80 81 18 360 ≤ 29548467729408 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1859 c22250R_80_2 (by norm_num)

theorem c22250R_80_0 : rowsJ2 80 81 0 360 ≤ 29801815550026 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22250R_1858 c22250R_80_1 (by norm_num)

theorem hr22250R_80 : rows2 80 81 ≤ 29801815550026 := rows2_le_of_rowsJ2 80 81 c22250R_80_0

theorem c22250R_81_50 : rowsJ2 81 82 79 360 ≤ 234566865294 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1960 rows22250R_1961 (by norm_num)

theorem c22250R_81_49 : rowsJ2 81 82 77 360 ≤ 234566865294 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1959 c22250R_81_50 (by norm_num)

theorem c22250R_81_48 : rowsJ2 81 82 75 360 ≤ 234566865294 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1958 c22250R_81_49 (by norm_num)

theorem c22250R_81_47 : rowsJ2 81 82 74 360 ≤ 234566865294 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1957 c22250R_81_48 (by norm_num)

theorem c22250R_81_46 : rowsJ2 81 82 73 360 ≤ 234566865294 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1956 c22250R_81_47 (by norm_num)

theorem c22250R_81_45 : rowsJ2 81 82 72 360 ≤ 234566865294 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1955 c22250R_81_46 (by norm_num)

theorem c22250R_81_44 : rowsJ2 81 82 71 360 ≤ 234566865294 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1954 c22250R_81_45 (by norm_num)

theorem c22250R_81_43 : rowsJ2 81 82 70 360 ≤ 283465233385 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1953 c22250R_81_44 (by norm_num)

theorem c22250R_81_42 : rowsJ2 81 82 69 360 ≤ 379906993789 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1952 c22250R_81_43 (by norm_num)

theorem c22250R_81_41 : rowsJ2 81 82 68 360 ≤ 524181956196 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1951 c22250R_81_42 (by norm_num)

theorem c22250R_81_40 : rowsJ2 81 82 67 360 ≤ 763511198038 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1950 c22250R_81_41 (by norm_num)

theorem c22250R_81_39 : rowsJ2 81 82 66 360 ≤ 1098516962261 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1949 c22250R_81_40 (by norm_num)

theorem c22250R_81_38 : rowsJ2 81 82 65 360 ≤ 1576046673057 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1948 c22250R_81_39 (by norm_num)

theorem c22250R_81_37 : rowsJ2 81 82 64 360 ≤ 2197109226473 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1947 c22250R_81_38 (by norm_num)

theorem c22250R_81_36 : rowsJ2 81 82 63 360 ≤ 2958057565298 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1946 c22250R_81_37 (by norm_num)

theorem c22250R_81_35 : rowsJ2 81 82 62 360 ≤ 3860003022816 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1945 c22250R_81_36 (by norm_num)

theorem c22250R_81_34 : rowsJ2 81 82 61 360 ≤ 4899520623424 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1944 c22250R_81_35 (by norm_num)

theorem c22250R_81_33 : rowsJ2 81 82 60 360 ≤ 6077822526124 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1943 c22250R_81_34 (by norm_num)

theorem c22250R_81_32 : rowsJ2 81 82 59 360 ≤ 7391697997660 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1942 c22250R_81_33 (by norm_num)

theorem c22250R_81_31 : rowsJ2 81 82 58 360 ≤ 8842459207339 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1941 c22250R_81_32 (by norm_num)

theorem c22250R_81_30 : rowsJ2 81 82 57 360 ≤ 10427102947227 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1940 c22250R_81_31 (by norm_num)

theorem c22250R_81_29 : rowsJ2 81 82 56 360 ≤ 12147041361497 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1939 c22250R_81_30 (by norm_num)

theorem c22250R_81_28 : rowsJ2 81 82 55 360 ≤ 14046899512771 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1938 c22250R_81_29 (by norm_num)

theorem c22250R_81_27 : rowsJ2 81 82 54 360 ≤ 16034019022233 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1937 c22250R_81_28 (by norm_num)

theorem c22250R_81_26 : rowsJ2 81 82 53 360 ≤ 18014316800373 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1936 c22250R_81_27 (by norm_num)

theorem c22250R_81_25 : rowsJ2 81 82 52 360 ≤ 19804439935867 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1935 c22250R_81_26 (by norm_num)

theorem c22250R_81_24 : rowsJ2 81 82 51 360 ≤ 21263922024373 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1934 c22250R_81_25 (by norm_num)

theorem c22250R_81_23 : rowsJ2 81 82 50 360 ≤ 22407725507467 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1933 c22250R_81_24 (by norm_num)

theorem c22250R_81_22 : rowsJ2 81 82 49 360 ≤ 23195710453908 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1932 c22250R_81_23 (by norm_num)

theorem c22250R_81_21 : rowsJ2 81 82 48 360 ≤ 23618873539743 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1931 c22250R_81_22 (by norm_num)

theorem c22250R_81_20 : rowsJ2 81 82 47 360 ≤ 23713290829303 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1930 c22250R_81_21 (by norm_num)

theorem c22250R_81_19 : rowsJ2 81 82 46 360 ≤ 23713290829303 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1929 c22250R_81_20 (by norm_num)

theorem c22250R_81_18 : rowsJ2 81 82 45 360 ≤ 23713290829303 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1928 c22250R_81_19 (by norm_num)

theorem c22250R_81_17 : rowsJ2 81 82 44 360 ≤ 23713290829303 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1927 c22250R_81_18 (by norm_num)

theorem c22250R_81_16 : rowsJ2 81 82 43 360 ≤ 23713290829303 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1926 c22250R_81_17 (by norm_num)

theorem c22250R_81_15 : rowsJ2 81 82 42 360 ≤ 23713290829303 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1925 c22250R_81_16 (by norm_num)

theorem c22250R_81_14 : rowsJ2 81 82 40 360 ≤ 23713290829303 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1924 c22250R_81_15 (by norm_num)

theorem c22250R_81_13 : rowsJ2 81 82 37 360 ≤ 23713290829303 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1923 c22250R_81_14 (by norm_num)

theorem c22250R_81_12 : rowsJ2 81 82 34 360 ≤ 23713290829303 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1922 c22250R_81_13 (by norm_num)

theorem c22250R_81_11 : rowsJ2 81 82 32 360 ≤ 23713290829303 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1921 c22250R_81_12 (by norm_num)

theorem c22250R_81_10 : rowsJ2 81 82 30 360 ≤ 23713290829303 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1920 c22250R_81_11 (by norm_num)

theorem c22250R_81_9 : rowsJ2 81 82 28 360 ≤ 23713290829303 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1919 c22250R_81_10 (by norm_num)

theorem c22250R_81_8 : rowsJ2 81 82 27 360 ≤ 23713290829303 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1918 c22250R_81_9 (by norm_num)

theorem c22250R_81_7 : rowsJ2 81 82 26 360 ≤ 23713992829234 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1917 c22250R_81_8 (by norm_num)

theorem c22250R_81_6 : rowsJ2 81 82 25 360 ≤ 23715404949785 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1916 c22250R_81_7 (by norm_num)

theorem c22250R_81_5 : rowsJ2 81 82 24 360 ≤ 23718235558434 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1915 c22250R_81_6 (by norm_num)

theorem c22250R_81_4 : rowsJ2 81 82 23 360 ≤ 23721771925058 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1914 c22250R_81_5 (by norm_num)

theorem c22250R_81_3 : rowsJ2 81 82 22 360 ≤ 23726722381072 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1913 c22250R_81_4 (by norm_num)

theorem c22250R_81_2 : rowsJ2 81 82 20 360 ≤ 23737343244115 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1912 c22250R_81_3 (by norm_num)

theorem c22250R_81_1 : rowsJ2 81 82 18 360 ≤ 23738768568847 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1911 c22250R_81_2 (by norm_num)

theorem c22250R_81_0 : rowsJ2 81 82 0 360 ≤ 23940391033286 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22250R_1910 c22250R_81_1 (by norm_num)

theorem hr22250R_81 : rows2 81 82 ≤ 23940391033286 := rows2_le_of_rowsJ2 81 82 c22250R_81_0

theorem c22250R_82_49 : rowsJ2 82 83 80 360 ≤ 595070552957 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_2011 rows22250R_2012 (by norm_num)

theorem c22250R_82_48 : rowsJ2 82 83 78 360 ≤ 595070552957 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_2010 c22250R_82_49 (by norm_num)

theorem c22250R_82_47 : rowsJ2 82 83 76 360 ≤ 595070552957 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_2009 c22250R_82_48 (by norm_num)

theorem c22250R_82_46 : rowsJ2 82 83 74 360 ≤ 595070552957 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_2008 c22250R_82_47 (by norm_num)

theorem c22250R_82_45 : rowsJ2 82 83 73 360 ≤ 595070552957 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_2007 c22250R_82_46 (by norm_num)

theorem c22250R_82_44 : rowsJ2 82 83 72 360 ≤ 595070552957 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_2006 c22250R_82_45 (by norm_num)

theorem c22250R_82_43 : rowsJ2 82 83 71 360 ≤ 595070552957 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_2005 c22250R_82_44 (by norm_num)

theorem c22250R_82_42 : rowsJ2 82 83 70 360 ≤ 595070552957 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_2004 c22250R_82_43 (by norm_num)

theorem c22250R_82_41 : rowsJ2 82 83 69 360 ≤ 595070552957 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_2003 c22250R_82_42 (by norm_num)

theorem c22250R_82_40 : rowsJ2 82 83 68 360 ≤ 642791379199 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_2002 c22250R_82_41 (by norm_num)

theorem c22250R_82_39 : rowsJ2 82 83 67 360 ≤ 738520111107 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_2001 c22250R_82_40 (by norm_num)

theorem c22250R_82_38 : rowsJ2 82 83 66 360 ≤ 929521609743 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_2000 c22250R_82_39 (by norm_num)

theorem c22250R_82_37 : rowsJ2 82 83 65 360 ≤ 1216423519906 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1999 c22250R_82_38 (by norm_num)

theorem c22250R_82_36 : rowsJ2 82 83 64 360 ≤ 1646131703326 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1998 c22250R_82_37 (by norm_num)

theorem c22250R_82_35 : rowsJ2 82 83 63 360 ≤ 2169833229800 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1997 c22250R_82_36 (by norm_num)

theorem c22250R_82_34 : rowsJ2 82 83 62 360 ≤ 2833834427979 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1996 c22250R_82_35 (by norm_num)

theorem c22250R_82_33 : rowsJ2 82 83 61 360 ≤ 3590174213727 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1995 c22250R_82_34 (by norm_num)

theorem c22250R_82_32 : rowsJ2 82 83 60 360 ≤ 4484597816831 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1994 c22250R_82_33 (by norm_num)

theorem c22250R_82_31 : rowsJ2 82 83 59 360 ≤ 5469950012429 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1993 c22250R_82_32 (by norm_num)

theorem c22250R_82_30 : rowsJ2 82 83 58 360 ≤ 6591452795643 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1992 c22250R_82_31 (by norm_num)

theorem c22250R_82_29 : rowsJ2 82 83 57 360 ≤ 7802712938602 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1991 c22250R_82_30 (by norm_num)

theorem c22250R_82_28 : rowsJ2 82 83 56 360 ≤ 9148466605560 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1990 c22250R_82_29 (by norm_num)

theorem c22250R_82_27 : rowsJ2 82 83 55 360 ≤ 10630107210117 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1989 c22250R_82_28 (by norm_num)

theorem c22250R_82_26 : rowsJ2 82 83 54 360 ≤ 12292327752328 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1988 c22250R_82_27 (by norm_num)

theorem c22250R_82_25 : rowsJ2 82 83 53 360 ≤ 13996605217378 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1987 c22250R_82_26 (by norm_num)

theorem c22250R_82_24 : rowsJ2 82 83 52 360 ≤ 15601134627022 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1986 c22250R_82_25 (by norm_num)

theorem c22250R_82_23 : rowsJ2 82 83 51 360 ≤ 16922604327369 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1985 c22250R_82_24 (by norm_num)

theorem c22250R_82_22 : rowsJ2 82 83 50 360 ≤ 18015859069029 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1984 c22250R_82_23 (by norm_num)

theorem c22250R_82_21 : rowsJ2 82 83 49 360 ≤ 18797865316986 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1983 c22250R_82_22 (by norm_num)

theorem c22250R_82_20 : rowsJ2 82 83 48 360 ≤ 19217817726637 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1982 c22250R_82_21 (by norm_num)

theorem c22250R_82_19 : rowsJ2 82 83 47 360 ≤ 19311518641464 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1981 c22250R_82_20 (by norm_num)

theorem c22250R_82_18 : rowsJ2 82 83 46 360 ≤ 19311518641464 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1980 c22250R_82_19 (by norm_num)

theorem c22250R_82_17 : rowsJ2 82 83 45 360 ≤ 19311518641464 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1979 c22250R_82_18 (by norm_num)

theorem c22250R_82_16 : rowsJ2 82 83 44 360 ≤ 19311518641464 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1978 c22250R_82_17 (by norm_num)

theorem c22250R_82_15 : rowsJ2 82 83 43 360 ≤ 19311518641464 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1977 c22250R_82_16 (by norm_num)

theorem c22250R_82_14 : rowsJ2 82 83 41 360 ≤ 19311518641464 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1976 c22250R_82_15 (by norm_num)

theorem c22250R_82_13 : rowsJ2 82 83 39 360 ≤ 19311518641464 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1975 c22250R_82_14 (by norm_num)

theorem c22250R_82_12 : rowsJ2 82 83 36 360 ≤ 19311518641464 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1974 c22250R_82_13 (by norm_num)

theorem c22250R_82_11 : rowsJ2 82 83 33 360 ≤ 19311518641464 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1973 c22250R_82_12 (by norm_num)

theorem c22250R_82_10 : rowsJ2 82 83 31 360 ≤ 19311518641464 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1972 c22250R_82_11 (by norm_num)

theorem c22250R_82_9 : rowsJ2 82 83 29 360 ≤ 19311518641464 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1971 c22250R_82_10 (by norm_num)

theorem c22250R_82_8 : rowsJ2 82 83 27 360 ≤ 19311518641464 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1970 c22250R_82_9 (by norm_num)

theorem c22250R_82_7 : rowsJ2 82 83 26 360 ≤ 19312215315093 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1969 c22250R_82_8 (by norm_num)

theorem c22250R_82_6 : rowsJ2 82 83 25 360 ≤ 19313616721425 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1968 c22250R_82_7 (by norm_num)

theorem c22250R_82_5 : rowsJ2 82 83 24 360 ≤ 19316425853325 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1967 c22250R_82_6 (by norm_num)

theorem c22250R_82_4 : rowsJ2 82 83 23 360 ≤ 19320660771585 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1966 c22250R_82_5 (by norm_num)

theorem c22250R_82_3 : rowsJ2 82 83 22 360 ≤ 19326298142607 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1965 c22250R_82_4 (by norm_num)

theorem c22250R_82_2 : rowsJ2 82 83 20 360 ≤ 19339732825004 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1964 c22250R_82_3 (by norm_num)

theorem c22250R_82_1 : rowsJ2 82 83 18 360 ≤ 19342593374396 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1963 c22250R_82_2 (by norm_num)

theorem c22250R_82_0 : rowsJ2 82 83 0 360 ≤ 19499556464277 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22250R_1962 c22250R_82_1 (by norm_num)

theorem hr22250R_82 : rows2 82 83 ≤ 19499556464277 := rows2_le_of_rowsJ2 82 83 c22250R_82_0

theorem c22250R_83_48 : rowsJ2 83 84 81 360 ≤ 1659088626345 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2061 rows22250R_2062 (by norm_num)

theorem c22250R_83_47 : rowsJ2 83 84 79 360 ≤ 1717025333274 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2060 c22250R_83_48 (by norm_num)

theorem c22250R_83_46 : rowsJ2 83 84 77 360 ≤ 1717025333274 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2059 c22250R_83_47 (by norm_num)

theorem c22250R_83_45 : rowsJ2 83 84 75 360 ≤ 1717025333274 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2058 c22250R_83_46 (by norm_num)

theorem c22250R_83_44 : rowsJ2 83 84 73 360 ≤ 1717025333274 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2057 c22250R_83_45 (by norm_num)

theorem c22250R_83_43 : rowsJ2 83 84 72 360 ≤ 1717025333274 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2056 c22250R_83_44 (by norm_num)

theorem c22250R_83_42 : rowsJ2 83 84 71 360 ≤ 1717025333274 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2055 c22250R_83_43 (by norm_num)

theorem c22250R_83_41 : rowsJ2 83 84 70 360 ≤ 1717025333274 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2054 c22250R_83_42 (by norm_num)

theorem c22250R_83_40 : rowsJ2 83 84 69 360 ≤ 1717025333274 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2053 c22250R_83_41 (by norm_num)

theorem c22250R_83_39 : rowsJ2 83 84 68 360 ≤ 1717025333274 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2052 c22250R_83_40 (by norm_num)

theorem c22250R_83_38 : rowsJ2 83 84 67 360 ≤ 1764792309023 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2051 c22250R_83_39 (by norm_num)

theorem c22250R_83_37 : rowsJ2 83 84 66 360 ≤ 1860620642110 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2050 c22250R_83_38 (by norm_num)

theorem c22250R_83_36 : rowsJ2 83 84 65 360 ≤ 2051835128482 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2049 c22250R_83_37 (by norm_num)

theorem c22250R_83_35 : rowsJ2 83 84 64 360 ≤ 2339078761884 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2048 c22250R_83_36 (by norm_num)

theorem c22250R_83_34 : rowsJ2 83 84 63 360 ≤ 2719871127078 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2047 c22250R_83_35 (by norm_num)

theorem c22250R_83_33 : rowsJ2 83 84 62 360 ≤ 3194924464972 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2046 c22250R_83_34 (by norm_num)

theorem c22250R_83_32 : rowsJ2 83 84 61 360 ≤ 3761908488690 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2045 c22250R_83_33 (by norm_num)

theorem c22250R_83_31 : rowsJ2 83 84 60 360 ≤ 4421603422160 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2044 c22250R_83_32 (by norm_num)

theorem c22250R_83_30 : rowsJ2 83 84 59 360 ≤ 5171823619556 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2043 c22250R_83_31 (by norm_num)

theorem c22250R_83_29 : rowsJ2 83 84 58 360 ≤ 6013416566460 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2042 c22250R_83_30 (by norm_num)

theorem c22250R_83_28 : rowsJ2 83 84 57 360 ≤ 6944336535583 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2041 c22250R_83_29 (by norm_num)

theorem c22250R_83_27 : rowsJ2 83 84 56 360 ≤ 7965498082409 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2040 c22250R_83_28 (by norm_num)

theorem c22250R_83_26 : rowsJ2 83 84 55 360 ≤ 9121703530711 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2039 c22250R_83_27 (by norm_num)

theorem c22250R_83_25 : rowsJ2 83 84 54 360 ≤ 10414337392144 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2038 c22250R_83_26 (by norm_num)

theorem c22250R_83_24 : rowsJ2 83 84 53 360 ≤ 11841224847252 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2037 c22250R_83_25 (by norm_num)

theorem c22250R_83_23 : rowsJ2 83 84 52 360 ≤ 13216926842375 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2036 c22250R_83_24 (by norm_num)

theorem c22250R_83_22 : rowsJ2 83 84 51 360 ≤ 14399845864374 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2035 c22250R_83_23 (by norm_num)

theorem c22250R_83_21 : rowsJ2 83 84 50 360 ≤ 15400483353013 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2034 c22250R_83_22 (by norm_num)

theorem c22250R_83_20 : rowsJ2 83 84 49 360 ≤ 16176600943977 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2033 c22250R_83_21 (by norm_num)

theorem c22250R_83_19 : rowsJ2 83 84 48 360 ≤ 16593391031462 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2032 c22250R_83_20 (by norm_num)

theorem c22250R_83_18 : rowsJ2 83 84 47 360 ≤ 16686386360433 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2031 c22250R_83_19 (by norm_num)

theorem c22250R_83_17 : rowsJ2 83 84 46 360 ≤ 16686386360433 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2030 c22250R_83_18 (by norm_num)

theorem c22250R_83_16 : rowsJ2 83 84 45 360 ≤ 16686386360433 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2029 c22250R_83_17 (by norm_num)

theorem c22250R_83_15 : rowsJ2 83 84 44 360 ≤ 16686386360433 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2028 c22250R_83_16 (by norm_num)

theorem c22250R_83_14 : rowsJ2 83 84 43 360 ≤ 16686386360433 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2027 c22250R_83_15 (by norm_num)

theorem c22250R_83_13 : rowsJ2 83 84 42 360 ≤ 16686386360433 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2026 c22250R_83_14 (by norm_num)

theorem c22250R_83_12 : rowsJ2 83 84 40 360 ≤ 16686386360433 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2025 c22250R_83_13 (by norm_num)

theorem c22250R_83_11 : rowsJ2 83 84 37 360 ≤ 17802003204394 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2024 c22250R_83_12 (by norm_num)

theorem c22250R_83_10 : rowsJ2 83 84 34 360 ≤ 17876554120681 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2023 c22250R_83_11 (by norm_num)

theorem c22250R_83_9 : rowsJ2 83 84 31 360 ≤ 17876554120681 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2022 c22250R_83_10 (by norm_num)

theorem c22250R_83_8 : rowsJ2 83 84 29 360 ≤ 17876554120681 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2021 c22250R_83_9 (by norm_num)

theorem c22250R_83_7 : rowsJ2 83 84 27 360 ≤ 17876554120681 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2020 c22250R_83_8 (by norm_num)

theorem c22250R_83_6 : rowsJ2 83 84 25 360 ≤ 17877254792063 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2019 c22250R_83_7 (by norm_num)

theorem c22250R_83_5 : rowsJ2 83 84 24 360 ≤ 17878664492111 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2018 c22250R_83_6 (by norm_num)

theorem c22250R_83_4 : rowsJ2 83 84 23 360 ≤ 17881490767780 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2017 c22250R_83_5 (by norm_num)

theorem c22250R_83_3 : rowsJ2 83 84 22 360 ≤ 17885752335321 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2016 c22250R_83_4 (by norm_num)

theorem c22250R_83_2 : rowsJ2 83 84 20 360 ≤ 17897836069832 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2015 c22250R_83_3 (by norm_num)

theorem c22250R_83_1 : rowsJ2 83 84 18 360 ≤ 17902859956558 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2014 c22250R_83_2 (by norm_num)

theorem c22250R_83_0 : rowsJ2 83 84 0 360 ≤ 18022302968503 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22250R_2013 c22250R_83_1 (by norm_num)

theorem hr22250R_83 : rows2 83 84 ≤ 18022302968503 := rows2_le_of_rowsJ2 83 84 c22250R_83_0

theorem c22250R_84_47 : rowsJ2 84 85 82 360 ≤ 3099457634745 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2110 rows22250R_2111 (by norm_num)

theorem c22250R_84_46 : rowsJ2 84 85 80 360 ≤ 3328765103884 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2109 c22250R_84_47 (by norm_num)

theorem c22250R_84_45 : rowsJ2 84 85 78 360 ≤ 3328765103884 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2108 c22250R_84_46 (by norm_num)

theorem c22250R_84_44 : rowsJ2 84 85 76 360 ≤ 3328765103884 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2107 c22250R_84_45 (by norm_num)

theorem c22250R_84_43 : rowsJ2 84 85 74 360 ≤ 3328765103884 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2106 c22250R_84_44 (by norm_num)

theorem c22250R_84_42 : rowsJ2 84 85 72 360 ≤ 3328765103884 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2105 c22250R_84_43 (by norm_num)

theorem c22250R_84_41 : rowsJ2 84 85 71 360 ≤ 3328765103884 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2104 c22250R_84_42 (by norm_num)

theorem c22250R_84_40 : rowsJ2 84 85 70 360 ≤ 3328765103884 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2103 c22250R_84_41 (by norm_num)

theorem c22250R_84_39 : rowsJ2 84 85 69 360 ≤ 3328765103884 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2102 c22250R_84_40 (by norm_num)

theorem c22250R_84_38 : rowsJ2 84 85 68 360 ≤ 3328765103884 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2101 c22250R_84_39 (by norm_num)

theorem c22250R_84_37 : rowsJ2 84 85 67 360 ≤ 3328765103884 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2100 c22250R_84_38 (by norm_num)

theorem c22250R_84_36 : rowsJ2 84 85 66 360 ≤ 3376584490433 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2099 c22250R_84_37 (by norm_num)

theorem c22250R_84_35 : rowsJ2 84 85 65 360 ≤ 3472525122877 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2098 c22250R_84_36 (by norm_num)

theorem c22250R_84_34 : rowsJ2 84 85 64 360 ≤ 3663978217190 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2097 c22250R_84_35 (by norm_num)

theorem c22250R_84_33 : rowsJ2 84 85 63 360 ≤ 3902511306170 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2096 c22250R_84_34 (by norm_num)

theorem c22250R_84_32 : rowsJ2 84 85 62 360 ≤ 4234853457799 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2095 c22250R_84_33 (by norm_num)

theorem c22250R_84_31 : rowsJ2 84 85 61 360 ≤ 4613379109266 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2094 c22250R_84_32 (by norm_num)

theorem c22250R_84_30 : rowsJ2 84 85 60 360 ≤ 5084195625486 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2093 c22250R_84_31 (by norm_num)

theorem c22250R_84_29 : rowsJ2 84 85 59 360 ≤ 5600439367526 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2092 c22250R_84_30 (by norm_num)

theorem c22250R_84_28 : rowsJ2 84 85 58 360 ≤ 6207635521890 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2091 c22250R_84_29 (by norm_num)

theorem c22250R_84_27 : rowsJ2 84 85 57 360 ≤ 6859639238432 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2090 c22250R_84_28 (by norm_num)

theorem c22250R_84_26 : rowsJ2 84 85 56 360 ≤ 7601432250427 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2089 c22250R_84_27 (by norm_num)

theorem c22250R_84_25 : rowsJ2 84 85 55 360 ≤ 8433910051648 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2088 c22250R_84_26 (by norm_num)

theorem c22250R_84_24 : rowsJ2 84 85 54 360 ≤ 9401948515231 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2087 c22250R_84_25 (by norm_num)

theorem c22250R_84_23 : rowsJ2 84 85 53 360 ≤ 10506924201055 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2086 c22250R_84_24 (by norm_num)

theorem c22250R_84_22 : rowsJ2 84 85 52 360 ≤ 11652654673885 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2085 c22250R_84_23 (by norm_num)

theorem c22250R_84_21 : rowsJ2 84 85 51 360 ≤ 12653888124606 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2084 c22250R_84_22 (by norm_num)

theorem c22250R_84_20 : rowsJ2 84 85 50 360 ≤ 13561562260069 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2083 c22250R_84_21 (by norm_num)

theorem c22250R_84_19 : rowsJ2 84 85 49 360 ≤ 14289795611080 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2082 c22250R_84_20 (by norm_num)

theorem c22250R_84_18 : rowsJ2 84 85 48 360 ≤ 14703470646233 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2081 c22250R_84_19 (by norm_num)

theorem c22250R_84_17 : rowsJ2 84 85 47 360 ≤ 14795770936323 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2080 c22250R_84_18 (by norm_num)

theorem c22250R_84_16 : rowsJ2 84 85 46 360 ≤ 14795770936323 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2079 c22250R_84_17 (by norm_num)

theorem c22250R_84_15 : rowsJ2 84 85 45 360 ≤ 14795770936323 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2078 c22250R_84_16 (by norm_num)

theorem c22250R_84_14 : rowsJ2 84 85 44 360 ≤ 14795770936323 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2077 c22250R_84_15 (by norm_num)

theorem c22250R_84_13 : rowsJ2 84 85 43 360 ≤ 14795770936323 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2076 c22250R_84_14 (by norm_num)

theorem c22250R_84_12 : rowsJ2 84 85 42 360 ≤ 14795770936323 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2075 c22250R_84_13 (by norm_num)

theorem c22250R_84_11 : rowsJ2 84 85 40 360 ≤ 15650504600513 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2074 c22250R_84_12 (by norm_num)

theorem c22250R_84_10 : rowsJ2 84 85 37 360 ≤ 18093816032107 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2073 c22250R_84_11 (by norm_num)

theorem c22250R_84_9 : rowsJ2 84 85 34 360 ≤ 18243558941748 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2072 c22250R_84_10 (by norm_num)

theorem c22250R_84_8 : rowsJ2 84 85 31 360 ≤ 18243558941748 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2071 c22250R_84_9 (by norm_num)

theorem c22250R_84_7 : rowsJ2 84 85 29 360 ≤ 18243558941748 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2070 c22250R_84_8 (by norm_num)

theorem c22250R_84_6 : rowsJ2 84 85 27 360 ≤ 18243558941748 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2069 c22250R_84_7 (by norm_num)

theorem c22250R_84_5 : rowsJ2 84 85 25 360 ≤ 18243558941748 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2068 c22250R_84_6 (by norm_num)

theorem c22250R_84_4 : rowsJ2 84 85 23 360 ≤ 18245682183461 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2067 c22250R_84_5 (by norm_num)

theorem c22250R_84_3 : rowsJ2 84 85 22 360 ≤ 18248526405452 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2066 c22250R_84_4 (by norm_num)

theorem c22250R_84_2 : rowsJ2 84 85 20 360 ≤ 18258528087440 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2065 c22250R_84_3 (by norm_num)

theorem c22250R_84_1 : rowsJ2 84 85 18 360 ≤ 18265023695579 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2064 c22250R_84_2 (by norm_num)

theorem c22250R_84_0 : rowsJ2 84 85 0 360 ≤ 18354178758334 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22250R_2063 c22250R_84_1 (by norm_num)

theorem hr22250R_84 : rows2 84 85 ≤ 18354178758334 := rows2_le_of_rowsJ2 84 85 c22250R_84_0

theorem c22250R_85_46 : rowsJ2 85 86 84 360 ≤ 3169975825454 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2158 rows22250R_2159 (by norm_num)

theorem c22250R_85_45 : rowsJ2 85 86 82 360 ≤ 4477017698045 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2157 c22250R_85_46 (by norm_num)

theorem c22250R_85_44 : rowsJ2 85 86 80 360 ≤ 4704624057342 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2156 c22250R_85_45 (by norm_num)

theorem c22250R_85_43 : rowsJ2 85 86 77 360 ≤ 4704624057342 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2155 c22250R_85_44 (by norm_num)

theorem c22250R_85_42 : rowsJ2 85 86 75 360 ≤ 4704624057342 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2154 c22250R_85_43 (by norm_num)

theorem c22250R_85_41 : rowsJ2 85 86 73 360 ≤ 4704624057342 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2153 c22250R_85_42 (by norm_num)

theorem c22250R_85_40 : rowsJ2 85 86 71 360 ≤ 4704624057342 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2152 c22250R_85_41 (by norm_num)

theorem c22250R_85_39 : rowsJ2 85 86 70 360 ≤ 4704624057342 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2151 c22250R_85_40 (by norm_num)

theorem c22250R_85_38 : rowsJ2 85 86 69 360 ≤ 4704624057342 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2150 c22250R_85_39 (by norm_num)

theorem c22250R_85_37 : rowsJ2 85 86 68 360 ≤ 4704624057342 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2149 c22250R_85_38 (by norm_num)

theorem c22250R_85_36 : rowsJ2 85 86 67 360 ≤ 4704624057342 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2148 c22250R_85_37 (by norm_num)

theorem c22250R_85_35 : rowsJ2 85 86 66 360 ≤ 4704624057342 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2147 c22250R_85_36 (by norm_num)

theorem c22250R_85_34 : rowsJ2 85 86 65 360 ≤ 4752502156939 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2146 c22250R_85_35 (by norm_num)

theorem c22250R_85_33 : rowsJ2 85 86 64 360 ≤ 4848567875544 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2145 c22250R_85_34 (by norm_num)

theorem c22250R_85_32 : rowsJ2 85 86 63 360 ≤ 4991558376671 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2144 c22250R_85_33 (by norm_num)

theorem c22250R_85_31 : rowsJ2 85 86 62 360 ≤ 5181818272846 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2143 c22250R_85_32 (by norm_num)

theorem c22250R_85_30 : rowsJ2 85 86 61 360 ≤ 5418160864046 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2142 c22250R_85_31 (by norm_num)

theorem c22250R_85_29 : rowsJ2 85 86 60 360 ≤ 5700965138267 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2141 c22250R_85_30 (by norm_num)

theorem c22250R_85_28 : rowsJ2 85 86 59 360 ≤ 6029117664468 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2140 c22250R_85_29 (by norm_num)

theorem c22250R_85_27 : rowsJ2 85 86 58 360 ≤ 6403031366001 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2139 c22250R_85_28 (by norm_num)

theorem c22250R_85_26 : rowsJ2 85 86 57 360 ≤ 6821663604410 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2138 c22250R_85_27 (by norm_num)

theorem c22250R_85_25 : rowsJ2 85 86 56 360 ≤ 7285461068141 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2137 c22250R_85_26 (by norm_num)

theorem c22250R_85_24 : rowsJ2 85 86 55 360 ≤ 7839468864161 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2136 c22250R_85_25 (by norm_num)

theorem c22250R_85_23 : rowsJ2 85 86 54 360 ≤ 8484564123169 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2135 c22250R_85_24 (by norm_num)

theorem c22250R_85_22 : rowsJ2 85 86 53 360 ≤ 9265703673161 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2134 c22250R_85_23 (by norm_num)

theorem c22250R_85_21 : rowsJ2 85 86 52 360 ≤ 10137092644299 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2133 c22250R_85_22 (by norm_num)

theorem c22250R_85_20 : rowsJ2 85 86 51 360 ≤ 10955715760090 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2132 c22250R_85_21 (by norm_num)

theorem c22250R_85_19 : rowsJ2 85 86 50 360 ≤ 11727399975031 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2131 c22250R_85_20 (by norm_num)

theorem c22250R_85_18 : rowsJ2 85 86 49 360 ≤ 12407600942040 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2130 c22250R_85_19 (by norm_num)

theorem c22250R_85_17 : rowsJ2 85 86 48 360 ≤ 12818207142682 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2129 c22250R_85_18 (by norm_num)

theorem c22250R_85_16 : rowsJ2 85 86 47 360 ≤ 12909822706135 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2128 c22250R_85_17 (by norm_num)

theorem c22250R_85_15 : rowsJ2 85 86 46 360 ≤ 12909822706135 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2127 c22250R_85_16 (by norm_num)

theorem c22250R_85_14 : rowsJ2 85 86 45 360 ≤ 12909822706135 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2126 c22250R_85_15 (by norm_num)

theorem c22250R_85_13 : rowsJ2 85 86 44 360 ≤ 12909822706135 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2125 c22250R_85_14 (by norm_num)

theorem c22250R_85_12 : rowsJ2 85 86 43 360 ≤ 12909822706135 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2124 c22250R_85_13 (by norm_num)

theorem c22250R_85_11 : rowsJ2 85 86 42 360 ≤ 12909822706135 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2123 c22250R_85_12 (by norm_num)

theorem c22250R_85_10 : rowsJ2 85 86 40 360 ≤ 15536075529847 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2122 c22250R_85_11 (by norm_num)

theorem c22250R_85_9 : rowsJ2 85 86 37 360 ≤ 19375225579975 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2121 c22250R_85_10 (by norm_num)

theorem c22250R_85_8 : rowsJ2 85 86 33 360 ≤ 19676923935748 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2120 c22250R_85_9 (by norm_num)

theorem c22250R_85_7 : rowsJ2 85 86 30 360 ≤ 19676923935748 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2119 c22250R_85_8 (by norm_num)

theorem c22250R_85_6 : rowsJ2 85 86 28 360 ≤ 19676923935748 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2118 c22250R_85_7 (by norm_num)

theorem c22250R_85_5 : rowsJ2 85 86 26 360 ≤ 19676923935748 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2117 c22250R_85_6 (by norm_num)

theorem c22250R_85_4 : rowsJ2 85 86 24 360 ≤ 19676923935748 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2116 c22250R_85_5 (by norm_num)

theorem c22250R_85_3 : rowsJ2 85 86 22 360 ≤ 19679060645159 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2115 c22250R_85_4 (by norm_num)

theorem c22250R_85_2 : rowsJ2 85 86 20 360 ≤ 19686242280055 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2114 c22250R_85_3 (by norm_num)

theorem c22250R_85_1 : rowsJ2 85 86 18 360 ≤ 19694210356864 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2113 c22250R_85_2 (by norm_num)

theorem c22250R_85_0 : rowsJ2 85 86 0 360 ≤ 19756691935818 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22250R_2112 c22250R_85_1 (by norm_num)

theorem hr22250R_85 : rows2 85 86 ≤ 19756691935818 := rows2_le_of_rowsJ2 85 86 c22250R_85_0

theorem c22250R_86_46 : rowsJ2 86 87 85 360 ≤ 3501313097605 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2206 rows22250R_2207 (by norm_num)

theorem c22250R_86_45 : rowsJ2 86 87 84 360 ≤ 4767174643648 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2205 c22250R_86_46 (by norm_num)

theorem c22250R_86_44 : rowsJ2 86 87 82 360 ≤ 6069689388729 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2204 c22250R_86_45 (by norm_num)

theorem c22250R_86_43 : rowsJ2 86 87 79 360 ≤ 6295619691576 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2203 c22250R_86_44 (by norm_num)

theorem c22250R_86_42 : rowsJ2 86 87 76 360 ≤ 6295619691576 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2202 c22250R_86_43 (by norm_num)

theorem c22250R_86_41 : rowsJ2 86 87 74 360 ≤ 6295619691576 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2201 c22250R_86_42 (by norm_num)

theorem c22250R_86_40 : rowsJ2 86 87 72 360 ≤ 6295619691576 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2200 c22250R_86_41 (by norm_num)

theorem c22250R_86_39 : rowsJ2 86 87 70 360 ≤ 6295619691576 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2199 c22250R_86_40 (by norm_num)

theorem c22250R_86_38 : rowsJ2 86 87 69 360 ≤ 6295619691576 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2198 c22250R_86_39 (by norm_num)

theorem c22250R_86_37 : rowsJ2 86 87 68 360 ≤ 6295619691576 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2197 c22250R_86_38 (by norm_num)

theorem c22250R_86_36 : rowsJ2 86 87 67 360 ≤ 6295619691576 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2196 c22250R_86_37 (by norm_num)

theorem c22250R_86_35 : rowsJ2 86 87 66 360 ≤ 6295619691576 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2195 c22250R_86_36 (by norm_num)

theorem c22250R_86_34 : rowsJ2 86 87 65 360 ≤ 6295619691576 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2194 c22250R_86_35 (by norm_num)

theorem c22250R_86_33 : rowsJ2 86 87 64 360 ≤ 6343562852509 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2193 c22250R_86_34 (by norm_num)

theorem c22250R_86_32 : rowsJ2 86 87 63 360 ≤ 6391398349470 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2192 c22250R_86_33 (by norm_num)

theorem c22250R_86_31 : rowsJ2 86 87 62 360 ≤ 6486342104023 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2191 c22250R_86_32 (by norm_num)

theorem c22250R_86_30 : rowsJ2 86 87 61 360 ≤ 6581104821322 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2190 c22250R_86_31 (by norm_num)

theorem c22250R_86_29 : rowsJ2 86 87 60 360 ≤ 6722217904809 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2189 c22250R_86_30 (by norm_num)

theorem c22250R_86_28 : rowsJ2 86 87 59 360 ≤ 6863109753277 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2188 c22250R_86_29 (by norm_num)

theorem c22250R_86_27 : rowsJ2 86 87 58 360 ≤ 7049668684704 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2187 c22250R_86_28 (by norm_num)

theorem c22250R_86_26 : rowsJ2 86 87 57 360 ≤ 7235998511949 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2186 c22250R_86_27 (by norm_num)

theorem c22250R_86_25 : rowsJ2 86 87 56 360 ≤ 7467384746231 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2185 c22250R_86_26 (by norm_num)

theorem c22250R_86_24 : rowsJ2 86 87 55 360 ≤ 7744245924126 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2184 c22250R_86_25 (by norm_num)

theorem c22250R_86_23 : rowsJ2 86 87 54 360 ≤ 8111697667419 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2183 c22250R_86_24 (by norm_num)

theorem c22250R_86_22 : rowsJ2 86 87 53 360 ≤ 8570599376129 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2182 c22250R_86_23 (by norm_num)

theorem c22250R_86_21 : rowsJ2 86 87 52 360 ≤ 9165996261866 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2181 c22250R_86_22 (by norm_num)

theorem c22250R_86_20 : rowsJ2 86 87 51 360 ≤ 9757777100006 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2180 c22250R_86_21 (by norm_num)

theorem c22250R_86_19 : rowsJ2 86 87 50 360 ≤ 10392781206374 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2179 c22250R_86_20 (by norm_num)

theorem c22250R_86_18 : rowsJ2 86 87 49 360 ≤ 10982029594005 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2178 c22250R_86_19 (by norm_num)

theorem c22250R_86_17 : rowsJ2 86 87 48 360 ≤ 11389612156941 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2177 c22250R_86_18 (by norm_num)

theorem c22250R_86_16 : rowsJ2 86 87 47 360 ≤ 11480553078190 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2176 c22250R_86_17 (by norm_num)

theorem c22250R_86_15 : rowsJ2 86 87 46 360 ≤ 11480553078190 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2175 c22250R_86_16 (by norm_num)

theorem c22250R_86_14 : rowsJ2 86 87 45 360 ≤ 11480553078190 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2174 c22250R_86_15 (by norm_num)

theorem c22250R_86_13 : rowsJ2 86 87 44 360 ≤ 11480553078190 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2173 c22250R_86_14 (by norm_num)

theorem c22250R_86_12 : rowsJ2 86 87 43 360 ≤ 11480553078190 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2172 c22250R_86_13 (by norm_num)

theorem c22250R_86_11 : rowsJ2 86 87 42 360 ≤ 12997114101820 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2171 c22250R_86_12 (by norm_num)

theorem c22250R_86_10 : rowsJ2 86 87 40 360 ≤ 17868176633542 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2170 c22250R_86_11 (by norm_num)

theorem c22250R_86_9 : rowsJ2 86 87 38 360 ≤ 22179941365413 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2169 c22250R_86_10 (by norm_num)

theorem c22250R_86_8 : rowsJ2 86 87 35 360 ≤ 23839494575571 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2168 c22250R_86_9 (by norm_num)

theorem c22250R_86_7 : rowsJ2 86 87 31 360 ≤ 23839494575571 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2167 c22250R_86_8 (by norm_num)

theorem c22250R_86_6 : rowsJ2 86 87 28 360 ≤ 23839494575571 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2166 c22250R_86_7 (by norm_num)

theorem c22250R_86_5 : rowsJ2 86 87 26 360 ≤ 23839494575571 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2165 c22250R_86_6 (by norm_num)

theorem c22250R_86_4 : rowsJ2 86 87 24 360 ≤ 23839494575571 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2164 c22250R_86_5 (by norm_num)

theorem c22250R_86_3 : rowsJ2 86 87 22 360 ≤ 23840208397775 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2163 c22250R_86_4 (by norm_num)

theorem c22250R_86_2 : rowsJ2 86 87 20 360 ≤ 23844528000644 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2162 c22250R_86_3 (by norm_num)

theorem c22250R_86_1 : rowsJ2 86 87 18 360 ≤ 23852523524852 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2161 c22250R_86_2 (by norm_num)

theorem c22250R_86_0 : rowsJ2 86 87 0 360 ≤ 23896491809919 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22250R_2160 c22250R_86_1 (by norm_num)

theorem hr22250R_86 : rows2 86 87 ≤ 23896491809919 := rows2_le_of_rowsJ2 86 87 c22250R_86_0

theorem c22250R_87_47 : rowsJ2 87 88 86 360 ≤ 3967495286986 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2255 rows22250R_2256 (by norm_num)

theorem c22250R_87_46 : rowsJ2 87 88 85 360 ≤ 5403174331641 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2254 c22250R_87_47 (by norm_num)

theorem c22250R_87_45 : rowsJ2 87 88 84 360 ≤ 6573834465729 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2253 c22250R_87_46 (by norm_num)

theorem c22250R_87_44 : rowsJ2 87 88 83 360 ≤ 7346556283948 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2252 c22250R_87_45 (by norm_num)

theorem c22250R_87_43 : rowsJ2 87 88 81 360 ≤ 7863634346776 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2251 c22250R_87_44 (by norm_num)

theorem c22250R_87_42 : rowsJ2 87 88 78 360 ≤ 7919876982384 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2250 c22250R_87_43 (by norm_num)

theorem c22250R_87_41 : rowsJ2 87 88 75 360 ≤ 7919876982384 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2249 c22250R_87_42 (by norm_num)

theorem c22250R_87_40 : rowsJ2 87 88 73 360 ≤ 7919876982384 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2248 c22250R_87_41 (by norm_num)

theorem c22250R_87_39 : rowsJ2 87 88 71 360 ≤ 7919876982384 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2247 c22250R_87_40 (by norm_num)

theorem c22250R_87_38 : rowsJ2 87 88 69 360 ≤ 7919876982384 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2246 c22250R_87_39 (by norm_num)

theorem c22250R_87_37 : rowsJ2 87 88 68 360 ≤ 7919876982384 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2245 c22250R_87_38 (by norm_num)

theorem c22250R_87_36 : rowsJ2 87 88 67 360 ≤ 7919876982384 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2244 c22250R_87_37 (by norm_num)

theorem c22250R_87_35 : rowsJ2 87 88 66 360 ≤ 7919876982384 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2243 c22250R_87_36 (by norm_num)

theorem c22250R_87_34 : rowsJ2 87 88 65 360 ≤ 7919876982384 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2242 c22250R_87_35 (by norm_num)

theorem c22250R_87_33 : rowsJ2 87 88 64 360 ≤ 7919876982384 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2241 c22250R_87_34 (by norm_num)

theorem c22250R_87_32 : rowsJ2 87 88 63 360 ≤ 7919876982384 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2240 c22250R_87_33 (by norm_num)

theorem c22250R_87_31 : rowsJ2 87 88 62 360 ≤ 7919876982384 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2239 c22250R_87_32 (by norm_num)

theorem c22250R_87_30 : rowsJ2 87 88 61 360 ≤ 7919876982384 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2238 c22250R_87_31 (by norm_num)

theorem c22250R_87_29 : rowsJ2 87 88 60 360 ≤ 7919876982384 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2237 c22250R_87_30 (by norm_num)

theorem c22250R_87_28 : rowsJ2 87 88 59 360 ≤ 7919876982384 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2236 c22250R_87_29 (by norm_num)

theorem c22250R_87_27 : rowsJ2 87 88 58 360 ≤ 7919876982384 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2235 c22250R_87_28 (by norm_num)

theorem c22250R_87_26 : rowsJ2 87 88 57 360 ≤ 7919876982384 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2234 c22250R_87_27 (by norm_num)

theorem c22250R_87_25 : rowsJ2 87 88 56 360 ≤ 7919876982384 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2233 c22250R_87_26 (by norm_num)

theorem c22250R_87_24 : rowsJ2 87 88 55 360 ≤ 7965223236331 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2232 c22250R_87_25 (by norm_num)

theorem c22250R_87_23 : rowsJ2 87 88 54 360 ≤ 8056306527670 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2231 c22250R_87_24 (by norm_num)

theorem c22250R_87_22 : rowsJ2 87 88 53 360 ≤ 8238320144083 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2230 c22250R_87_23 (by norm_num)

theorem c22250R_87_21 : rowsJ2 87 88 52 360 ≤ 8512106321976 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2229 c22250R_87_22 (by norm_num)

theorem c22250R_87_20 : rowsJ2 87 88 51 360 ≤ 8875660385064 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2228 c22250R_87_21 (by norm_num)

theorem c22250R_87_19 : rowsJ2 87 88 50 360 ≤ 9329897695275 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2227 c22250R_87_20 (by norm_num)

theorem c22250R_87_18 : rowsJ2 87 88 49 360 ≤ 9827742044036 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2226 c22250R_87_19 (by norm_num)

theorem c22250R_87_17 : rowsJ2 87 88 48 360 ≤ 10189474980463 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2225 c22250R_87_18 (by norm_num)

theorem c22250R_87_16 : rowsJ2 87 88 47 360 ≤ 10279751122789 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2224 c22250R_87_17 (by norm_num)

theorem c22250R_87_15 : rowsJ2 87 88 46 360 ≤ 10279751122789 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2223 c22250R_87_16 (by norm_num)

theorem c22250R_87_14 : rowsJ2 87 88 45 360 ≤ 10279751122789 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2222 c22250R_87_15 (by norm_num)

theorem c22250R_87_13 : rowsJ2 87 88 44 360 ≤ 10279751122789 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2221 c22250R_87_14 (by norm_num)

theorem c22250R_87_12 : rowsJ2 87 88 43 360 ≤ 11899418952140 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2220 c22250R_87_13 (by norm_num)

theorem c22250R_87_11 : rowsJ2 87 88 42 360 ≤ 14789997028773 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2219 c22250R_87_12 (by norm_num)

theorem c22250R_87_10 : rowsJ2 87 88 41 360 ≤ 18218640026219 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2218 c22250R_87_11 (by norm_num)

theorem c22250R_87_9 : rowsJ2 87 88 39 360 ≤ 24524372367812 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2217 c22250R_87_10 (by norm_num)

theorem c22250R_87_8 : rowsJ2 87 88 36 360 ≤ 28408139709608 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2216 c22250R_87_9 (by norm_num)

theorem c22250R_87_7 : rowsJ2 87 88 32 360 ≤ 28561652069757 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2215 c22250R_87_8 (by norm_num)

theorem c22250R_87_6 : rowsJ2 87 88 29 360 ≤ 28561652069757 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2214 c22250R_87_7 (by norm_num)

theorem c22250R_87_5 : rowsJ2 87 88 26 360 ≤ 28561652069757 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2213 c22250R_87_6 (by norm_num)

theorem c22250R_87_4 : rowsJ2 87 88 24 360 ≤ 28561652069757 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2212 c22250R_87_5 (by norm_num)

theorem c22250R_87_3 : rowsJ2 87 88 22 360 ≤ 28561652069757 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2211 c22250R_87_4 (by norm_num)

theorem c22250R_87_2 : rowsJ2 87 88 20 360 ≤ 28563817587351 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2210 c22250R_87_3 (by norm_num)

theorem c22250R_87_1 : rowsJ2 87 88 18 360 ≤ 28570384082780 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2209 c22250R_87_2 (by norm_num)

theorem c22250R_87_0 : rowsJ2 87 88 0 360 ≤ 28599564622583 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22250R_2208 c22250R_87_1 (by norm_num)

theorem hr22250R_87 : rows2 87 88 ≤ 28599564622583 := rows2_le_of_rowsJ2 87 88 c22250R_87_0

theorem c22250R_88_47 : rowsJ2 88 89 87 360 ≤ 5011677857633 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2304 rows22250R_2305 (by norm_num)

theorem c22250R_88_46 : rowsJ2 88 89 86 360 ≤ 6671510029202 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2303 c22250R_88_47 (by norm_num)

theorem c22250R_88_45 : rowsJ2 88 89 85 360 ≤ 8005522106683 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2302 c22250R_88_46 (by norm_num)

theorem c22250R_88_44 : rowsJ2 88 89 84 360 ≤ 9077071814058 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2301 c22250R_88_45 (by norm_num)

theorem c22250R_88_43 : rowsJ2 88 89 82 360 ≤ 10193430609206 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2300 c22250R_88_44 (by norm_num)

theorem c22250R_88_42 : rowsJ2 88 89 80 360 ≤ 10416081777607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2299 c22250R_88_43 (by norm_num)

theorem c22250R_88_41 : rowsJ2 88 89 77 360 ≤ 10416081777607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2298 c22250R_88_42 (by norm_num)

theorem c22250R_88_40 : rowsJ2 88 89 74 360 ≤ 10416081777607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2297 c22250R_88_41 (by norm_num)

theorem c22250R_88_39 : rowsJ2 88 89 72 360 ≤ 10416081777607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2296 c22250R_88_40 (by norm_num)

theorem c22250R_88_38 : rowsJ2 88 89 70 360 ≤ 10416081777607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2295 c22250R_88_39 (by norm_num)

theorem c22250R_88_37 : rowsJ2 88 89 68 360 ≤ 10416081777607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2294 c22250R_88_38 (by norm_num)

theorem c22250R_88_36 : rowsJ2 88 89 67 360 ≤ 10416081777607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2293 c22250R_88_37 (by norm_num)

theorem c22250R_88_35 : rowsJ2 88 89 66 360 ≤ 10416081777607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2292 c22250R_88_36 (by norm_num)

theorem c22250R_88_34 : rowsJ2 88 89 65 360 ≤ 10416081777607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2291 c22250R_88_35 (by norm_num)

theorem c22250R_88_33 : rowsJ2 88 89 64 360 ≤ 10416081777607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2290 c22250R_88_34 (by norm_num)

theorem c22250R_88_32 : rowsJ2 88 89 63 360 ≤ 10416081777607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2289 c22250R_88_33 (by norm_num)

theorem c22250R_88_31 : rowsJ2 88 89 62 360 ≤ 10416081777607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2288 c22250R_88_32 (by norm_num)

theorem c22250R_88_30 : rowsJ2 88 89 61 360 ≤ 10416081777607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2287 c22250R_88_31 (by norm_num)

theorem c22250R_88_29 : rowsJ2 88 89 60 360 ≤ 10416081777607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2286 c22250R_88_30 (by norm_num)

theorem c22250R_88_28 : rowsJ2 88 89 59 360 ≤ 10416081777607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2285 c22250R_88_29 (by norm_num)

theorem c22250R_88_27 : rowsJ2 88 89 58 360 ≤ 10416081777607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2284 c22250R_88_28 (by norm_num)

theorem c22250R_88_26 : rowsJ2 88 89 57 360 ≤ 10416081777607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2283 c22250R_88_27 (by norm_num)

theorem c22250R_88_25 : rowsJ2 88 89 56 360 ≤ 10416081777607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2282 c22250R_88_26 (by norm_num)

theorem c22250R_88_24 : rowsJ2 88 89 55 360 ≤ 10416081777607 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2281 c22250R_88_25 (by norm_num)

theorem c22250R_88_23 : rowsJ2 88 89 54 360 ≤ 10461532652347 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2280 c22250R_88_24 (by norm_num)

theorem c22250R_88_22 : rowsJ2 88 89 53 360 ≤ 10552834561008 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2279 c22250R_88_23 (by norm_num)

theorem c22250R_88_21 : rowsJ2 88 89 52 360 ≤ 10735302311663 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2278 c22250R_88_22 (by norm_num)

theorem c22250R_88_20 : rowsJ2 88 89 51 360 ≤ 10962994493410 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2277 c22250R_88_21 (by norm_num)

theorem c22250R_88_19 : rowsJ2 88 89 50 360 ≤ 11280752781548 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2276 c22250R_88_20 (by norm_num)

theorem c22250R_88_18 : rowsJ2 88 89 49 360 ≤ 11643247996506 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2275 c22250R_88_19 (by norm_num)

theorem c22250R_88_17 : rowsJ2 88 89 48 360 ≤ 11958912890799 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2274 c22250R_88_18 (by norm_num)

theorem c22250R_88_16 : rowsJ2 88 89 47 360 ≤ 12048533902750 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2273 c22250R_88_17 (by norm_num)

theorem c22250R_88_15 : rowsJ2 88 89 46 360 ≤ 12048533902750 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2272 c22250R_88_16 (by norm_num)

theorem c22250R_88_14 : rowsJ2 88 89 45 360 ≤ 12048533902750 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2271 c22250R_88_15 (by norm_num)

theorem c22250R_88_13 : rowsJ2 88 89 44 360 ≤ 14212757762215 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2270 c22250R_88_14 (by norm_num)

theorem c22250R_88_12 : rowsJ2 88 89 43 360 ≤ 17700401342032 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2269 c22250R_88_13 (by norm_num)

theorem c22250R_88_11 : rowsJ2 88 89 42 360 ≤ 22213840786710 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2268 c22250R_88_12 (by norm_num)

theorem c22250R_88_10 : rowsJ2 88 89 40 360 ≤ 30939804938568 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2267 c22250R_88_11 (by norm_num)

theorem c22250R_88_9 : rowsJ2 88 89 38 360 ≤ 36052200393271 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2266 c22250R_88_10 (by norm_num)

theorem c22250R_88_8 : rowsJ2 88 89 35 360 ≤ 38631099975494 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2265 c22250R_88_9 (by norm_num)

theorem c22250R_88_7 : rowsJ2 88 89 31 360 ≤ 38631099975494 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2264 c22250R_88_8 (by norm_num)

theorem c22250R_88_6 : rowsJ2 88 89 28 360 ≤ 38631099975494 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2263 c22250R_88_7 (by norm_num)

theorem c22250R_88_5 : rowsJ2 88 89 25 360 ≤ 38631099975494 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2262 c22250R_88_6 (by norm_num)

theorem c22250R_88_4 : rowsJ2 88 89 23 360 ≤ 38631099975494 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2261 c22250R_88_5 (by norm_num)

theorem c22250R_88_3 : rowsJ2 88 89 21 360 ≤ 38631099975494 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2260 c22250R_88_4 (by norm_num)

theorem c22250R_88_2 : rowsJ2 88 89 19 360 ≤ 38633280877151 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2259 c22250R_88_3 (by norm_num)

theorem c22250R_88_1 : rowsJ2 88 89 17 360 ≤ 38638440033308 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2258 c22250R_88_2 (by norm_num)

theorem c22250R_88_0 : rowsJ2 88 89 0 360 ≤ 38654380552969 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22250R_2257 c22250R_88_1 (by norm_num)

theorem hr22250R_88 : rows2 88 89 ≤ 38654380552969 := rows2_le_of_rowsJ2 88 89 c22250R_88_0

theorem c22250R_89_47 : rowsJ2 89 90 88 360 ≤ 6376771565559 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2353 rows22250R_2354 (by norm_num)

theorem c22250R_89_46 : rowsJ2 89 90 87 360 ≤ 8545743113862 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2352 c22250R_89_47 (by norm_num)

theorem c22250R_89_45 : rowsJ2 89 90 86 360 ≤ 10193616732118 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2351 c22250R_89_46 (by norm_num)

theorem c22250R_89_44 : rowsJ2 89 90 85 360 ≤ 11421813402179 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2350 c22250R_89_45 (by norm_num)

theorem c22250R_89_43 : rowsJ2 89 90 84 360 ≤ 12394374985625 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2349 c22250R_89_44 (by norm_num)

theorem c22250R_89_42 : rowsJ2 89 90 82 360 ≤ 13410693685585 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2348 c22250R_89_43 (by norm_num)

theorem c22250R_89_41 : rowsJ2 89 90 79 360 ≤ 13631740724416 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2347 c22250R_89_42 (by norm_num)

theorem c22250R_89_40 : rowsJ2 89 90 76 360 ≤ 13631740724416 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2346 c22250R_89_41 (by norm_num)

theorem c22250R_89_39 : rowsJ2 89 90 73 360 ≤ 13631740724416 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2345 c22250R_89_40 (by norm_num)

theorem c22250R_89_38 : rowsJ2 89 90 71 360 ≤ 13631740724416 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2344 c22250R_89_39 (by norm_num)

theorem c22250R_89_37 : rowsJ2 89 90 69 360 ≤ 13631740724416 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2343 c22250R_89_38 (by norm_num)

theorem c22250R_89_36 : rowsJ2 89 90 67 360 ≤ 13631740724416 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2342 c22250R_89_37 (by norm_num)

theorem c22250R_89_35 : rowsJ2 89 90 66 360 ≤ 13631740724416 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2341 c22250R_89_36 (by norm_num)

theorem c22250R_89_34 : rowsJ2 89 90 65 360 ≤ 13631740724416 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2340 c22250R_89_35 (by norm_num)

theorem c22250R_89_33 : rowsJ2 89 90 64 360 ≤ 13631740724416 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2339 c22250R_89_34 (by norm_num)

theorem c22250R_89_32 : rowsJ2 89 90 63 360 ≤ 13631740724416 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2338 c22250R_89_33 (by norm_num)

theorem c22250R_89_31 : rowsJ2 89 90 62 360 ≤ 13631740724416 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2337 c22250R_89_32 (by norm_num)

theorem c22250R_89_30 : rowsJ2 89 90 61 360 ≤ 13631740724416 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2336 c22250R_89_31 (by norm_num)

theorem c22250R_89_29 : rowsJ2 89 90 60 360 ≤ 13631740724416 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2335 c22250R_89_30 (by norm_num)

theorem c22250R_89_28 : rowsJ2 89 90 59 360 ≤ 13631740724416 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2334 c22250R_89_29 (by norm_num)

theorem c22250R_89_27 : rowsJ2 89 90 58 360 ≤ 13631740724416 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2333 c22250R_89_28 (by norm_num)

theorem c22250R_89_26 : rowsJ2 89 90 57 360 ≤ 13631740724416 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2332 c22250R_89_27 (by norm_num)

theorem c22250R_89_25 : rowsJ2 89 90 56 360 ≤ 13631740724416 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2331 c22250R_89_26 (by norm_num)

theorem c22250R_89_24 : rowsJ2 89 90 55 360 ≤ 13631740724416 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2330 c22250R_89_25 (by norm_num)

theorem c22250R_89_23 : rowsJ2 89 90 54 360 ≤ 13631740724416 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2329 c22250R_89_24 (by norm_num)

theorem c22250R_89_22 : rowsJ2 89 90 53 360 ≤ 13677303089422 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2328 c22250R_89_23 (by norm_num)

theorem c22250R_89_21 : rowsJ2 89 90 52 360 ≤ 13768837622023 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2327 c22250R_89_22 (by norm_num)

theorem c22250R_89_20 : rowsJ2 89 90 51 360 ≤ 13905321536636 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2326 c22250R_89_21 (by norm_num)

theorem c22250R_89_19 : rowsJ2 89 90 50 360 ≤ 14087201423245 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2325 c22250R_89_20 (by norm_num)

theorem c22250R_89_18 : rowsJ2 89 90 49 360 ≤ 14313523567850 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2324 c22250R_89_19 (by norm_num)

theorem c22250R_89_17 : rowsJ2 89 90 48 360 ≤ 14539303570948 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2323 c22250R_89_18 (by norm_num)

theorem c22250R_89_16 : rowsJ2 89 90 47 360 ≤ 14628278892530 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2322 c22250R_89_17 (by norm_num)

theorem c22250R_89_15 : rowsJ2 89 90 46 360 ≤ 14628278892530 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2321 c22250R_89_16 (by norm_num)

theorem c22250R_89_14 : rowsJ2 89 90 45 360 ≤ 16963118687906 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2320 c22250R_89_15 (by norm_num)

theorem c22250R_89_13 : rowsJ2 89 90 44 360 ≤ 21157681035507 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2319 c22250R_89_14 (by norm_num)

theorem c22250R_89_12 : rowsJ2 89 90 43 360 ≤ 26375228974182 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2318 c22250R_89_13 (by norm_num)

theorem c22250R_89_11 : rowsJ2 89 90 42 360 ≤ 32369616072527 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2317 c22250R_89_12 (by norm_num)

theorem c22250R_89_10 : rowsJ2 89 90 41 360 ≤ 37455085330234 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2316 c22250R_89_11 (by norm_num)

theorem c22250R_89_9 : rowsJ2 89 90 39 360 ≤ 45003035493354 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2315 c22250R_89_10 (by norm_num)

theorem c22250R_89_8 : rowsJ2 89 90 36 360 ≤ 49779772176439 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2314 c22250R_89_9 (by norm_num)

theorem c22250R_89_7 : rowsJ2 89 90 32 360 ≤ 50325006545875 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2313 c22250R_89_8 (by norm_num)

theorem c22250R_89_6 : rowsJ2 89 90 28 360 ≤ 50325006545875 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2312 c22250R_89_7 (by norm_num)

theorem c22250R_89_5 : rowsJ2 89 90 25 360 ≤ 50325006545875 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2311 c22250R_89_6 (by norm_num)

theorem c22250R_89_4 : rowsJ2 89 90 23 360 ≤ 50325006545875 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2310 c22250R_89_5 (by norm_num)

theorem c22250R_89_3 : rowsJ2 89 90 21 360 ≤ 50325006545875 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2309 c22250R_89_4 (by norm_num)

theorem c22250R_89_2 : rowsJ2 89 90 19 360 ≤ 50325735393272 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2308 c22250R_89_3 (by norm_num)

theorem c22250R_89_1 : rowsJ2 89 90 17 360 ≤ 50329421980009 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2307 c22250R_89_2 (by norm_num)

theorem c22250R_89_0 : rowsJ2 89 90 0 360 ≤ 50338214306382 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22250R_2306 c22250R_89_1 (by norm_num)

theorem hr22250R_89 : rows2 89 90 ≤ 50338214306382 := rows2_le_of_rowsJ2 89 90 c22250R_89_0

theorem c22250R_90_47 : rowsJ2 90 91 89 360 ≤ 7990057347822 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2402 rows22250R_2403 (by norm_num)

theorem c22250R_90_46 : rowsJ2 90 91 88 360 ≤ 10785286545245 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2401 c22250R_90_47 (by norm_num)

theorem c22250R_90_45 : rowsJ2 90 91 87 360 ≤ 12939337371196 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2400 c22250R_90_46 (by norm_num)

theorem c22250R_90_44 : rowsJ2 90 91 86 360 ≤ 14575423518547 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2399 c22250R_90_45 (by norm_num)

theorem c22250R_90_43 : rowsJ2 90 91 85 360 ≤ 15794834725729 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2398 c22250R_90_44 (by norm_num)

theorem c22250R_90_42 : rowsJ2 90 91 84 360 ≤ 16664209441177 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2397 c22250R_90_43 (by norm_num)

theorem c22250R_90_41 : rowsJ2 90 91 83 360 ≤ 17333136596683 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2396 c22250R_90_42 (by norm_num)

theorem c22250R_90_40 : rowsJ2 90 91 81 360 ≤ 17839118463994 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2395 c22250R_90_41 (by norm_num)

theorem c22250R_90_39 : rowsJ2 90 91 78 360 ≤ 17894154165242 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2394 c22250R_90_40 (by norm_num)

theorem c22250R_90_38 : rowsJ2 90 91 75 360 ≤ 17894154165242 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2393 c22250R_90_39 (by norm_num)

theorem c22250R_90_37 : rowsJ2 90 91 72 360 ≤ 17894154165242 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2392 c22250R_90_38 (by norm_num)

theorem c22250R_90_36 : rowsJ2 90 91 70 360 ≤ 17894154165242 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2391 c22250R_90_37 (by norm_num)

theorem c22250R_90_35 : rowsJ2 90 91 68 360 ≤ 17894154165242 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2390 c22250R_90_36 (by norm_num)

theorem c22250R_90_34 : rowsJ2 90 91 66 360 ≤ 17894154165242 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2389 c22250R_90_35 (by norm_num)

theorem c22250R_90_33 : rowsJ2 90 91 65 360 ≤ 17894154165242 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2388 c22250R_90_34 (by norm_num)

theorem c22250R_90_32 : rowsJ2 90 91 64 360 ≤ 17894154165242 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2387 c22250R_90_33 (by norm_num)

theorem c22250R_90_31 : rowsJ2 90 91 63 360 ≤ 17894154165242 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2386 c22250R_90_32 (by norm_num)

theorem c22250R_90_30 : rowsJ2 90 91 62 360 ≤ 17894154165242 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2385 c22250R_90_31 (by norm_num)

theorem c22250R_90_29 : rowsJ2 90 91 61 360 ≤ 17894154165242 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2384 c22250R_90_30 (by norm_num)

theorem c22250R_90_28 : rowsJ2 90 91 60 360 ≤ 17894154165242 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2383 c22250R_90_29 (by norm_num)

theorem c22250R_90_27 : rowsJ2 90 91 59 360 ≤ 17894154165242 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2382 c22250R_90_28 (by norm_num)

theorem c22250R_90_26 : rowsJ2 90 91 58 360 ≤ 17894154165242 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2381 c22250R_90_27 (by norm_num)

theorem c22250R_90_25 : rowsJ2 90 91 57 360 ≤ 17894154165242 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2380 c22250R_90_26 (by norm_num)

theorem c22250R_90_24 : rowsJ2 90 91 56 360 ≤ 17894154165242 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2379 c22250R_90_25 (by norm_num)

theorem c22250R_90_23 : rowsJ2 90 91 55 360 ≤ 17894154165242 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2378 c22250R_90_24 (by norm_num)

theorem c22250R_90_22 : rowsJ2 90 91 54 360 ≤ 17894154165242 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2377 c22250R_90_23 (by norm_num)

theorem c22250R_90_21 : rowsJ2 90 91 53 360 ≤ 17894154165242 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2376 c22250R_90_22 (by norm_num)

theorem c22250R_90_20 : rowsJ2 90 91 52 360 ≤ 17939834987676 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2375 c22250R_90_21 (by norm_num)

theorem c22250R_90_19 : rowsJ2 90 91 51 360 ≤ 17985482346386 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2374 c22250R_90_20 (by norm_num)

theorem c22250R_90_18 : rowsJ2 90 91 50 360 ≤ 18076243028541 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2373 c22250R_90_19 (by norm_num)

theorem c22250R_90_17 : rowsJ2 90 91 49 360 ≤ 18166970323258 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2372 c22250R_90_18 (by norm_num)

theorem c22250R_90_16 : rowsJ2 90 91 48 360 ≤ 18302316173831 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2371 c22250R_90_17 (by norm_num)

theorem c22250R_90_15 : rowsJ2 90 91 47 360 ≤ 18346944266717 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2370 c22250R_90_16 (by norm_num)

theorem c22250R_90_14 : rowsJ2 90 91 46 360 ≤ 21390668767199 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2369 c22250R_90_15 (by norm_num)

theorem c22250R_90_13 : rowsJ2 90 91 45 360 ≤ 26416238296219 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2368 c22250R_90_14 (by norm_num)

theorem c22250R_90_12 : rowsJ2 90 91 44 360 ≤ 32949832750087 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2367 c22250R_90_13 (by norm_num)

theorem c22250R_90_11 : rowsJ2 90 91 43 360 ≤ 40206353198374 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2366 c22250R_90_12 (by norm_num)

theorem c22250R_90_10 : rowsJ2 90 91 42 360 ≤ 46466128469054 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2365 c22250R_90_11 (by norm_num)

theorem c22250R_90_9 : rowsJ2 90 91 41 360 ≤ 51826882572265 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2364 c22250R_90_10 (by norm_num)

theorem c22250R_90_8 : rowsJ2 90 91 39 360 ≤ 59954655212855 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2363 c22250R_90_9 (by norm_num)

theorem c22250R_90_7 : rowsJ2 90 91 36 360 ≤ 65174059709570 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2362 c22250R_90_8 (by norm_num)

theorem c22250R_90_6 : rowsJ2 90 91 31 360 ≤ 65955550761407 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2361 c22250R_90_7 (by norm_num)

theorem c22250R_90_5 : rowsJ2 90 91 27 360 ≤ 65955550761407 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2360 c22250R_90_6 (by norm_num)

theorem c22250R_90_4 : rowsJ2 90 91 24 360 ≤ 65955550761407 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2359 c22250R_90_5 (by norm_num)

theorem c22250R_90_3 : rowsJ2 90 91 22 360 ≤ 65955550761407 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2358 c22250R_90_4 (by norm_num)

theorem c22250R_90_2 : rowsJ2 90 91 20 360 ≤ 65955550761407 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2357 c22250R_90_3 (by norm_num)

theorem c22250R_90_1 : rowsJ2 90 91 17 360 ≤ 65957764511007 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2356 c22250R_90_2 (by norm_num)

theorem c22250R_90_0 : rowsJ2 90 91 0 360 ≤ 65962547168540 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22250R_2355 c22250R_90_1 (by norm_num)

theorem hr22250R_90 : rows2 90 91 ≤ 65962547168540 := rows2_le_of_rowsJ2 90 91 c22250R_90_0

theorem c22250R_91_46 : rowsJ2 91 92 90 360 ≤ 9876763764390 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2450 rows22250R_2451 (by norm_num)

theorem c22250R_91_45 : rowsJ2 91 92 89 360 ≤ 13411454357341 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2449 c22250R_91_46 (by norm_num)

theorem c22250R_91_44 : rowsJ2 91 92 88 360 ≤ 16191334492604 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2448 c22250R_91_45 (by norm_num)

theorem c22250R_91_43 : rowsJ2 91 92 87 360 ≤ 18331883955408 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2447 c22250R_91_44 (by norm_num)

theorem c22250R_91_42 : rowsJ2 91 92 86 360 ≤ 19955251428921 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2446 c22250R_91_43 (by norm_num)

theorem c22250R_91_41 : rowsJ2 91 92 85 360 ≤ 21166001967838 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2445 c22250R_91_42 (by norm_num)

theorem c22250R_91_40 : rowsJ2 91 92 84 360 ≤ 22029202091839 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2444 c22250R_91_41 (by norm_num)

theorem c22250R_91_39 : rowsJ2 91 92 83 360 ≤ 22597112277155 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2443 c22250R_91_40 (by norm_num)

theorem c22250R_91_38 : rowsJ2 91 92 81 360 ≤ 23099500491176 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2442 c22250R_91_39 (by norm_num)

theorem c22250R_91_37 : rowsJ2 91 92 78 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2441 c22250R_91_38 (by norm_num)

theorem c22250R_91_36 : rowsJ2 91 92 74 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2440 c22250R_91_37 (by norm_num)

theorem c22250R_91_35 : rowsJ2 91 92 71 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2439 c22250R_91_36 (by norm_num)

theorem c22250R_91_34 : rowsJ2 91 92 69 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2438 c22250R_91_35 (by norm_num)

theorem c22250R_91_33 : rowsJ2 91 92 67 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2437 c22250R_91_34 (by norm_num)

theorem c22250R_91_32 : rowsJ2 91 92 65 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2436 c22250R_91_33 (by norm_num)

theorem c22250R_91_31 : rowsJ2 91 92 64 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2435 c22250R_91_32 (by norm_num)

theorem c22250R_91_30 : rowsJ2 91 92 63 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2434 c22250R_91_31 (by norm_num)

theorem c22250R_91_29 : rowsJ2 91 92 62 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2433 c22250R_91_30 (by norm_num)

theorem c22250R_91_28 : rowsJ2 91 92 61 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2432 c22250R_91_29 (by norm_num)

theorem c22250R_91_27 : rowsJ2 91 92 60 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2431 c22250R_91_28 (by norm_num)

theorem c22250R_91_26 : rowsJ2 91 92 59 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2430 c22250R_91_27 (by norm_num)

theorem c22250R_91_25 : rowsJ2 91 92 58 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2429 c22250R_91_26 (by norm_num)

theorem c22250R_91_24 : rowsJ2 91 92 57 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2428 c22250R_91_25 (by norm_num)

theorem c22250R_91_23 : rowsJ2 91 92 56 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2427 c22250R_91_24 (by norm_num)

theorem c22250R_91_22 : rowsJ2 91 92 55 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2426 c22250R_91_23 (by norm_num)

theorem c22250R_91_21 : rowsJ2 91 92 54 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2425 c22250R_91_22 (by norm_num)

theorem c22250R_91_20 : rowsJ2 91 92 53 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2424 c22250R_91_21 (by norm_num)

theorem c22250R_91_19 : rowsJ2 91 92 52 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2423 c22250R_91_20 (by norm_num)

theorem c22250R_91_18 : rowsJ2 91 92 51 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2422 c22250R_91_19 (by norm_num)

theorem c22250R_91_17 : rowsJ2 91 92 50 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2421 c22250R_91_18 (by norm_num)

theorem c22250R_91_16 : rowsJ2 91 92 49 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2420 c22250R_91_17 (by norm_num)

theorem c22250R_91_15 : rowsJ2 91 92 48 360 ≤ 23154145310374 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2419 c22250R_91_16 (by norm_num)

theorem c22250R_91_14 : rowsJ2 91 92 47 360 ≤ 26358540860898 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2418 c22250R_91_15 (by norm_num)

theorem c22250R_91_13 : rowsJ2 91 92 46 360 ≤ 32321865479481 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2417 c22250R_91_14 (by norm_num)

theorem c22250R_91_12 : rowsJ2 91 92 45 360 ≤ 39988297595451 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2416 c22250R_91_13 (by norm_num)

theorem c22250R_91_11 : rowsJ2 91 92 44 360 ≤ 48806995841293 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2415 c22250R_91_12 (by norm_num)

theorem c22250R_91_10 : rowsJ2 91 92 43 360 ≤ 56471157308043 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2414 c22250R_91_11 (by norm_num)

theorem c22250R_91_9 : rowsJ2 91 92 42 360 ≤ 63072802969686 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2413 c22250R_91_10 (by norm_num)

theorem c22250R_91_8 : rowsJ2 91 92 40 360 ≤ 73480038515838 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2412 c22250R_91_9 (by norm_num)

theorem c22250R_91_7 : rowsJ2 91 92 38 360 ≤ 80221981410607 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2411 c22250R_91_8 (by norm_num)

theorem c22250R_91_6 : rowsJ2 91 92 34 360 ≤ 84174844191780 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2410 c22250R_91_7 (by norm_num)

theorem c22250R_91_5 : rowsJ2 91 92 29 360 ≤ 84174844191780 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2409 c22250R_91_6 (by norm_num)

theorem c22250R_91_4 : rowsJ2 91 92 25 360 ≤ 84174844191780 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2408 c22250R_91_5 (by norm_num)

theorem c22250R_91_3 : rowsJ2 91 92 22 360 ≤ 84174844191780 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2407 c22250R_91_4 (by norm_num)

theorem c22250R_91_2 : rowsJ2 91 92 20 360 ≤ 84174844191780 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2406 c22250R_91_3 (by norm_num)

theorem c22250R_91_1 : rowsJ2 91 92 17 360 ≤ 84175584198351 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2405 c22250R_91_2 (by norm_num)

theorem c22250R_91_0 : rowsJ2 91 92 0 360 ≤ 84176335451437 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22250R_2404 c22250R_91_1 (by norm_num)

theorem hr22250R_91 : rows2 91 92 ≤ 84176335451437 := rows2_le_of_rowsJ2 91 92 c22250R_91_0

theorem c22250R_92_46 : rowsJ2 92 93 91 360 ≤ 12073815501593 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2498 rows22250R_2499 (by norm_num)

theorem c22250R_92_45 : rowsJ2 92 93 90 360 ≤ 16488837126405 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2497 c22250R_92_46 (by norm_num)

theorem c22250R_92_44 : rowsJ2 92 93 89 360 ≤ 20008757633230 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2496 c22250R_92_45 (by norm_num)

theorem c22250R_92_43 : rowsJ2 92 93 88 360 ≤ 22773806162724 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2495 c22250R_92_44 (by norm_num)

theorem c22250R_92_42 : rowsJ2 92 93 87 360 ≤ 24900039449121 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2494 c22250R_92_43 (by norm_num)

theorem c22250R_92_41 : rowsJ2 92 93 86 360 ≤ 26511996198192 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2493 c22250R_92_42 (by norm_num)

theorem c22250R_92_40 : rowsJ2 92 93 85 360 ≤ 27714208223223 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2492 c22250R_92_41 (by norm_num)

theorem c22250R_92_39 : rowsJ2 92 93 84 360 ≤ 28571320845289 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2491 c22250R_92_40 (by norm_num)

theorem c22250R_92_38 : rowsJ2 92 93 83 360 ≤ 29135225986755 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2490 c22250R_92_39 (by norm_num)

theorem c22250R_92_37 : rowsJ2 92 93 81 360 ≤ 29634071234155 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2489 c22250R_92_38 (by norm_num)

theorem c22250R_92_36 : rowsJ2 92 93 77 360 ≤ 29688330684500 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2488 c22250R_92_37 (by norm_num)

theorem c22250R_92_35 : rowsJ2 92 93 73 360 ≤ 29688330684500 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2487 c22250R_92_36 (by norm_num)

theorem c22250R_92_34 : rowsJ2 92 93 70 360 ≤ 29688330684500 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2486 c22250R_92_35 (by norm_num)

theorem c22250R_92_33 : rowsJ2 92 93 68 360 ≤ 29688330684500 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2485 c22250R_92_34 (by norm_num)

theorem c22250R_92_32 : rowsJ2 92 93 66 360 ≤ 29688330684500 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2484 c22250R_92_33 (by norm_num)

theorem c22250R_92_31 : rowsJ2 92 93 64 360 ≤ 29688330684500 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2483 c22250R_92_32 (by norm_num)

theorem c22250R_92_30 : rowsJ2 92 93 63 360 ≤ 29688330684500 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2482 c22250R_92_31 (by norm_num)

theorem c22250R_92_29 : rowsJ2 92 93 62 360 ≤ 29688330684500 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2481 c22250R_92_30 (by norm_num)

theorem c22250R_92_28 : rowsJ2 92 93 61 360 ≤ 29688330684500 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2480 c22250R_92_29 (by norm_num)

theorem c22250R_92_27 : rowsJ2 92 93 60 360 ≤ 29688330684500 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2479 c22250R_92_28 (by norm_num)

theorem c22250R_92_26 : rowsJ2 92 93 59 360 ≤ 29688330684500 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2478 c22250R_92_27 (by norm_num)

theorem c22250R_92_25 : rowsJ2 92 93 58 360 ≤ 29688330684500 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2477 c22250R_92_26 (by norm_num)

theorem c22250R_92_24 : rowsJ2 92 93 57 360 ≤ 29688330684500 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2476 c22250R_92_25 (by norm_num)

theorem c22250R_92_23 : rowsJ2 92 93 56 360 ≤ 29688330684500 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2475 c22250R_92_24 (by norm_num)

theorem c22250R_92_22 : rowsJ2 92 93 55 360 ≤ 29688330684500 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2474 c22250R_92_23 (by norm_num)

theorem c22250R_92_21 : rowsJ2 92 93 54 360 ≤ 29688330684500 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2473 c22250R_92_22 (by norm_num)

theorem c22250R_92_20 : rowsJ2 92 93 53 360 ≤ 29688330684500 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2472 c22250R_92_21 (by norm_num)

theorem c22250R_92_19 : rowsJ2 92 93 52 360 ≤ 29688330684500 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2471 c22250R_92_20 (by norm_num)

theorem c22250R_92_18 : rowsJ2 92 93 51 360 ≤ 29688330684500 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2470 c22250R_92_19 (by norm_num)

theorem c22250R_92_17 : rowsJ2 92 93 50 360 ≤ 29688330684500 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2469 c22250R_92_18 (by norm_num)

theorem c22250R_92_16 : rowsJ2 92 93 49 360 ≤ 29688330684500 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2468 c22250R_92_17 (by norm_num)

theorem c22250R_92_15 : rowsJ2 92 93 48 360 ≤ 33468005532002 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2467 c22250R_92_16 (by norm_num)

theorem c22250R_92_14 : rowsJ2 92 93 47 360 ≤ 40165524126330 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2466 c22250R_92_15 (by norm_num)

theorem c22250R_92_13 : rowsJ2 92 93 46 360 ≤ 49382341990473 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2465 c22250R_92_14 (by norm_num)

theorem c22250R_92_12 : rowsJ2 92 93 45 360 ≤ 59978875239835 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2464 c22250R_92_13 (by norm_num)

theorem c22250R_92_11 : rowsJ2 92 93 44 360 ≤ 69348327125513 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2463 c22250R_92_12 (by norm_num)

theorem c22250R_92_10 : rowsJ2 92 93 43 360 ≤ 77498178696017 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2462 c22250R_92_11 (by norm_num)

theorem c22250R_92_9 : rowsJ2 92 93 42 360 ≤ 84519503575154 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2461 c22250R_92_10 (by norm_num)

theorem c22250R_92_8 : rowsJ2 92 93 41 360 ≤ 90507880077924 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2460 c22250R_92_9 (by norm_num)

theorem c22250R_92_7 : rowsJ2 92 93 39 360 ≤ 99792913717628 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2459 c22250R_92_8 (by norm_num)

theorem c22250R_92_6 : rowsJ2 92 93 36 360 ≤ 106133339660257 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2458 c22250R_92_7 (by norm_num)

theorem c22250R_92_5 : rowsJ2 92 93 31 360 ≤ 107387929769899 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2457 c22250R_92_6 (by norm_num)

theorem c22250R_92_4 : rowsJ2 92 93 26 360 ≤ 107387929769899 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2456 c22250R_92_5 (by norm_num)

theorem c22250R_92_3 : rowsJ2 92 93 23 360 ≤ 107387929769899 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2455 c22250R_92_4 (by norm_num)

theorem c22250R_92_2 : rowsJ2 92 93 20 360 ≤ 107387929769899 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2454 c22250R_92_3 (by norm_num)

theorem c22250R_92_1 : rowsJ2 92 93 17 360 ≤ 107387929769899 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2453 c22250R_92_2 (by norm_num)

theorem c22250R_92_0 : rowsJ2 92 93 0 360 ≤ 107388675724961 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22250R_2452 c22250R_92_1 (by norm_num)

theorem hr22250R_92 : rows2 92 93 ≤ 107388675724961 := rows2_le_of_rowsJ2 92 93 c22250R_92_0

theorem c22250R_93_46 : rowsJ2 93 94 92 360 ≤ 14386991425560 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2546 rows22250R_2547 (by norm_num)

theorem c22250R_93_45 : rowsJ2 93 94 91 360 ≤ 19825582482625 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2545 c22250R_93_46 (by norm_num)

theorem c22250R_93_44 : rowsJ2 93 94 90 360 ≤ 24230260358927 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2544 c22250R_93_45 (by norm_num)

theorem c22250R_93_43 : rowsJ2 93 94 89 360 ≤ 27737390467739 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2543 c22250R_93_44 (by norm_num)

theorem c22250R_93_42 : rowsJ2 93 94 88 360 ≤ 30487052599935 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2542 c22250R_93_43 (by norm_num)

theorem c22250R_93_41 : rowsJ2 93 94 87 360 ≤ 32599288998166 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2541 c22250R_93_42 (by norm_num)

theorem c22250R_93_40 : rowsJ2 93 94 86 360 ≤ 34199995120140 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2540 c22250R_93_41 (by norm_num)

theorem c22250R_93_39 : rowsJ2 93 94 85 360 ≤ 35393788219368 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2539 c22250R_93_40 (by norm_num)

theorem c22250R_93_38 : rowsJ2 93 94 84 360 ≤ 36244898599387 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2538 c22250R_93_39 (by norm_num)

theorem c22250R_93_37 : rowsJ2 93 94 83 360 ≤ 36804854790541 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2537 c22250R_93_38 (by norm_num)

theorem c22250R_93_36 : rowsJ2 93 94 80 360 ≤ 37354086172000 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2536 c22250R_93_37 (by norm_num)

theorem c22250R_93_35 : rowsJ2 93 94 76 360 ≤ 37354086172000 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2535 c22250R_93_36 (by norm_num)

theorem c22250R_93_34 : rowsJ2 93 94 72 360 ≤ 37354086172000 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2534 c22250R_93_35 (by norm_num)

theorem c22250R_93_33 : rowsJ2 93 94 69 360 ≤ 37354086172000 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2533 c22250R_93_34 (by norm_num)

theorem c22250R_93_32 : rowsJ2 93 94 67 360 ≤ 37354086172000 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2532 c22250R_93_33 (by norm_num)

theorem c22250R_93_31 : rowsJ2 93 94 65 360 ≤ 37354086172000 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2531 c22250R_93_32 (by norm_num)

theorem c22250R_93_30 : rowsJ2 93 94 63 360 ≤ 37354086172000 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2530 c22250R_93_31 (by norm_num)

theorem c22250R_93_29 : rowsJ2 93 94 62 360 ≤ 37354086172000 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2529 c22250R_93_30 (by norm_num)

theorem c22250R_93_28 : rowsJ2 93 94 61 360 ≤ 37354086172000 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2528 c22250R_93_29 (by norm_num)

theorem c22250R_93_27 : rowsJ2 93 94 60 360 ≤ 37354086172000 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2527 c22250R_93_28 (by norm_num)

theorem c22250R_93_26 : rowsJ2 93 94 59 360 ≤ 37354086172000 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2526 c22250R_93_27 (by norm_num)

theorem c22250R_93_25 : rowsJ2 93 94 58 360 ≤ 37354086172000 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2525 c22250R_93_26 (by norm_num)

theorem c22250R_93_24 : rowsJ2 93 94 57 360 ≤ 37354086172000 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2524 c22250R_93_25 (by norm_num)

theorem c22250R_93_23 : rowsJ2 93 94 56 360 ≤ 37354086172000 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2523 c22250R_93_24 (by norm_num)

theorem c22250R_93_22 : rowsJ2 93 94 55 360 ≤ 37354086172000 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2522 c22250R_93_23 (by norm_num)

theorem c22250R_93_21 : rowsJ2 93 94 54 360 ≤ 37354086172000 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2521 c22250R_93_22 (by norm_num)

theorem c22250R_93_20 : rowsJ2 93 94 53 360 ≤ 37354086172000 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2520 c22250R_93_21 (by norm_num)

theorem c22250R_93_19 : rowsJ2 93 94 52 360 ≤ 37354086172000 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2519 c22250R_93_20 (by norm_num)

theorem c22250R_93_18 : rowsJ2 93 94 51 360 ≤ 37354086172000 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2518 c22250R_93_19 (by norm_num)

theorem c22250R_93_17 : rowsJ2 93 94 50 360 ≤ 37354086172000 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2517 c22250R_93_18 (by norm_num)

theorem c22250R_93_16 : rowsJ2 93 94 49 360 ≤ 41009810148805 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2516 c22250R_93_17 (by norm_num)

theorem c22250R_93_15 : rowsJ2 93 94 48 360 ≤ 48456120500010 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2515 c22250R_93_16 (by norm_num)

theorem c22250R_93_14 : rowsJ2 93 94 47 360 ≤ 58529509917616 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2514 c22250R_93_15 (by norm_num)

theorem c22250R_93_13 : rowsJ2 93 94 46 360 ≤ 70834071198554 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2513 c22250R_93_14 (by norm_num)

theorem c22250R_93_12 : rowsJ2 93 94 45 360 ≤ 81965541529971 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2512 c22250R_93_13 (by norm_num)

theorem c22250R_93_11 : rowsJ2 93 94 44 360 ≤ 91885017730513 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2511 c22250R_93_12 (by norm_num)

theorem c22250R_93_10 : rowsJ2 93 94 43 360 ≤ 100600068421970 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2510 c22250R_93_11 (by norm_num)

theorem c22250R_93_9 : rowsJ2 93 94 42 360 ≤ 108120295528931 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2509 c22250R_93_10 (by norm_num)

theorem c22250R_93_8 : rowsJ2 93 94 41 360 ≤ 114540279955634 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2508 c22250R_93_9 (by norm_num)

theorem c22250R_93_7 : rowsJ2 93 94 39 360 ≤ 124482131561358 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2507 c22250R_93_8 (by norm_num)

theorem c22250R_93_6 : rowsJ2 93 94 37 360 ≤ 130219447149528 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2506 c22250R_93_7 (by norm_num)

theorem c22250R_93_5 : rowsJ2 93 94 33 360 ≤ 132992969716098 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2505 c22250R_93_6 (by norm_num)

theorem c22250R_93_4 : rowsJ2 93 94 27 360 ≤ 132992969716098 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2504 c22250R_93_5 (by norm_num)

theorem c22250R_93_3 : rowsJ2 93 94 23 360 ≤ 132992969716098 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2503 c22250R_93_4 (by norm_num)

theorem c22250R_93_2 : rowsJ2 93 94 20 360 ≤ 132992969716098 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2502 c22250R_93_3 (by norm_num)

theorem c22250R_93_1 : rowsJ2 93 94 17 360 ≤ 132992969716098 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2501 c22250R_93_2 (by norm_num)

theorem c22250R_93_0 : rowsJ2 93 94 0 360 ≤ 132992969716098 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22250R_2500 c22250R_93_1 (by norm_num)

theorem hr22250R_93 : rows2 93 94 ≤ 132992969716098 := rows2_le_of_rowsJ2 93 94 c22250R_93_0

theorem c22250R_94_46 : rowsJ2 94 95 93 360 ≤ 14366665502819 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2594 rows22250R_2595 (by norm_num)

theorem c22250R_94_45 : rowsJ2 94 95 92 360 ≤ 20929772626455 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2593 c22250R_94_46 (by norm_num)

theorem c22250R_94_44 : rowsJ2 94 95 91 360 ≤ 26365225230954 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2592 c22250R_94_45 (by norm_num)

theorem c22250R_94_43 : rowsJ2 94 95 90 360 ≤ 30760965028951 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2591 c22250R_94_44 (by norm_num)

theorem c22250R_94_42 : rowsJ2 94 95 89 360 ≤ 34255104693540 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2590 c22250R_94_43 (by norm_num)

theorem c22250R_94_41 : rowsJ2 94 95 88 360 ≤ 36991050555217 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2589 c22250R_94_42 (by norm_num)

theorem c22250R_94_40 : rowsJ2 94 95 87 360 ≤ 39089609153115 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2588 c22250R_94_41 (by norm_num)

theorem c22250R_94_39 : rowsJ2 94 95 86 360 ≤ 40678131382656 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2587 c22250R_94_40 (by norm_num)

theorem c22250R_94_38 : rowsJ2 94 95 85 360 ≤ 41863622649248 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2586 c22250R_94_39 (by norm_num)

theorem c22250R_94_37 : rowsJ2 94 95 84 360 ≤ 42708814268358 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2585 c22250R_94_38 (by norm_num)

theorem c22250R_94_36 : rowsJ2 94 95 82 360 ≤ 43596927316650 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2584 c22250R_94_37 (by norm_num)

theorem c22250R_94_35 : rowsJ2 94 95 79 360 ≤ 43810288369019 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2583 c22250R_94_36 (by norm_num)

theorem c22250R_94_34 : rowsJ2 94 95 75 360 ≤ 43810288369019 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2582 c22250R_94_35 (by norm_num)

theorem c22250R_94_33 : rowsJ2 94 95 71 360 ≤ 43810288369019 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2581 c22250R_94_34 (by norm_num)

theorem c22250R_94_32 : rowsJ2 94 95 68 360 ≤ 43810288369019 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2580 c22250R_94_33 (by norm_num)

theorem c22250R_94_31 : rowsJ2 94 95 66 360 ≤ 43810288369019 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2579 c22250R_94_32 (by norm_num)

theorem c22250R_94_30 : rowsJ2 94 95 64 360 ≤ 43810288369019 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2578 c22250R_94_31 (by norm_num)

theorem c22250R_94_29 : rowsJ2 94 95 62 360 ≤ 43810288369019 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2577 c22250R_94_30 (by norm_num)

theorem c22250R_94_28 : rowsJ2 94 95 61 360 ≤ 43810288369019 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2576 c22250R_94_29 (by norm_num)

theorem c22250R_94_27 : rowsJ2 94 95 60 360 ≤ 43810288369019 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2575 c22250R_94_28 (by norm_num)

theorem c22250R_94_26 : rowsJ2 94 95 59 360 ≤ 43810288369019 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2574 c22250R_94_27 (by norm_num)

theorem c22250R_94_25 : rowsJ2 94 95 58 360 ≤ 43810288369019 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2573 c22250R_94_26 (by norm_num)

theorem c22250R_94_24 : rowsJ2 94 95 57 360 ≤ 43810288369019 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2572 c22250R_94_25 (by norm_num)

theorem c22250R_94_23 : rowsJ2 94 95 56 360 ≤ 43810288369019 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2571 c22250R_94_24 (by norm_num)

theorem c22250R_94_22 : rowsJ2 94 95 55 360 ≤ 43810288369019 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2570 c22250R_94_23 (by norm_num)

theorem c22250R_94_21 : rowsJ2 94 95 54 360 ≤ 43810288369019 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2569 c22250R_94_22 (by norm_num)

theorem c22250R_94_20 : rowsJ2 94 95 53 360 ≤ 43810288369019 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2568 c22250R_94_21 (by norm_num)

theorem c22250R_94_19 : rowsJ2 94 95 52 360 ≤ 43810288369019 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2567 c22250R_94_20 (by norm_num)

theorem c22250R_94_18 : rowsJ2 94 95 51 360 ≤ 43810288369019 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2566 c22250R_94_19 (by norm_num)

theorem c22250R_94_17 : rowsJ2 94 95 50 360 ≤ 47143780828936 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2565 c22250R_94_18 (by norm_num)

theorem c22250R_94_16 : rowsJ2 94 95 49 360 ≤ 54144415626357 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2564 c22250R_94_17 (by norm_num)

theorem c22250R_94_15 : rowsJ2 94 95 48 360 ≤ 65557914574542 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2563 c22250R_94_16 (by norm_num)

theorem c22250R_94_14 : rowsJ2 94 95 47 360 ≤ 79307559777640 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2562 c22250R_94_15 (by norm_num)

theorem c22250R_94_13 : rowsJ2 94 95 46 360 ≤ 92086858195280 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2561 c22250R_94_14 (by norm_num)

theorem c22250R_94_12 : rowsJ2 94 95 45 360 ≤ 103752847871988 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2560 c22250R_94_13 (by norm_num)

theorem c22250R_94_11 : rowsJ2 94 95 44 360 ≤ 114221795678537 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2559 c22250R_94_12 (by norm_num)

theorem c22250R_94_10 : rowsJ2 94 95 43 360 ≤ 123501358205516 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2558 c22250R_94_11 (by norm_num)

theorem c22250R_94_9 : rowsJ2 94 95 42 360 ≤ 131601215801275 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2557 c22250R_94_10 (by norm_num)

theorem c22250R_94_8 : rowsJ2 94 95 41 360 ≤ 138533255024639 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2556 c22250R_94_9 (by norm_num)

theorem c22250R_94_7 : rowsJ2 94 95 39 360 ≤ 149292180239495 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2555 c22250R_94_8 (by norm_num)

theorem c22250R_94_6 : rowsJ2 94 95 37 360 ≤ 155638703075352 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2554 c22250R_94_7 (by norm_num)

theorem c22250R_94_5 : rowsJ2 94 95 33 360 ≤ 158796379525211 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2553 c22250R_94_6 (by norm_num)

theorem c22250R_94_4 : rowsJ2 94 95 27 360 ≤ 158796379525211 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2552 c22250R_94_5 (by norm_num)

theorem c22250R_94_3 : rowsJ2 94 95 23 360 ≤ 158796379525211 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2551 c22250R_94_4 (by norm_num)

theorem c22250R_94_2 : rowsJ2 94 95 20 360 ≤ 158796379525211 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2550 c22250R_94_3 (by norm_num)

theorem c22250R_94_1 : rowsJ2 94 95 17 360 ≤ 158796379525211 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2549 c22250R_94_2 (by norm_num)

theorem c22250R_94_0 : rowsJ2 94 95 0 360 ≤ 158796379525211 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22250R_2548 c22250R_94_1 (by norm_num)

theorem hr22250R_94 : rows2 94 95 ≤ 158796379525211 := rows2_le_of_rowsJ2 94 95 c22250R_94_0

theorem c22250R_95_47 : rowsJ2 95 96 94 360 ≤ 11141102293429 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2643 rows22250R_2644 (by norm_num)

theorem c22250R_95_46 : rowsJ2 95 96 93 360 ≤ 17641386623468 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2642 c22250R_95_47 (by norm_num)

theorem c22250R_95_45 : rowsJ2 95 96 92 360 ≤ 24056732109972 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2641 c22250R_95_46 (by norm_num)

theorem c22250R_95_44 : rowsJ2 95 96 91 360 ≤ 29492363584257 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2640 c22250R_95_45 (by norm_num)

theorem c22250R_95_43 : rowsJ2 95 96 90 360 ≤ 33879568717658 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2639 c22250R_95_44 (by norm_num)

theorem c22250R_95_42 : rowsJ2 95 96 89 360 ≤ 37361664778970 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2638 c22250R_95_43 (by norm_num)

theorem c22250R_95_41 : rowsJ2 95 96 88 360 ≤ 40084440065584 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2637 c22250R_95_42 (by norm_num)

theorem c22250R_95_40 : rowsJ2 95 96 87 360 ≤ 42169649924607 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2636 c22250R_95_41 (by norm_num)

theorem c22250R_95_39 : rowsJ2 95 96 86 360 ≤ 43746186528034 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2635 c22250R_95_40 (by norm_num)

theorem c22250R_95_38 : rowsJ2 95 96 85 360 ≤ 44923490629188 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2634 c22250R_95_39 (by norm_num)

theorem c22250R_95_37 : rowsJ2 95 96 84 360 ≤ 45762845238941 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2633 c22250R_95_38 (by norm_num)

theorem c22250R_95_36 : rowsJ2 95 96 83 360 ≤ 46315067161431 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2632 c22250R_95_37 (by norm_num)

theorem c22250R_95_35 : rowsJ2 95 96 81 360 ≤ 46803577127542 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2631 c22250R_95_36 (by norm_num)

theorem c22250R_95_34 : rowsJ2 95 96 78 360 ≤ 46856712408247 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2630 c22250R_95_35 (by norm_num)

theorem c22250R_95_33 : rowsJ2 95 96 74 360 ≤ 46856712408247 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2629 c22250R_95_34 (by norm_num)

theorem c22250R_95_32 : rowsJ2 95 96 70 360 ≤ 46856712408247 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2628 c22250R_95_33 (by norm_num)

theorem c22250R_95_31 : rowsJ2 95 96 67 360 ≤ 46856712408247 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2627 c22250R_95_32 (by norm_num)

theorem c22250R_95_30 : rowsJ2 95 96 65 360 ≤ 46856712408247 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2626 c22250R_95_31 (by norm_num)

theorem c22250R_95_29 : rowsJ2 95 96 63 360 ≤ 46856712408247 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2625 c22250R_95_30 (by norm_num)

theorem c22250R_95_28 : rowsJ2 95 96 61 360 ≤ 46856712408247 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2624 c22250R_95_29 (by norm_num)

theorem c22250R_95_27 : rowsJ2 95 96 60 360 ≤ 46856712408247 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2623 c22250R_95_28 (by norm_num)

theorem c22250R_95_26 : rowsJ2 95 96 59 360 ≤ 46856712408247 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2622 c22250R_95_27 (by norm_num)

theorem c22250R_95_25 : rowsJ2 95 96 58 360 ≤ 46856712408247 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2621 c22250R_95_26 (by norm_num)

theorem c22250R_95_24 : rowsJ2 95 96 57 360 ≤ 46856712408247 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2620 c22250R_95_25 (by norm_num)

theorem c22250R_95_23 : rowsJ2 95 96 56 360 ≤ 46856712408247 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2619 c22250R_95_24 (by norm_num)

theorem c22250R_95_22 : rowsJ2 95 96 55 360 ≤ 46856712408247 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2618 c22250R_95_23 (by norm_num)

theorem c22250R_95_21 : rowsJ2 95 96 54 360 ≤ 46856712408247 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2617 c22250R_95_22 (by norm_num)

theorem c22250R_95_20 : rowsJ2 95 96 53 360 ≤ 46856712408247 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2616 c22250R_95_21 (by norm_num)

theorem c22250R_95_19 : rowsJ2 95 96 52 360 ≤ 46856712408247 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2615 c22250R_95_20 (by norm_num)

theorem c22250R_95_18 : rowsJ2 95 96 51 360 ≤ 49379522080948 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2614 c22250R_95_19 (by norm_num)

theorem c22250R_95_17 : rowsJ2 95 96 50 360 ≤ 55195736159690 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2613 c22250R_95_18 (by norm_num)

theorem c22250R_95_16 : rowsJ2 95 96 49 360 ≤ 64686840044469 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2612 c22250R_95_17 (by norm_num)

theorem c22250R_95_15 : rowsJ2 95 96 48 360 ≤ 78551204966307 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2611 c22250R_95_16 (by norm_num)

theorem c22250R_95_14 : rowsJ2 95 96 47 360 ≤ 92747443496223 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2610 c22250R_95_15 (by norm_num)

theorem c22250R_95_13 : rowsJ2 95 96 46 360 ≤ 105957563316263 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2609 c22250R_95_14 (by norm_num)

theorem c22250R_95_12 : rowsJ2 95 96 45 360 ≤ 118082803844898 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2608 c22250R_95_13 (by norm_num)

theorem c22250R_95_11 : rowsJ2 95 96 44 360 ≤ 129025024502948 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2607 c22250R_95_12 (by norm_num)

theorem c22250R_95_10 : rowsJ2 95 96 43 360 ≤ 138791953036764 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2606 c22250R_95_11 (by norm_num)

theorem c22250R_95_9 : rowsJ2 95 96 42 360 ≤ 147393331027549 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2605 c22250R_95_10 (by norm_num)

theorem c22250R_95_8 : rowsJ2 95 96 41 360 ≤ 154841095262577 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2604 c22250R_95_9 (by norm_num)

theorem c22250R_95_7 : rowsJ2 95 96 40 360 ≤ 161149574875749 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2603 c22250R_95_8 (by norm_num)

theorem c22250R_95_6 : rowsJ2 95 96 38 360 ≤ 170432261689136 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2602 c22250R_95_7 (by norm_num)

theorem c22250R_95_5 : rowsJ2 95 96 35 360 ≤ 176287955602026 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2601 c22250R_95_6 (by norm_num)

theorem c22250R_95_4 : rowsJ2 95 96 29 360 ≤ 177081525300369 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2600 c22250R_95_5 (by norm_num)

theorem c22250R_95_3 : rowsJ2 95 96 24 360 ≤ 177081525300369 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2599 c22250R_95_4 (by norm_num)

theorem c22250R_95_2 : rowsJ2 95 96 20 360 ≤ 177081525300369 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2598 c22250R_95_3 (by norm_num)

theorem c22250R_95_1 : rowsJ2 95 96 17 360 ≤ 177081525300369 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2597 c22250R_95_2 (by norm_num)

theorem c22250R_95_0 : rowsJ2 95 96 0 360 ≤ 177081525300369 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22250R_2596 c22250R_95_1 (by norm_num)

theorem hr22250R_95 : rows2 95 96 ≤ 177081525300369 := rows2_le_of_rowsJ2 95 96 c22250R_95_0

theorem c22250R_96_46 : rowsJ2 96 97 95 360 ≤ 8875519238156 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2691 rows22250R_2692 (by norm_num)

theorem c22250R_96_45 : rowsJ2 96 97 94 360 ≤ 13855748949972 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2690 c22250R_96_46 (by norm_num)

theorem c22250R_96_44 : rowsJ2 96 97 93 360 ≤ 19405663947522 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2689 c22250R_96_45 (by norm_num)

theorem c22250R_96_43 : rowsJ2 96 97 92 360 ≤ 25594142677123 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2688 c22250R_96_44 (by norm_num)

theorem c22250R_96_42 : rowsJ2 96 97 91 360 ≤ 30953260088989 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2687 c22250R_96_43 (by norm_num)

theorem c22250R_96_41 : rowsJ2 96 97 90 360 ≤ 35334592117706 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2686 c22250R_96_42 (by norm_num)

theorem c22250R_96_40 : rowsJ2 96 97 89 360 ≤ 38805624953543 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2685 c22250R_96_41 (by norm_num)

theorem c22250R_96_39 : rowsJ2 96 97 88 360 ≤ 41514715662319 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2684 c22250R_96_40 (by norm_num)

theorem c22250R_96_38 : rowsJ2 96 97 87 360 ≤ 43586897242368 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2683 c22250R_96_39 (by norm_num)

theorem c22250R_96_37 : rowsJ2 96 97 86 360 ≤ 45152733996186 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2682 c22250R_96_38 (by norm_num)

theorem c22250R_96_36 : rowsJ2 96 97 85 360 ≤ 46320872156374 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2681 c22250R_96_37 (by norm_num)

theorem c22250R_96_35 : rowsJ2 96 97 84 360 ≤ 47154469826181 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2680 c22250R_96_36 (by norm_num)

theorem c22250R_96_34 : rowsJ2 96 97 83 360 ≤ 47702904185696 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2679 c22250R_96_35 (by norm_num)

theorem c22250R_96_33 : rowsJ2 96 97 81 360 ≤ 48188063574462 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2678 c22250R_96_34 (by norm_num)

theorem c22250R_96_32 : rowsJ2 96 97 77 360 ≤ 48240834412514 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2677 c22250R_96_33 (by norm_num)

theorem c22250R_96_31 : rowsJ2 96 97 73 360 ≤ 48240834412514 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2676 c22250R_96_32 (by norm_num)

theorem c22250R_96_30 : rowsJ2 96 97 69 360 ≤ 48240834412514 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2675 c22250R_96_31 (by norm_num)

theorem c22250R_96_29 : rowsJ2 96 97 66 360 ≤ 48240834412514 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2674 c22250R_96_30 (by norm_num)

theorem c22250R_96_28 : rowsJ2 96 97 64 360 ≤ 48240834412514 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2673 c22250R_96_29 (by norm_num)

theorem c22250R_96_27 : rowsJ2 96 97 62 360 ≤ 48240834412514 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2672 c22250R_96_28 (by norm_num)

theorem c22250R_96_26 : rowsJ2 96 97 60 360 ≤ 48240834412514 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2671 c22250R_96_27 (by norm_num)

theorem c22250R_96_25 : rowsJ2 96 97 59 360 ≤ 48240834412514 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2670 c22250R_96_26 (by norm_num)

theorem c22250R_96_24 : rowsJ2 96 97 58 360 ≤ 48240834412514 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2669 c22250R_96_25 (by norm_num)

theorem c22250R_96_23 : rowsJ2 96 97 57 360 ≤ 48240834412514 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2668 c22250R_96_24 (by norm_num)

theorem c22250R_96_22 : rowsJ2 96 97 56 360 ≤ 48240834412514 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2667 c22250R_96_23 (by norm_num)

theorem c22250R_96_21 : rowsJ2 96 97 55 360 ≤ 48240834412514 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2666 c22250R_96_22 (by norm_num)

theorem c22250R_96_20 : rowsJ2 96 97 54 360 ≤ 48240834412514 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2665 c22250R_96_21 (by norm_num)

theorem c22250R_96_19 : rowsJ2 96 97 53 360 ≤ 48240834412514 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2664 c22250R_96_20 (by norm_num)

theorem c22250R_96_18 : rowsJ2 96 97 52 360 ≤ 50509159442950 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2663 c22250R_96_19 (by norm_num)

theorem c22250R_96_17 : rowsJ2 96 97 51 360 ≤ 55308087743187 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2662 c22250R_96_18 (by norm_num)

theorem c22250R_96_16 : rowsJ2 96 97 50 360 ≤ 63407547511193 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2661 c22250R_96_17 (by norm_num)

theorem c22250R_96_15 : rowsJ2 96 97 49 360 ≤ 75143448879393 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2660 c22250R_96_16 (by norm_num)

theorem c22250R_96_14 : rowsJ2 96 97 48 360 ≤ 88301210628363 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2659 c22250R_96_15 (by norm_num)

theorem c22250R_96_13 : rowsJ2 96 97 47 360 ≤ 102974938613007 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2658 c22250R_96_14 (by norm_num)

theorem c22250R_96_12 : rowsJ2 96 97 46 360 ≤ 116692839944496 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2657 c22250R_96_13 (by norm_num)

theorem c22250R_96_11 : rowsJ2 96 97 45 360 ≤ 129309043244295 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2656 c22250R_96_12 (by norm_num)

theorem c22250R_96_10 : rowsJ2 96 97 44 360 ≤ 140724424374610 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2655 c22250R_96_11 (by norm_num)

theorem c22250R_96_9 : rowsJ2 96 97 43 360 ≤ 150978481960962 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2654 c22250R_96_10 (by norm_num)

theorem c22250R_96_8 : rowsJ2 96 97 42 360 ≤ 160081019475244 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2653 c22250R_96_9 (by norm_num)

theorem c22250R_96_7 : rowsJ2 96 97 41 360 ≤ 168044024791461 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2652 c22250R_96_8 (by norm_num)

theorem c22250R_96_6 : rowsJ2 96 97 39 360 ≤ 180611505337283 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2651 c22250R_96_7 (by norm_num)

theorem c22250R_96_5 : rowsJ2 96 97 36 360 ≤ 190400794788549 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2650 c22250R_96_6 (by norm_num)

theorem c22250R_96_4 : rowsJ2 96 97 30 360 ≤ 192507148661068 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2649 c22250R_96_5 (by norm_num)

theorem c22250R_96_3 : rowsJ2 96 97 24 360 ≤ 192507148661068 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2648 c22250R_96_4 (by norm_num)

theorem c22250R_96_2 : rowsJ2 96 97 20 360 ≤ 192507148661068 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2647 c22250R_96_3 (by norm_num)

theorem c22250R_96_1 : rowsJ2 96 97 17 360 ≤ 192507148661068 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2646 c22250R_96_2 (by norm_num)

theorem c22250R_96_0 : rowsJ2 96 97 0 360 ≤ 192507148661068 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22250R_2645 c22250R_96_1 (by norm_num)

theorem hr22250R_96 : rows2 96 97 ≤ 192507148661068 := rows2_le_of_rowsJ2 96 97 c22250R_96_0

theorem c22250R_97_47 : rowsJ2 97 98 96 360 ≤ 7914644211683 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2740 rows22250R_2741 (by norm_num)

theorem c22250R_97_46 : rowsJ2 97 98 95 360 ≤ 11958137005039 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2739 c22250R_97_47 (by norm_num)

theorem c22250R_97_45 : rowsJ2 97 98 94 360 ≤ 16147388634765 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2738 c22250R_97_46 (by norm_num)

theorem c22250R_97_44 : rowsJ2 97 98 93 360 ≤ 20834741144105 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2737 c22250R_97_45 (by norm_num)

theorem c22250R_97_43 : rowsJ2 97 98 92 360 ≤ 26092304207257 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2736 c22250R_97_44 (by norm_num)

theorem c22250R_97_42 : rowsJ2 97 98 91 360 ≤ 31297213117650 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2735 c22250R_97_43 (by norm_num)

theorem c22250R_97_41 : rowsJ2 97 98 90 360 ≤ 35674281959922 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2734 c22250R_97_42 (by norm_num)

theorem c22250R_97_40 : rowsJ2 97 98 89 360 ≤ 39135288118072 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2733 c22250R_97_41 (by norm_num)

theorem c22250R_97_39 : rowsJ2 97 98 88 360 ≤ 41831311644373 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2732 c22250R_97_40 (by norm_num)

theorem c22250R_97_38 : rowsJ2 97 98 87 360 ≤ 43890786920200 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2731 c22250R_97_39 (by norm_num)

theorem c22250R_97_37 : rowsJ2 97 98 86 360 ≤ 45444988416967 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2730 c22250R_97_38 (by norm_num)

theorem c22250R_97_36 : rowsJ2 97 98 85 360 ≤ 46605206929997 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2729 c22250R_97_37 (by norm_num)

theorem c22250R_97_35 : rowsJ2 97 98 84 360 ≤ 47433126092947 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2728 c22250R_97_36 (by norm_num)

theorem c22250R_97_34 : rowsJ2 97 98 83 360 ≤ 47977824491598 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2727 c22250R_97_35 (by norm_num)

theorem c22250R_97_33 : rowsJ2 97 98 81 360 ≤ 48459678951602 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2726 c22250R_97_34 (by norm_num)

theorem c22250R_97_32 : rowsJ2 97 98 77 360 ≤ 48512090312204 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2725 c22250R_97_33 (by norm_num)

theorem c22250R_97_31 : rowsJ2 97 98 72 360 ≤ 48512090312204 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2724 c22250R_97_32 (by norm_num)

theorem c22250R_97_30 : rowsJ2 97 98 68 360 ≤ 48512090312204 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2723 c22250R_97_31 (by norm_num)

theorem c22250R_97_29 : rowsJ2 97 98 65 360 ≤ 48512090312204 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2722 c22250R_97_30 (by norm_num)

theorem c22250R_97_28 : rowsJ2 97 98 63 360 ≤ 48512090312204 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2721 c22250R_97_29 (by norm_num)

theorem c22250R_97_27 : rowsJ2 97 98 61 360 ≤ 48512090312204 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2720 c22250R_97_28 (by norm_num)

theorem c22250R_97_26 : rowsJ2 97 98 59 360 ≤ 48512090312204 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2719 c22250R_97_27 (by norm_num)

theorem c22250R_97_25 : rowsJ2 97 98 58 360 ≤ 48512090312204 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2718 c22250R_97_26 (by norm_num)

theorem c22250R_97_24 : rowsJ2 97 98 57 360 ≤ 48512090312204 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2717 c22250R_97_25 (by norm_num)

theorem c22250R_97_23 : rowsJ2 97 98 56 360 ≤ 48512090312204 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2716 c22250R_97_24 (by norm_num)

theorem c22250R_97_22 : rowsJ2 97 98 55 360 ≤ 48512090312204 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2715 c22250R_97_23 (by norm_num)

theorem c22250R_97_21 : rowsJ2 97 98 54 360 ≤ 48512090312204 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2714 c22250R_97_22 (by norm_num)

theorem c22250R_97_20 : rowsJ2 97 98 53 360 ≤ 50175270729619 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2713 c22250R_97_21 (by norm_num)

theorem c22250R_97_19 : rowsJ2 97 98 52 360 ≤ 54110260320607 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2712 c22250R_97_20 (by norm_num)

theorem c22250R_97_18 : rowsJ2 97 98 51 360 ≤ 60580501756375 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2711 c22250R_97_19 (by norm_num)

theorem c22250R_97_17 : rowsJ2 97 98 50 360 ≤ 70307377745691 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2710 c22250R_97_18 (by norm_num)

theorem c22250R_97_16 : rowsJ2 97 98 49 360 ≤ 81316156550963 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2709 c22250R_97_17 (by norm_num)

theorem c22250R_97_15 : rowsJ2 97 98 48 360 ≤ 93696893169560 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2708 c22250R_97_16 (by norm_num)

theorem c22250R_97_14 : rowsJ2 97 98 47 360 ≤ 107590506933644 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2707 c22250R_97_15 (by norm_num)

theorem c22250R_97_13 : rowsJ2 97 98 46 360 ≤ 121772435457490 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2706 c22250R_97_14 (by norm_num)

theorem c22250R_97_12 : rowsJ2 97 98 45 360 ≤ 134881236961536 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2705 c22250R_97_13 (by norm_num)

theorem c22250R_97_11 : rowsJ2 97 98 44 360 ≤ 146770550299680 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2704 c22250R_97_12 (by norm_num)

theorem c22250R_97_10 : rowsJ2 97 98 43 360 ≤ 157433171294596 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2703 c22250R_97_11 (by norm_num)

theorem c22250R_97_9 : rowsJ2 97 98 42 360 ≤ 166957327985429 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2702 c22250R_97_10 (by norm_num)

theorem c22250R_97_8 : rowsJ2 97 98 41 360 ≤ 175355041377856 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2701 c22250R_97_9 (by norm_num)

theorem c22250R_97_7 : rowsJ2 97 98 40 360 ≤ 182640700477256 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2700 c22250R_97_8 (by norm_num)

theorem c22250R_97_6 : rowsJ2 97 98 38 360 ≤ 193526952641355 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2699 c22250R_97_7 (by norm_num)

theorem c22250R_97_5 : rowsJ2 97 98 36 360 ≤ 199544779625105 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2698 c22250R_97_6 (by norm_num)

theorem c22250R_97_4 : rowsJ2 97 98 32 360 ≤ 202128443263656 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2697 c22250R_97_5 (by norm_num)

theorem c22250R_97_3 : rowsJ2 97 98 25 360 ≤ 202128443263656 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2696 c22250R_97_4 (by norm_num)

theorem c22250R_97_2 : rowsJ2 97 98 20 360 ≤ 202128443263656 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2695 c22250R_97_3 (by norm_num)

theorem c22250R_97_1 : rowsJ2 97 98 16 360 ≤ 202128443263656 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2694 c22250R_97_2 (by norm_num)

theorem c22250R_97_0 : rowsJ2 97 98 0 360 ≤ 202128443263656 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22250R_2693 c22250R_97_1 (by norm_num)

theorem hr22250R_97 : rows2 97 98 ≤ 202128443263656 := rows2_le_of_rowsJ2 97 98 c22250R_97_0

theorem c22250R_98_47 : rowsJ2 98 99 97 360 ≤ 7377478570729 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2789 rows22250R_2790 (by norm_num)

theorem c22250R_98_46 : rowsJ2 98 99 96 360 ≤ 10993332568087 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2788 c22250R_98_47 (by norm_num)

theorem c22250R_98_45 : rowsJ2 98 99 95 360 ≤ 14642848074636 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2787 c22250R_98_46 (by norm_num)

theorem c22250R_98_44 : rowsJ2 98 99 94 360 ≤ 18397657134866 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2786 c22250R_98_45 (by norm_num)

theorem c22250R_98_43 : rowsJ2 98 99 93 360 ≤ 22312975936934 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2785 c22250R_98_44 (by norm_num)

theorem c22250R_98_42 : rowsJ2 98 99 92 360 ≤ 26726888611678 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2784 c22250R_98_43 (by norm_num)

theorem c22250R_98_41 : rowsJ2 98 99 91 360 ≤ 31697625831052 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2783 c22250R_98_42 (by norm_num)

theorem c22250R_98_40 : rowsJ2 98 99 90 360 ≤ 35993072689791 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2782 c22250R_98_41 (by norm_num)

theorem c22250R_98_39 : rowsJ2 98 99 89 360 ≤ 39445112407755 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2781 c22250R_98_40 (by norm_num)

theorem c22250R_98_38 : rowsJ2 98 99 88 360 ≤ 42129785168040 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2780 c22250R_98_39 (by norm_num)

theorem c22250R_98_37 : rowsJ2 98 99 87 360 ≤ 44175804960392 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2779 c22250R_98_38 (by norm_num)

theorem c22250R_98_36 : rowsJ2 98 99 86 360 ≤ 45718559342408 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2778 c22250R_98_37 (by norm_num)

theorem c22250R_98_35 : rowsJ2 98 99 85 360 ≤ 46870965661085 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2777 c22250R_98_36 (by norm_num)

theorem c22250R_98_34 : rowsJ2 98 99 84 360 ≤ 47693283158256 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2776 c22250R_98_35 (by norm_num)

theorem c22250R_98_33 : rowsJ2 98 99 83 360 ≤ 48234296150748 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2775 c22250R_98_34 (by norm_num)

theorem c22250R_98_32 : rowsJ2 98 99 81 360 ≤ 48712890404007 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2774 c22250R_98_33 (by norm_num)

theorem c22250R_98_31 : rowsJ2 98 99 77 360 ≤ 48764947151575 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2773 c22250R_98_32 (by norm_num)

theorem c22250R_98_30 : rowsJ2 98 99 72 360 ≤ 48764947151575 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2772 c22250R_98_31 (by norm_num)

theorem c22250R_98_29 : rowsJ2 98 99 67 360 ≤ 48764947151575 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2771 c22250R_98_30 (by norm_num)

theorem c22250R_98_28 : rowsJ2 98 99 64 360 ≤ 48764947151575 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2770 c22250R_98_29 (by norm_num)

theorem c22250R_98_27 : rowsJ2 98 99 62 360 ≤ 48764947151575 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2769 c22250R_98_28 (by norm_num)

theorem c22250R_98_26 : rowsJ2 98 99 60 360 ≤ 48764947151575 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2768 c22250R_98_27 (by norm_num)

theorem c22250R_98_25 : rowsJ2 98 99 58 360 ≤ 48764947151575 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2767 c22250R_98_26 (by norm_num)

theorem c22250R_98_24 : rowsJ2 98 99 57 360 ≤ 48764947151575 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2766 c22250R_98_25 (by norm_num)

theorem c22250R_98_23 : rowsJ2 98 99 56 360 ≤ 48764947151575 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2765 c22250R_98_24 (by norm_num)

theorem c22250R_98_22 : rowsJ2 98 99 55 360 ≤ 48764947151575 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2764 c22250R_98_23 (by norm_num)

theorem c22250R_98_21 : rowsJ2 98 99 54 360 ≤ 50188367214947 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2763 c22250R_98_22 (by norm_num)

theorem c22250R_98_20 : rowsJ2 98 99 53 360 ≤ 53280167882521 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2762 c22250R_98_21 (by norm_num)

theorem c22250R_98_19 : rowsJ2 98 99 52 360 ≤ 58647763276049 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2761 c22250R_98_20 (by norm_num)

theorem c22250R_98_18 : rowsJ2 98 99 51 360 ≤ 66555754690604 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2760 c22250R_98_19 (by norm_num)

theorem c22250R_98_17 : rowsJ2 98 99 50 360 ≤ 75609209475221 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2759 c22250R_98_18 (by norm_num)

theorem c22250R_98_16 : rowsJ2 98 99 49 360 ≤ 85894410291886 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2758 c22250R_98_17 (by norm_num)

theorem c22250R_98_15 : rowsJ2 98 99 48 360 ≤ 97549001515614 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2757 c22250R_98_16 (by norm_num)

theorem c22250R_98_14 : rowsJ2 98 99 47 360 ≤ 110666704617016 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2756 c22250R_98_15 (by norm_num)

theorem c22250R_98_13 : rowsJ2 98 99 46 360 ≤ 125392488206256 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2755 c22250R_98_14 (by norm_num)

theorem c22250R_98_12 : rowsJ2 98 99 45 360 ≤ 139027626023424 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2754 c22250R_98_13 (by norm_num)

theorem c22250R_98_11 : rowsJ2 98 99 44 360 ≤ 151470938978193 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2753 c22250R_98_12 (by norm_num)

theorem c22250R_98_10 : rowsJ2 98 99 43 360 ≤ 162621800079426 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2752 c22250R_98_11 (by norm_num)

theorem c22250R_98_9 : rowsJ2 98 99 42 360 ≤ 172567600952852 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2751 c22250R_98_10 (by norm_num)

theorem c22250R_98_8 : rowsJ2 98 99 41 360 ≤ 181399933419771 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2750 c22250R_98_9 (by norm_num)

theorem c22250R_98_7 : rowsJ2 98 99 40 360 ≤ 189133208361802 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2749 c22250R_98_8 (by norm_num)

theorem c22250R_98_6 : rowsJ2 98 99 39 360 ≤ 195784403066189 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2748 c22250R_98_7 (by norm_num)

theorem c22250R_98_5 : rowsJ2 98 99 37 360 ≤ 204651415458203 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2747 c22250R_98_6 (by norm_num)

theorem c22250R_98_4 : rowsJ2 98 99 33 360 ≤ 210567655948588 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2746 c22250R_98_5 (by norm_num)

theorem c22250R_98_3 : rowsJ2 98 99 25 360 ≤ 210648735883327 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2745 c22250R_98_4 (by norm_num)

theorem c22250R_98_2 : rowsJ2 98 99 20 360 ≤ 210648735883327 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2744 c22250R_98_3 (by norm_num)

theorem c22250R_98_1 : rowsJ2 98 99 16 360 ≤ 210648735883327 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2743 c22250R_98_2 (by norm_num)

theorem c22250R_98_0 : rowsJ2 98 99 0 360 ≤ 210648735883327 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22250R_2742 c22250R_98_1 (by norm_num)

theorem hr22250R_98 : rows2 98 99 ≤ 210648735883327 := rows2_le_of_rowsJ2 98 99 c22250R_98_0

theorem c22250R_99_47 : rowsJ2 99 100 98 360 ≤ 7226897494312 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2838 rows22250R_2839 (by norm_num)

theorem c22250R_99_46 : rowsJ2 99 100 97 360 ≤ 10592771978508 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2837 c22250R_99_47 (by norm_num)

theorem c22250R_99_45 : rowsJ2 99 100 96 360 ≤ 13889896491685 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2836 c22250R_99_46 (by norm_num)

theorem c22250R_99_44 : rowsJ2 99 100 95 360 ≤ 17177648809271 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2835 c22250R_99_45 (by norm_num)

theorem c22250R_99_43 : rowsJ2 99 100 94 360 ≤ 20527985802344 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2834 c22250R_99_44 (by norm_num)

theorem c22250R_99_42 : rowsJ2 99 100 93 360 ≤ 23998642432884 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2833 c22250R_99_43 (by norm_num)

theorem c22250R_99_41 : rowsJ2 99 100 92 360 ≤ 27658922550042 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2832 c22250R_99_42 (by norm_num)

theorem c22250R_99_40 : rowsJ2 99 100 91 360 ≤ 31804466112707 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2831 c22250R_99_41 (by norm_num)

theorem c22250R_99_39 : rowsJ2 99 100 90 360 ≤ 35939864829771 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2830 c22250R_99_40 (by norm_num)

theorem c22250R_99_38 : rowsJ2 99 100 89 360 ≤ 39384045293307 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2829 c22250R_99_39 (by norm_num)

theorem c22250R_99_37 : rowsJ2 99 100 88 360 ≤ 42056909669605 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2828 c22250R_99_38 (by norm_num)

theorem c22250R_99_36 : rowsJ2 99 100 87 360 ≤ 44090929089613 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2827 c22250R_99_37 (by norm_num)

theorem c22250R_99_35 : rowsJ2 99 100 86 360 ≤ 45622421163319 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2826 c22250R_99_36 (by norm_num)

theorem c22250R_99_34 : rowsJ2 99 100 85 360 ≤ 46766037183304 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2825 c22250R_99_35 (by norm_num)

theorem c22250R_99_33 : rowsJ2 99 100 84 360 ≤ 47582828306532 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2824 c22250R_99_34 (by norm_num)

theorem c22250R_99_32 : rowsJ2 99 100 83 360 ≤ 48120205428316 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2823 c22250R_99_33 (by norm_num)

theorem c22250R_99_31 : rowsJ2 99 100 80 360 ≤ 48647290196065 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2822 c22250R_99_32 (by norm_num)

theorem c22250R_99_30 : rowsJ2 99 100 76 360 ≤ 48647290196065 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2821 c22250R_99_31 (by norm_num)

theorem c22250R_99_29 : rowsJ2 99 100 71 360 ≤ 48647290196065 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2820 c22250R_99_30 (by norm_num)

theorem c22250R_99_28 : rowsJ2 99 100 66 360 ≤ 48647290196065 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2819 c22250R_99_29 (by norm_num)

theorem c22250R_99_27 : rowsJ2 99 100 63 360 ≤ 48647290196065 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2818 c22250R_99_28 (by norm_num)

theorem c22250R_99_26 : rowsJ2 99 100 61 360 ≤ 48647290196065 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2817 c22250R_99_27 (by norm_num)

theorem c22250R_99_25 : rowsJ2 99 100 59 360 ≤ 48647290196065 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2816 c22250R_99_26 (by norm_num)

theorem c22250R_99_24 : rowsJ2 99 100 57 360 ≤ 48647290196065 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2815 c22250R_99_25 (by norm_num)

theorem c22250R_99_23 : rowsJ2 99 100 56 360 ≤ 48647290196065 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2814 c22250R_99_24 (by norm_num)

theorem c22250R_99_22 : rowsJ2 99 100 55 360 ≤ 49504129228347 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2813 c22250R_99_23 (by norm_num)

theorem c22250R_99_21 : rowsJ2 99 100 54 360 ≤ 51785967429390 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2812 c22250R_99_22 (by norm_num)

theorem c22250R_99_20 : rowsJ2 99 100 53 360 ≤ 55688256253222 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2811 c22250R_99_21 (by norm_num)

theorem c22250R_99_19 : rowsJ2 99 100 52 360 ≤ 61818409222276 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2810 c22250R_99_20 (by norm_num)

theorem c22250R_99_18 : rowsJ2 99 100 51 360 ≤ 69032435504991 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2809 c22250R_99_19 (by norm_num)

theorem c22250R_99_17 : rowsJ2 99 100 50 360 ≤ 77340676073143 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2808 c22250R_99_18 (by norm_num)

theorem c22250R_99_16 : rowsJ2 99 100 49 360 ≤ 86877799819763 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2807 c22250R_99_17 (by norm_num)

theorem c22250R_99_15 : rowsJ2 99 100 48 360 ≤ 97733535324921 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2806 c22250R_99_16 (by norm_num)

theorem c22250R_99_14 : rowsJ2 99 100 47 360 ≤ 110049341492073 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2805 c22250R_99_15 (by norm_num)

theorem c22250R_99_13 : rowsJ2 99 100 46 360 ≤ 123922808337615 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2804 c22250R_99_14 (by norm_num)

theorem c22250R_99_12 : rowsJ2 99 100 45 360 ≤ 138086995485962 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2803 c22250R_99_13 (by norm_num)

theorem c22250R_99_11 : rowsJ2 99 100 44 360 ≤ 151039881478877 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2802 c22250R_99_12 (by norm_num)

theorem c22250R_99_10 : rowsJ2 99 100 43 360 ≤ 162679835762297 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2801 c22250R_99_11 (by norm_num)

theorem c22250R_99_9 : rowsJ2 99 100 42 360 ≤ 173046869665231 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2800 c22250R_99_10 (by norm_num)

theorem c22250R_99_8 : rowsJ2 99 100 41 360 ≤ 182231671579411 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2799 c22250R_99_9 (by norm_num)

theorem c22250R_99_7 : rowsJ2 99 100 40 360 ≤ 190329388281546 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2798 c22250R_99_8 (by norm_num)

theorem c22250R_99_6 : rowsJ2 99 100 39 360 ≤ 197356986255522 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2797 c22250R_99_7 (by norm_num)

theorem c22250R_99_5 : rowsJ2 99 100 37 360 ≤ 207003377118610 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2796 c22250R_99_6 (by norm_num)

theorem c22250R_99_4 : rowsJ2 99 100 34 360 ≤ 213399646532373 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2795 c22250R_99_5 (by norm_num)

theorem c22250R_99_3 : rowsJ2 99 100 26 360 ≤ 213959753630567 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2794 c22250R_99_4 (by norm_num)

theorem c22250R_99_2 : rowsJ2 99 100 20 360 ≤ 213959753630567 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2793 c22250R_99_3 (by norm_num)

theorem c22250R_99_1 : rowsJ2 99 100 16 360 ≤ 213959753630567 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2792 c22250R_99_2 (by norm_num)

theorem c22250R_99_0 : rowsJ2 99 100 0 360 ≤ 213959753630567 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22250R_2791 c22250R_99_1 (by norm_num)

theorem hr22250R_99 : rows2 99 100 ≤ 213959753630567 := rows2_le_of_rowsJ2 99 100 c22250R_99_0

theorem c22250R_100_46 : rowsJ2 100 101 99 360 ≤ 7508643769227 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2886 rows22250R_2887 (by norm_num)

theorem c22250R_100_45 : rowsJ2 100 101 98 360 ≤ 10855009471705 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2885 c22250R_100_46 (by norm_num)

theorem c22250R_100_44 : rowsJ2 100 101 97 360 ≤ 14008914789606 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2884 c22250R_100_45 (by norm_num)

theorem c22250R_100_43 : rowsJ2 100 101 96 360 ≤ 17048209945304 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2883 c22250R_100_44 (by norm_num)

theorem c22250R_100_42 : rowsJ2 100 101 95 360 ≤ 20033973971114 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2882 c22250R_100_43 (by norm_num)

theorem c22250R_100_41 : rowsJ2 100 101 94 360 ≤ 23039681272250 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2881 c22250R_100_42 (by norm_num)

theorem c22250R_100_40 : rowsJ2 100 101 93 360 ≤ 26123480212365 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2880 c22250R_100_41 (by norm_num)

theorem c22250R_100_39 : rowsJ2 100 101 92 360 ≤ 29357095606933 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2879 c22250R_100_40 (by norm_num)

theorem c22250R_100_38 : rowsJ2 100 101 91 360 ≤ 32766977030906 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2878 c22250R_100_39 (by norm_num)

theorem c22250R_100_37 : rowsJ2 100 101 90 360 ≤ 36662637381917 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2877 c22250R_100_38 (by norm_num)

theorem c22250R_100_36 : rowsJ2 100 101 89 360 ≤ 40020993164120 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2876 c22250R_100_37 (by norm_num)

theorem c22250R_100_35 : rowsJ2 100 101 88 360 ≤ 42682721978589 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2875 c22250R_100_36 (by norm_num)

theorem c22250R_100_34 : rowsJ2 100 101 87 360 ≤ 44705071572174 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2874 c22250R_100_35 (by norm_num)

theorem c22250R_100_33 : rowsJ2 100 101 86 360 ≤ 46225492575809 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2873 c22250R_100_34 (by norm_num)

theorem c22250R_100_32 : rowsJ2 100 101 85 360 ≤ 47360465760084 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2872 c22250R_100_33 (by norm_num)

theorem c22250R_100_31 : rowsJ2 100 101 84 360 ≤ 48171804293353 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2871 c22250R_100_32 (by norm_num)

theorem c22250R_100_30 : rowsJ2 100 101 82 360 ≤ 49024345092022 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2870 c22250R_100_31 (by norm_num)

theorem c22250R_100_29 : rowsJ2 100 101 79 360 ≤ 49229160236155 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2869 c22250R_100_30 (by norm_num)

theorem c22250R_100_28 : rowsJ2 100 101 75 360 ≤ 49229160236155 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2868 c22250R_100_29 (by norm_num)

theorem c22250R_100_27 : rowsJ2 100 101 70 360 ≤ 49229160236155 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2867 c22250R_100_28 (by norm_num)

theorem c22250R_100_26 : rowsJ2 100 101 65 360 ≤ 49229160236155 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2866 c22250R_100_27 (by norm_num)

theorem c22250R_100_25 : rowsJ2 100 101 62 360 ≤ 49229160236155 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2865 c22250R_100_26 (by norm_num)

theorem c22250R_100_24 : rowsJ2 100 101 60 360 ≤ 49229160236155 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2864 c22250R_100_25 (by norm_num)

theorem c22250R_100_23 : rowsJ2 100 101 58 360 ≤ 49229160236155 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2863 c22250R_100_24 (by norm_num)

theorem c22250R_100_22 : rowsJ2 100 101 56 360 ≤ 49888585937064 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2862 c22250R_100_23 (by norm_num)

theorem c22250R_100_21 : rowsJ2 100 101 55 360 ≤ 51407704227374 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2861 c22250R_100_22 (by norm_num)

theorem c22250R_100_20 : rowsJ2 100 101 54 360 ≤ 54301169473847 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2860 c22250R_100_21 (by norm_num)

theorem c22250R_100_19 : rowsJ2 100 101 53 360 ≤ 58818202930949 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2859 c22250R_100_20 (by norm_num)

theorem c22250R_100_18 : rowsJ2 100 101 52 360 ≤ 64308264883552 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2858 c22250R_100_19 (by norm_num)

theorem c22250R_100_17 : rowsJ2 100 101 51 360 ≤ 70830844211459 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2857 c22250R_100_18 (by norm_num)

theorem c22250R_100_16 : rowsJ2 100 101 50 360 ≤ 78445191641077 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2856 c22250R_100_17 (by norm_num)

theorem c22250R_100_15 : rowsJ2 100 101 49 360 ≤ 87237322053879 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2855 c22250R_100_16 (by norm_num)

theorem c22250R_100_14 : rowsJ2 100 101 48 360 ≤ 97345513911110 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2854 c22250R_100_15 (by norm_num)

theorem c22250R_100_13 : rowsJ2 100 101 47 360 ≤ 108863146054248 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2853 c22250R_100_14 (by norm_num)

theorem c22250R_100_12 : rowsJ2 100 101 46 360 ≤ 121935717729940 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2852 c22250R_100_13 (by norm_num)

theorem c22250R_100_11 : rowsJ2 100 101 45 360 ≤ 136580723406690 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2851 c22250R_100_12 (by norm_num)

theorem c22250R_100_10 : rowsJ2 100 101 44 360 ≤ 150126317293103 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2850 c22250R_100_11 (by norm_num)

theorem c22250R_100_9 : rowsJ2 100 101 43 360 ≤ 162338386608416 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2849 c22250R_100_10 (by norm_num)

theorem c22250R_100_8 : rowsJ2 100 101 42 360 ≤ 173209236810386 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2848 c22250R_100_9 (by norm_num)

theorem c22250R_100_7 : rowsJ2 100 101 41 360 ≤ 182828706797931 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2847 c22250R_100_8 (by norm_num)

theorem c22250R_100_6 : rowsJ2 100 101 40 360 ≤ 191290988970477 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2846 c22250R_100_7 (by norm_num)

theorem c22250R_100_5 : rowsJ2 100 101 38 360 ≤ 204632334665819 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2845 c22250R_100_6 (by norm_num)

theorem c22250R_100_4 : rowsJ2 100 101 35 360 ≤ 214714499133876 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2844 c22250R_100_5 (by norm_num)

theorem c22250R_100_3 : rowsJ2 100 101 29 360 ≤ 217119291379176 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2843 c22250R_100_4 (by norm_num)

theorem c22250R_100_2 : rowsJ2 100 101 21 360 ≤ 217119291379176 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2842 c22250R_100_3 (by norm_num)

theorem c22250R_100_1 : rowsJ2 100 101 16 360 ≤ 217119291379176 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2841 c22250R_100_2 (by norm_num)

theorem c22250R_100_0 : rowsJ2 100 101 0 360 ≤ 217119291379176 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22250R_2840 c22250R_100_1 (by norm_num)

theorem hr22250R_100 : rows2 100 101 ≤ 217119291379176 := rows2_le_of_rowsJ2 100 101 c22250R_100_0

theorem c22250R_101_47 : rowsJ2 101 102 100 360 ≤ 8078210992482 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2935 rows22250R_2936 (by norm_num)

theorem c22250R_101_46 : rowsJ2 101 102 99 360 ≤ 11569872867297 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2934 c22250R_101_47 (by norm_num)

theorem c22250R_101_45 : rowsJ2 101 102 98 360 ≤ 14788879688751 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2933 c22250R_101_46 (by norm_num)

theorem c22250R_101_44 : rowsJ2 101 102 97 360 ≤ 17766333684889 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2932 c22250R_101_45 (by norm_num)

theorem c22250R_101_43 : rowsJ2 101 102 96 360 ≤ 20580774618297 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2931 c22250R_101_44 (by norm_num)

theorem c22250R_101_42 : rowsJ2 101 102 95 360 ≤ 23296130182121 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2930 c22250R_101_43 (by norm_num)

theorem c22250R_101_41 : rowsJ2 101 102 94 360 ≤ 25987474319410 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2929 c22250R_101_42 (by norm_num)

theorem c22250R_101_40 : rowsJ2 101 102 93 360 ≤ 28714557424836 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2928 c22250R_101_41 (by norm_num)

theorem c22250R_101_39 : rowsJ2 101 102 92 360 ≤ 31549417410807 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2927 c22250R_101_40 (by norm_num)

theorem c22250R_101_38 : rowsJ2 101 102 91 360 ≤ 34550246992999 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2926 c22250R_101_39 (by norm_num)

theorem c22250R_101_37 : rowsJ2 101 102 90 360 ≤ 37727709997253 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2925 c22250R_101_38 (by norm_num)

theorem c22250R_101_36 : rowsJ2 101 102 89 360 ≤ 40922223200132 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2924 c22250R_101_37 (by norm_num)

theorem c22250R_101_35 : rowsJ2 101 102 88 360 ≤ 43573512636267 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2923 c22250R_101_36 (by norm_num)

theorem c22250R_101_34 : rowsJ2 101 102 87 360 ≤ 45583461246389 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2922 c22250R_101_35 (by norm_num)

theorem c22250R_101_33 : rowsJ2 101 102 86 360 ≤ 47092989743493 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2921 c22250R_101_34 (by norm_num)

theorem c22250R_101_32 : rowsJ2 101 102 85 360 ≤ 48220550198322 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2920 c22250R_101_33 (by norm_num)

theorem c22250R_101_31 : rowsJ2 101 102 84 360 ≤ 49025423393213 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2919 c22250R_101_32 (by norm_num)

theorem c22250R_101_30 : rowsJ2 101 102 82 360 ≤ 49872310691199 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2918 c22250R_101_31 (by norm_num)

theorem c22250R_101_29 : rowsJ2 101 102 79 360 ≤ 50075767633400 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2917 c22250R_101_30 (by norm_num)

theorem c22250R_101_28 : rowsJ2 101 102 75 360 ≤ 50075767633400 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2916 c22250R_101_29 (by norm_num)

theorem c22250R_101_27 : rowsJ2 101 102 69 360 ≤ 50075767633400 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2915 c22250R_101_28 (by norm_num)

theorem c22250R_101_26 : rowsJ2 101 102 64 360 ≤ 50075767633400 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2914 c22250R_101_27 (by norm_num)

theorem c22250R_101_25 : rowsJ2 101 102 61 360 ≤ 50075767633400 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2913 c22250R_101_26 (by norm_num)

theorem c22250R_101_24 : rowsJ2 101 102 59 360 ≤ 50075767633400 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2912 c22250R_101_25 (by norm_num)

theorem c22250R_101_23 : rowsJ2 101 102 57 360 ≤ 50342545204465 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2911 c22250R_101_24 (by norm_num)

theorem c22250R_101_22 : rowsJ2 101 102 55 360 ≤ 52940781503038 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2910 c22250R_101_23 (by norm_num)

theorem c22250R_101_21 : rowsJ2 101 102 54 360 ≤ 55990161393843 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2909 c22250R_101_22 (by norm_num)

theorem c22250R_101_20 : rowsJ2 101 102 53 360 ≤ 59898156600769 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2908 c22250R_101_21 (by norm_num)

theorem c22250R_101_19 : rowsJ2 101 102 52 360 ≤ 64725434837143 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2907 c22250R_101_20 (by norm_num)

theorem c22250R_101_18 : rowsJ2 101 102 51 360 ≤ 70532253269284 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2906 c22250R_101_19 (by norm_num)

theorem c22250R_101_17 : rowsJ2 101 102 50 360 ≤ 77378558227531 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2905 c22250R_101_18 (by norm_num)

theorem c22250R_101_16 : rowsJ2 101 102 49 360 ≤ 85399749415767 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2904 c22250R_101_17 (by norm_num)

theorem c22250R_101_15 : rowsJ2 101 102 48 360 ≤ 94685271473563 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2903 c22250R_101_16 (by norm_num)

theorem c22250R_101_14 : rowsJ2 101 102 47 360 ≤ 105377208635070 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2902 c22250R_101_15 (by norm_num)

theorem c22250R_101_13 : rowsJ2 101 102 46 360 ≤ 117572791689536 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2901 c22250R_101_14 (by norm_num)

theorem c22250R_101_12 : rowsJ2 101 102 45 360 ≤ 131337253839016 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2900 c22250R_101_13 (by norm_num)

theorem c22250R_101_11 : rowsJ2 101 102 44 360 ≤ 145346010464559 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2899 c22250R_101_12 (by norm_num)

theorem c22250R_101_10 : rowsJ2 101 102 43 360 ≤ 158132520527531 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2898 c22250R_101_11 (by norm_num)

theorem c22250R_101_9 : rowsJ2 101 102 42 360 ≤ 169508122059186 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2897 c22250R_101_10 (by norm_num)

theorem c22250R_101_8 : rowsJ2 101 102 41 360 ≤ 179561840630607 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2896 c22250R_101_9 (by norm_num)

theorem c22250R_101_7 : rowsJ2 101 102 40 360 ≤ 188386948645051 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2895 c22250R_101_8 (by norm_num)

theorem c22250R_101_6 : rowsJ2 101 102 39 360 ≤ 196081343922611 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2894 c22250R_101_7 (by norm_num)

theorem c22250R_101_5 : rowsJ2 101 102 37 360 ≤ 207288598398146 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2893 c22250R_101_6 (by norm_num)

theorem c22250R_101_4 : rowsJ2 101 102 35 360 ≤ 213353102468907 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2892 c22250R_101_5 (by norm_num)

theorem c22250R_101_3 : rowsJ2 101 102 30 360 ≤ 216415678632771 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2891 c22250R_101_4 (by norm_num)

theorem c22250R_101_2 : rowsJ2 101 102 21 360 ≤ 216415678632771 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2890 c22250R_101_3 (by norm_num)

theorem c22250R_101_1 : rowsJ2 101 102 16 360 ≤ 216415678632771 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2889 c22250R_101_2 (by norm_num)

theorem c22250R_101_0 : rowsJ2 101 102 0 360 ≤ 216415678632771 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22250R_2888 c22250R_101_1 (by norm_num)

theorem hr22250R_101 : rows2 101 102 ≤ 216415678632771 := rows2_le_of_rowsJ2 101 102 c22250R_101_0

theorem c22250R_102_47 : rowsJ2 102 103 101 360 ≤ 9011470872956 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2984 rows22250R_2985 (by norm_num)

theorem c22250R_102_46 : rowsJ2 102 103 100 360 ≤ 12828310192007 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2983 c22250R_102_47 (by norm_num)

theorem c22250R_102_45 : rowsJ2 102 103 99 360 ≤ 16273373200068 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2982 c22250R_102_46 (by norm_num)

theorem c22250R_102_44 : rowsJ2 102 103 98 360 ≤ 19394685497894 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2981 c22250R_102_45 (by norm_num)

theorem c22250R_102_43 : rowsJ2 102 103 97 360 ≤ 22259213816061 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2980 c22250R_102_44 (by norm_num)

theorem c22250R_102_42 : rowsJ2 102 103 96 360 ≤ 24912062494118 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2979 c22250R_102_43 (by norm_num)

theorem c22250R_102_41 : rowsJ2 102 103 95 360 ≤ 27417934253506 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2978 c22250R_102_42 (by norm_num)

theorem c22250R_102_40 : rowsJ2 102 103 94 360 ≤ 29854653802817 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2977 c22250R_102_41 (by norm_num)

theorem c22250R_102_39 : rowsJ2 102 103 93 360 ≤ 32283656778239 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2976 c22250R_102_40 (by norm_num)

theorem c22250R_102_38 : rowsJ2 102 103 92 360 ≤ 34778486914696 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2975 c22250R_102_39 (by norm_num)

theorem c22250R_102_37 : rowsJ2 102 103 91 360 ≤ 37397735177422 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2974 c22250R_102_38 (by norm_num)

theorem c22250R_102_36 : rowsJ2 102 103 90 360 ≤ 40183300319313 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2973 c22250R_102_37 (by norm_num)

theorem c22250R_102_35 : rowsJ2 102 103 89 360 ≤ 43132426968159 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2972 c22250R_102_36 (by norm_num)

theorem c22250R_102_34 : rowsJ2 102 103 88 360 ≤ 45695856456586 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2971 c22250R_102_35 (by norm_num)

theorem c22250R_102_33 : rowsJ2 102 103 87 360 ≤ 47693788859611 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2970 c22250R_102_34 (by norm_num)

theorem c22250R_102_32 : rowsJ2 102 103 86 360 ≤ 49192600356992 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2969 c22250R_102_33 (by norm_num)

theorem c22250R_102_31 : rowsJ2 102 103 85 360 ≤ 50311770327559 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2968 c22250R_102_32 (by norm_num)

theorem c22250R_102_30 : rowsJ2 102 103 84 360 ≤ 51111379202517 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2967 c22250R_102_31 (by norm_num)

theorem c22250R_102_29 : rowsJ2 102 103 82 360 ≤ 51952687486610 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2966 c22250R_102_30 (by norm_num)

theorem c22250R_102_28 : rowsJ2 102 103 79 360 ≤ 52154804121653 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2965 c22250R_102_29 (by norm_num)

theorem c22250R_102_27 : rowsJ2 102 103 74 360 ≤ 52154804121653 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2964 c22250R_102_28 (by norm_num)

theorem c22250R_102_26 : rowsJ2 102 103 68 360 ≤ 52154804121653 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2963 c22250R_102_27 (by norm_num)

theorem c22250R_102_25 : rowsJ2 102 103 63 360 ≤ 52154804121653 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2962 c22250R_102_26 (by norm_num)

theorem c22250R_102_24 : rowsJ2 102 103 60 360 ≤ 52154804121653 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2961 c22250R_102_25 (by norm_num)

theorem c22250R_102_23 : rowsJ2 102 103 58 360 ≤ 52289693674351 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2960 c22250R_102_24 (by norm_num)

theorem c22250R_102_22 : rowsJ2 102 103 56 360 ≤ 53697865684781 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2959 c22250R_102_23 (by norm_num)

theorem c22250R_102_21 : rowsJ2 102 103 54 360 ≤ 58058448666217 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2958 c22250R_102_22 (by norm_num)

theorem c22250R_102_20 : rowsJ2 102 103 53 360 ≤ 61412056472156 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2957 c22250R_102_21 (by norm_num)

theorem c22250R_102_19 : rowsJ2 102 103 52 360 ≤ 65630188052805 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2956 c22250R_102_20 (by norm_num)

theorem c22250R_102_18 : rowsJ2 102 103 51 360 ≤ 70773938829295 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2955 c22250R_102_19 (by norm_num)

theorem c22250R_102_17 : rowsJ2 102 103 50 360 ≤ 76904017164697 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2954 c22250R_102_18 (by norm_num)

theorem c22250R_102_16 : rowsJ2 102 103 49 360 ≤ 84156859768191 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2953 c22250R_102_17 (by norm_num)

theorem c22250R_102_15 : rowsJ2 102 103 48 360 ≤ 92671467648441 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2952 c22250R_102_16 (by norm_num)

theorem c22250R_102_14 : rowsJ2 102 103 47 360 ≤ 102540919570143 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2951 c22250R_102_15 (by norm_num)

theorem c22250R_102_13 : rowsJ2 102 103 46 360 ≤ 113911331515684 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2950 c22250R_102_14 (by norm_num)

theorem c22250R_102_12 : rowsJ2 102 103 45 360 ≤ 126799140791811 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2949 c22250R_102_13 (by norm_num)

theorem c22250R_102_11 : rowsJ2 102 103 44 360 ≤ 141270346163108 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2948 c22250R_102_12 (by norm_num)

theorem c22250R_102_10 : rowsJ2 102 103 43 360 ≤ 154583628222308 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2947 c22250R_102_11 (by norm_num)

theorem c22250R_102_9 : rowsJ2 102 103 42 360 ≤ 166550129239671 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2946 c22250R_102_10 (by norm_num)

theorem c22250R_102_8 : rowsJ2 102 103 41 360 ≤ 177123754194279 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2945 c22250R_102_9 (by norm_num)

theorem c22250R_102_7 : rowsJ2 102 103 40 360 ≤ 186396912367731 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2944 c22250R_102_8 (by norm_num)

theorem c22250R_102_6 : rowsJ2 102 103 39 360 ≤ 194466528084874 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2943 c22250R_102_7 (by norm_num)

theorem c22250R_102_5 : rowsJ2 102 103 37 360 ≤ 206368415468847 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2942 c22250R_102_6 (by norm_num)

theorem c22250R_102_4 : rowsJ2 102 103 35 360 ≤ 212987851838117 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2941 c22250R_102_5 (by norm_num)

theorem c22250R_102_3 : rowsJ2 102 103 31 360 ≤ 216708883732727 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2940 c22250R_102_4 (by norm_num)

theorem c22250R_102_2 : rowsJ2 102 103 22 360 ≤ 216708883732727 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2939 c22250R_102_3 (by norm_num)

theorem c22250R_102_1 : rowsJ2 102 103 16 360 ≤ 216708883732727 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2938 c22250R_102_2 (by norm_num)

theorem c22250R_102_0 : rowsJ2 102 103 0 360 ≤ 216708883732727 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22250R_2937 c22250R_102_1 (by norm_num)

theorem hr22250R_102 : rows2 102 103 ≤ 216708883732727 := rows2_le_of_rowsJ2 102 103 c22250R_102_0

theorem c22250R_103_48 : rowsJ2 103 104 102 360 ≤ 10269702550718 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3034 rows22250R_3035 (by norm_num)

theorem c22250R_103_47 : rowsJ2 103 104 101 360 ≤ 14559474193072 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3033 c22250R_103_48 (by norm_num)

theorem c22250R_103_46 : rowsJ2 103 104 100 360 ≤ 18386721614092 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3032 c22250R_103_47 (by norm_num)

theorem c22250R_103_45 : rowsJ2 103 104 99 360 ≤ 21787650230357 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3031 c22250R_103_46 (by norm_num)

theorem c22250R_103_44 : rowsJ2 103 104 98 360 ≤ 24846980784634 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3030 c22250R_103_45 (by norm_num)

theorem c22250R_103_43 : rowsJ2 103 104 97 360 ≤ 27598775253155 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3029 c22250R_103_44 (by norm_num)

theorem c22250R_103_42 : rowsJ2 103 104 96 360 ≤ 30123908091039 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3028 c22250R_103_43 (by norm_num)

theorem c22250R_103_41 : rowsJ2 103 104 95 360 ≤ 32453720135937 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3027 c22250R_103_42 (by norm_num)

theorem c22250R_103_40 : rowsJ2 103 104 94 360 ≤ 34666710702150 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3026 c22250R_103_41 (by norm_num)

theorem c22250R_103_39 : rowsJ2 103 104 93 360 ≤ 36827147853372 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3025 c22250R_103_40 (by norm_num)

theorem c22250R_103_38 : rowsJ2 103 104 92 360 ≤ 39010162337783 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3024 c22250R_103_39 (by norm_num)

theorem c22250R_103_37 : rowsJ2 103 104 91 360 ≤ 41275932125587 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3023 c22250R_103_38 (by norm_num)

theorem c22250R_103_36 : rowsJ2 103 104 90 360 ≤ 43696648534048 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3022 c22250R_103_37 (by norm_num)

theorem c22250R_103_35 : rowsJ2 103 104 89 360 ≤ 46270678137618 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3021 c22250R_103_36 (by norm_num)

theorem c22250R_103_34 : rowsJ2 103 104 88 360 ≤ 48666522455759 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3020 c22250R_103_35 (by norm_num)

theorem c22250R_103_33 : rowsJ2 103 104 87 360 ≤ 50653907114177 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3019 c22250R_103_34 (by norm_num)

theorem c22250R_103_32 : rowsJ2 103 104 86 360 ≤ 52141106312623 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3018 c22250R_103_33 (by norm_num)

theorem c22250R_103_31 : rowsJ2 103 104 85 360 ≤ 53252026474153 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3017 c22250R_103_32 (by norm_num)

theorem c22250R_103_30 : rowsJ2 103 104 84 360 ≤ 54046440222683 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3016 c22250R_103_31 (by norm_num)

theorem c22250R_103_29 : rowsJ2 103 104 83 360 ≤ 54569749764844 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3015 c22250R_103_30 (by norm_num)

theorem c22250R_103_28 : rowsJ2 103 104 81 360 ≤ 55032683082582 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3014 c22250R_103_29 (by norm_num)

theorem c22250R_103_27 : rowsJ2 103 104 78 360 ≤ 55083036388537 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3013 c22250R_103_28 (by norm_num)

theorem c22250R_103_26 : rowsJ2 103 104 73 360 ≤ 55083036388537 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3012 c22250R_103_27 (by norm_num)

theorem c22250R_103_25 : rowsJ2 103 104 67 360 ≤ 55083036388537 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3011 c22250R_103_26 (by norm_num)

theorem c22250R_103_24 : rowsJ2 103 104 62 360 ≤ 55083036388537 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3010 c22250R_103_25 (by norm_num)

theorem c22250R_103_23 : rowsJ2 103 104 59 360 ≤ 55083036388537 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3009 c22250R_103_24 (by norm_num)

theorem c22250R_103_22 : rowsJ2 103 104 57 360 ≤ 55558296042239 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3008 c22250R_103_23 (by norm_num)

theorem c22250R_103_21 : rowsJ2 103 104 55 360 ≤ 57866484770623 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3007 c22250R_103_22 (by norm_num)

theorem c22250R_103_20 : rowsJ2 103 104 53 360 ≤ 62830688030338 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3006 c22250R_103_21 (by norm_num)

theorem c22250R_103_19 : rowsJ2 103 104 52 360 ≤ 66494509954696 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3005 c22250R_103_20 (by norm_num)

theorem c22250R_103_18 : rowsJ2 103 104 51 360 ≤ 71029013628855 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3004 c22250R_103_19 (by norm_num)

theorem c22250R_103_17 : rowsJ2 103 104 50 360 ≤ 76495739605867 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3003 c22250R_103_18 (by norm_num)

theorem c22250R_103_16 : rowsJ2 103 104 49 360 ≤ 83032242819083 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3002 c22250R_103_17 (by norm_num)

theorem c22250R_103_15 : rowsJ2 103 104 48 360 ≤ 90778562546121 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3001 c22250R_103_16 (by norm_num)

theorem c22250R_103_14 : rowsJ2 103 104 47 360 ≤ 99877513854172 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_3000 c22250R_103_15 (by norm_num)

theorem c22250R_103_13 : rowsJ2 103 104 46 360 ≤ 110426028264847 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2999 c22250R_103_14 (by norm_num)

theorem c22250R_103_12 : rowsJ2 103 104 45 360 ≤ 122489253634581 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2998 c22250R_103_13 (by norm_num)

theorem c22250R_103_11 : rowsJ2 103 104 44 360 ≤ 136084196440297 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2997 c22250R_103_12 (by norm_num)

theorem c22250R_103_10 : rowsJ2 103 104 43 360 ≤ 149924003197005 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2996 c22250R_103_11 (by norm_num)

theorem c22250R_103_9 : rowsJ2 103 104 42 360 ≤ 162481437876953 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2995 c22250R_103_10 (by norm_num)

theorem c22250R_103_8 : rowsJ2 103 104 41 360 ≤ 173662482937015 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2994 c22250R_103_9 (by norm_num)

theorem c22250R_103_7 : rowsJ2 103 104 40 360 ≤ 183470716544926 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2993 c22250R_103_8 (by norm_num)

theorem c22250R_103_6 : rowsJ2 103 104 39 360 ≤ 192002147355413 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2992 c22250R_103_7 (by norm_num)

theorem c22250R_103_5 : rowsJ2 103 104 38 360 ≤ 198924459693356 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2991 c22250R_103_6 (by norm_num)

theorem c22250R_103_4 : rowsJ2 103 104 36 360 ≤ 208786140049166 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2990 c22250R_103_5 (by norm_num)

theorem c22250R_103_3 : rowsJ2 103 104 33 360 ≤ 215241533046678 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2989 c22250R_103_4 (by norm_num)

theorem c22250R_103_2 : rowsJ2 103 104 25 360 ≤ 216155632482987 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2988 c22250R_103_3 (by norm_num)

theorem c22250R_103_1 : rowsJ2 103 104 17 360 ≤ 216155632482987 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2987 c22250R_103_2 (by norm_num)

theorem c22250R_103_0 : rowsJ2 103 104 0 360 ≤ 216155632482987 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22250R_2986 c22250R_103_1 (by norm_num)

theorem hr22250R_103 : rows2 103 104 ≤ 216155632482987 := rows2_le_of_rowsJ2 103 104 c22250R_103_0

theorem c22250R_104_47 : rowsJ2 104 105 103 360 ≤ 11927362971745 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3083 rows22250R_3084 (by norm_num)

theorem c22250R_104_46 : rowsJ2 104 105 102 360 ≤ 16888598569942 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3082 c22250R_104_47 (by norm_num)

theorem c22250R_104_45 : rowsJ2 104 105 101 360 ≤ 21277420855719 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3081 c22250R_104_46 (by norm_num)

theorem c22250R_104_44 : rowsJ2 104 105 100 360 ≤ 25146564483114 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3080 c22250R_104_45 (by norm_num)

theorem c22250R_104_43 : rowsJ2 104 105 99 360 ≤ 28569909458372 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3079 c22250R_104_44 (by norm_num)

theorem c22250R_104_42 : rowsJ2 104 105 98 360 ≤ 31597580978027 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3078 c22250R_104_43 (by norm_num)

theorem c22250R_104_41 : rowsJ2 104 105 97 360 ≤ 34300426237189 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3077 c22250R_104_42 (by norm_num)

theorem c22250R_104_40 : rowsJ2 104 105 96 360 ≤ 36726308590043 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3076 c22250R_104_41 (by norm_num)

theorem c22250R_104_39 : rowsJ2 104 105 95 360 ≤ 38942432234927 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3075 c22250R_104_40 (by norm_num)

theorem c22250R_104_38 : rowsJ2 104 105 94 360 ≤ 40993827048538 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3074 c22250R_104_39 (by norm_num)

theorem c22250R_104_37 : rowsJ2 104 105 93 360 ≤ 42945517841457 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3073 c22250R_104_38 (by norm_num)

theorem c22250R_104_36 : rowsJ2 104 105 92 360 ≤ 44875373693157 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3072 c22250R_104_37 (by norm_num)

theorem c22250R_104_35 : rowsJ2 104 105 91 360 ≤ 46845242217308 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3071 c22250R_104_36 (by norm_num)

theorem c22250R_104_34 : rowsJ2 104 105 90 360 ≤ 48928809062943 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3070 c22250R_104_35 (by norm_num)

theorem c22250R_104_33 : rowsJ2 104 105 89 360 ≤ 51154384926493 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3069 c22250R_104_34 (by norm_num)

theorem c22250R_104_32 : rowsJ2 104 105 88 360 ≤ 53533589457668 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3068 c22250R_104_33 (by norm_num)

theorem c22250R_104_31 : rowsJ2 104 105 87 360 ≤ 55431443545814 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3067 c22250R_104_32 (by norm_num)

theorem c22250R_104_30 : rowsJ2 104 105 86 360 ≤ 56908322620160 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3066 c22250R_104_31 (by norm_num)

theorem c22250R_104_29 : rowsJ2 104 105 85 360 ≤ 58011131367159 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3065 c22250R_104_30 (by norm_num)

theorem c22250R_104_28 : rowsJ2 104 105 84 360 ≤ 58799339606715 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3064 c22250R_104_29 (by norm_num)

theorem c22250R_104_27 : rowsJ2 104 105 83 360 ≤ 59319246588287 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3063 c22250R_104_28 (by norm_num)

theorem c22250R_104_26 : rowsJ2 104 105 81 360 ≤ 59779169911876 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3062 c22250R_104_27 (by norm_num)

theorem c22250R_104_25 : rowsJ2 104 105 78 360 ≤ 59829195820449 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3061 c22250R_104_26 (by norm_num)

theorem c22250R_104_24 : rowsJ2 104 105 73 360 ≤ 59829195820449 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3060 c22250R_104_25 (by norm_num)

theorem c22250R_104_23 : rowsJ2 104 105 66 360 ≤ 59829195820449 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3059 c22250R_104_24 (by norm_num)

theorem c22250R_104_22 : rowsJ2 104 105 61 360 ≤ 59829195820449 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3058 c22250R_104_23 (by norm_num)

theorem c22250R_104_21 : rowsJ2 104 105 58 360 ≤ 59897916338968 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3057 c22250R_104_22 (by norm_num)

theorem c22250R_104_20 : rowsJ2 104 105 56 360 ≤ 60791942669911 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3056 c22250R_104_21 (by norm_num)

theorem c22250R_104_19 : rowsJ2 104 105 54 360 ≤ 63620377184916 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3055 c22250R_104_20 (by norm_num)

theorem c22250R_104_18 : rowsJ2 104 105 52 360 ≤ 69200004469254 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3054 c22250R_104_19 (by norm_num)

theorem c22250R_104_17 : rowsJ2 104 105 51 360 ≤ 73180295634747 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3053 c22250R_104_18 (by norm_num)

theorem c22250R_104_16 : rowsJ2 104 105 50 360 ≤ 78037684800689 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3052 c22250R_104_17 (by norm_num)

theorem c22250R_104_15 : rowsJ2 104 105 49 360 ≤ 83910930454380 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3051 c22250R_104_16 (by norm_num)

theorem c22250R_104_14 : rowsJ2 104 105 48 360 ≤ 90941191831477 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3050 c22250R_104_15 (by norm_num)

theorem c22250R_104_13 : rowsJ2 104 105 47 360 ≤ 99272324105741 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3049 c22250R_104_14 (by norm_num)

theorem c22250R_104_12 : rowsJ2 104 105 46 360 ≤ 109051183636271 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3048 c22250R_104_13 (by norm_num)

theorem c22250R_104_11 : rowsJ2 104 105 45 360 ≤ 120293168932229 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3047 c22250R_104_12 (by norm_num)

theorem c22250R_104_10 : rowsJ2 104 105 44 360 ≤ 133064184441833 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3046 c22250R_104_11 (by norm_num)

theorem c22250R_104_9 : rowsJ2 104 105 43 360 ≤ 147381829003417 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3045 c22250R_104_10 (by norm_num)

theorem c22250R_104_8 : rowsJ2 104 105 42 360 ≤ 160530414740160 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3044 c22250R_104_9 (by norm_num)

theorem c22250R_104_7 : rowsJ2 104 105 41 360 ≤ 172318969936602 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3043 c22250R_104_8 (by norm_num)

theorem c22250R_104_6 : rowsJ2 104 105 40 360 ≤ 182751214526228 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3042 c22250R_104_7 (by norm_num)

theorem c22250R_104_5 : rowsJ2 104 105 39 360 ≤ 191832909879813 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3041 c22250R_104_6 (by norm_num)

theorem c22250R_104_4 : rowsJ2 104 105 37 360 ≤ 205036245688101 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3040 c22250R_104_5 (by norm_num)

theorem c22250R_104_3 : rowsJ2 104 105 34 360 ≤ 215177162880836 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3039 c22250R_104_4 (by norm_num)

theorem c22250R_104_2 : rowsJ2 104 105 26 360 ≤ 217981670835399 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3038 c22250R_104_3 (by norm_num)

theorem c22250R_104_1 : rowsJ2 104 105 17 360 ≤ 217981670835399 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3037 c22250R_104_2 (by norm_num)

theorem c22250R_104_0 : rowsJ2 104 105 0 360 ≤ 217981670835399 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22250R_3036 c22250R_104_1 (by norm_num)

theorem hr22250R_104 : rows2 104 105 ≤ 217981670835399 := rows2_le_of_rowsJ2 104 105 c22250R_104_0

theorem c22250R_105_48 : rowsJ2 105 106 104 360 ≤ 13948545192580 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3133 rows22250R_3134 (by norm_num)

theorem c22250R_105_47 : rowsJ2 105 106 103 360 ≤ 19746560765338 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3132 c22250R_105_48 (by norm_num)

theorem c22250R_105_46 : rowsJ2 105 106 102 360 ≤ 24870541522192 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3131 c22250R_105_47 (by norm_num)

theorem c22250R_105_45 : rowsJ2 105 106 101 360 ≤ 29361984428343 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3130 c22250R_105_46 (by norm_num)

theorem c22250R_105_44 : rowsJ2 105 106 100 360 ≤ 33312141490230 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3129 c22250R_105_45 (by norm_num)

theorem c22250R_105_43 : rowsJ2 105 106 99 360 ≤ 36759734888006 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3128 c22250R_105_44 (by norm_num)

theorem c22250R_105_42 : rowsJ2 105 106 98 360 ≤ 39792469278029 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3127 c22250R_105_43 (by norm_num)

theorem c22250R_105_41 : rowsJ2 105 106 97 360 ≤ 42446666336406 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3126 c22250R_105_42 (by norm_num)

theorem c22250R_105_40 : rowsJ2 105 106 96 360 ≤ 44806884769001 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3125 c22250R_105_41 (by norm_num)

theorem c22250R_105_39 : rowsJ2 105 106 95 360 ≤ 46907385036124 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3124 c22250R_105_40 (by norm_num)

theorem c22250R_105_38 : rowsJ2 105 106 94 360 ≤ 48828975581219 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3123 c22250R_105_39 (by norm_num)

theorem c22250R_105_37 : rowsJ2 105 106 93 360 ≤ 50603275755103 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3122 c22250R_105_38 (by norm_num)

theorem c22250R_105_36 : rowsJ2 105 106 92 360 ≤ 52308814142152 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3121 c22250R_105_37 (by norm_num)

theorem c22250R_105_35 : rowsJ2 105 106 91 360 ≤ 54010255358958 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3120 c22250R_105_36 (by norm_num)

theorem c22250R_105_34 : rowsJ2 105 106 90 360 ≤ 55782859774115 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3119 c22250R_105_35 (by norm_num)

theorem c22250R_105_33 : rowsJ2 105 106 89 360 ≤ 57687292430617 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3118 c22250R_105_34 (by norm_num)

theorem c22250R_105_32 : rowsJ2 105 106 88 360 ≤ 59734028768789 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3117 c22250R_105_33 (by norm_num)

theorem c22250R_105_31 : rowsJ2 105 106 87 360 ≤ 61618254449641 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3116 c22250R_105_32 (by norm_num)

theorem c22250R_105_30 : rowsJ2 105 106 86 360 ≤ 63084980111576 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3115 c22250R_105_31 (by norm_num)

theorem c22250R_105_29 : rowsJ2 105 106 85 360 ≤ 64179823339665 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3114 c22250R_105_30 (by norm_num)

theorem c22250R_105_28 : rowsJ2 105 106 84 360 ≤ 64961936512474 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3113 c22250R_105_29 (by norm_num)

theorem c22250R_105_27 : rowsJ2 105 106 83 360 ≤ 65478484894556 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3112 c22250R_105_28 (by norm_num)

theorem c22250R_105_26 : rowsJ2 105 106 81 360 ≤ 65935437113121 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3111 c22250R_105_27 (by norm_num)

theorem c22250R_105_25 : rowsJ2 105 106 77 360 ≤ 65985139854287 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3110 c22250R_105_26 (by norm_num)

theorem c22250R_105_24 : rowsJ2 105 106 72 360 ≤ 65985139854287 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3109 c22250R_105_25 (by norm_num)

theorem c22250R_105_23 : rowsJ2 105 106 65 360 ≤ 65985139854287 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3108 c22250R_105_24 (by norm_num)

theorem c22250R_105_22 : rowsJ2 105 106 60 360 ≤ 65985139854287 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3107 c22250R_105_23 (by norm_num)

theorem c22250R_105_21 : rowsJ2 105 106 57 360 ≤ 66124778023287 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3106 c22250R_105_22 (by norm_num)

theorem c22250R_105_20 : rowsJ2 105 106 55 360 ≤ 67384420290566 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3105 c22250R_105_21 (by norm_num)

theorem c22250R_105_19 : rowsJ2 105 106 53 360 ≤ 70819070079276 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3104 c22250R_105_20 (by norm_num)

theorem c22250R_105_18 : rowsJ2 105 106 51 360 ≤ 77026461328589 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3103 c22250R_105_19 (by norm_num)

theorem c22250R_105_17 : rowsJ2 105 106 50 360 ≤ 81329757640755 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3102 c22250R_105_18 (by norm_num)

theorem c22250R_105_16 : rowsJ2 105 106 49 360 ≤ 86593983474343 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3101 c22250R_105_17 (by norm_num)

theorem c22250R_105_15 : rowsJ2 105 106 48 360 ≤ 92961503833563 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3100 c22250R_105_16 (by norm_num)

theorem c22250R_105_14 : rowsJ2 105 106 47 360 ≤ 100577296192191 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3099 c22250R_105_15 (by norm_num)

theorem c22250R_105_13 : rowsJ2 105 106 46 360 ≤ 109589259484597 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3098 c22250R_105_14 (by norm_num)

theorem c22250R_105_12 : rowsJ2 105 106 45 360 ≤ 120062520223412 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3097 c22250R_105_13 (by norm_num)

theorem c22250R_105_11 : rowsJ2 105 106 44 360 ≤ 132013029307713 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3096 c22250R_105_12 (by norm_num)

theorem c22250R_105_10 : rowsJ2 105 106 43 360 ≤ 145507479117282 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3095 c22250R_105_11 (by norm_num)

theorem c22250R_105_9 : rowsJ2 105 106 42 360 ≤ 159198814315076 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3094 c22250R_105_10 (by norm_num)

theorem c22250R_105_8 : rowsJ2 105 106 41 360 ≤ 171595159339455 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3093 c22250R_105_9 (by norm_num)

theorem c22250R_105_7 : rowsJ2 105 106 40 360 ≤ 182651571932984 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3092 c22250R_105_8 (by norm_num)

theorem c22250R_105_6 : rowsJ2 105 106 39 360 ≤ 192373947791139 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3091 c22250R_105_7 (by norm_num)

theorem c22250R_105_5 : rowsJ2 105 106 38 360 ≤ 200154345594868 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3090 c22250R_105_6 (by norm_num)

theorem c22250R_105_4 : rowsJ2 105 106 36 360 ≤ 211266373377971 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3089 c22250R_105_5 (by norm_num)

theorem c22250R_105_3 : rowsJ2 105 106 34 360 ≤ 217385176798070 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3088 c22250R_105_4 (by norm_num)

theorem c22250R_105_2 : rowsJ2 105 106 27 360 ≤ 220693401221902 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3087 c22250R_105_3 (by norm_num)

theorem c22250R_105_1 : rowsJ2 105 106 17 360 ≤ 220693401221902 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3086 c22250R_105_2 (by norm_num)

theorem c22250R_105_0 : rowsJ2 105 106 0 360 ≤ 220693401221902 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22250R_3085 c22250R_105_1 (by norm_num)

theorem hr22250R_105 : rows2 105 106 ≤ 220693401221902 := rows2_le_of_rowsJ2 105 106 c22250R_105_0

theorem c22250R_106_48 : rowsJ2 106 107 105 360 ≤ 16412619310693 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3183 rows22250R_3184 (by norm_num)

theorem c22250R_106_47 : rowsJ2 106 107 104 360 ≤ 23265750918793 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3182 c22250R_106_48 (by norm_num)

theorem c22250R_106_46 : rowsJ2 106 107 103 360 ≤ 29322914015893 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3181 c22250R_106_47 (by norm_num)

theorem c22250R_106_45 : rowsJ2 106 107 102 360 ≤ 34642757749334 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3180 c22250R_106_46 (by norm_num)

theorem c22250R_106_44 : rowsJ2 106 107 101 360 ≤ 39306375403654 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3179 c22250R_106_45 (by norm_num)

theorem c22250R_106_43 : rowsJ2 106 107 100 360 ≤ 43369100587310 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3178 c22250R_106_44 (by norm_num)

theorem c22250R_106_42 : rowsJ2 106 107 99 360 ≤ 46908259275881 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3177 c22250R_106_43 (by norm_num)

theorem c22250R_106_41 : rowsJ2 106 107 98 360 ≤ 49976290510858 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3176 c22250R_106_42 (by norm_num)

theorem c22250R_106_40 : rowsJ2 106 107 97 360 ≤ 52647185299639 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3175 c22250R_106_41 (by norm_num)

theorem c22250R_106_39 : rowsJ2 106 107 96 360 ≤ 54970868307097 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3174 c22250R_106_40 (by norm_num)

theorem c22250R_106_38 : rowsJ2 106 107 95 360 ≤ 57018388514701 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3173 c22250R_106_39 (by norm_num)

theorem c22250R_106_37 : rowsJ2 106 107 94 360 ≤ 58837501672800 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3172 c22250R_106_38 (by norm_num)

theorem c22250R_106_36 : rowsJ2 106 107 93 360 ≤ 60495702074349 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3171 c22250R_106_37 (by norm_num)

theorem c22250R_106_35 : rowsJ2 106 107 92 360 ≤ 62038002466213 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3170 c22250R_106_36 (by norm_num)

theorem c22250R_106_34 : rowsJ2 106 107 91 360 ≤ 63529805966988 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3169 c22250R_106_35 (by norm_num)

theorem c22250R_106_33 : rowsJ2 106 107 90 360 ≤ 65049099483205 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3168 c22250R_106_34 (by norm_num)

theorem c22250R_106_32 : rowsJ2 106 107 89 360 ≤ 66658202535840 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3167 c22250R_106_33 (by norm_num)

theorem c22250R_106_31 : rowsJ2 106 107 88 360 ≤ 68399408149736 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3166 c22250R_106_32 (by norm_num)

theorem c22250R_106_30 : rowsJ2 106 107 87 360 ≤ 70270246714848 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3165 c22250R_106_31 (by norm_num)

theorem c22250R_106_29 : rowsJ2 106 107 86 360 ≤ 71725921397433 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3164 c22250R_106_30 (by norm_num)

theorem c22250R_106_28 : rowsJ2 106 107 85 360 ≤ 72812933286303 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3163 c22250R_106_29 (by norm_num)

theorem c22250R_106_27 : rowsJ2 106 107 84 360 ≤ 73590140705820 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3162 c22250R_106_28 (by norm_num)

theorem c22250R_106_26 : rowsJ2 106 107 83 360 ≤ 74102293124193 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3161 c22250R_106_27 (by norm_num)

theorem c22250R_106_25 : rowsJ2 106 107 80 360 ≤ 74605696100314 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3160 c22250R_106_26 (by norm_num)

theorem c22250R_106_24 : rowsJ2 106 107 76 360 ≤ 74605696100314 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3159 c22250R_106_25 (by norm_num)

theorem c22250R_106_23 : rowsJ2 106 107 71 360 ≤ 74605696100314 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3158 c22250R_106_24 (by norm_num)

theorem c22250R_106_22 : rowsJ2 106 107 64 360 ≤ 74605696100314 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3157 c22250R_106_23 (by norm_num)

theorem c22250R_106_21 : rowsJ2 106 107 59 360 ≤ 74605696100314 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3156 c22250R_106_22 (by norm_num)

theorem c22250R_106_20 : rowsJ2 106 107 56 360 ≤ 74961605292939 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3155 c22250R_106_21 (by norm_num)

theorem c22250R_106_19 : rowsJ2 106 107 54 360 ≤ 76744811461589 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3154 c22250R_106_20 (by norm_num)

theorem c22250R_106_18 : rowsJ2 106 107 52 360 ≤ 80797679220415 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3153 c22250R_106_19 (by norm_num)

theorem c22250R_106_17 : rowsJ2 106 107 50 360 ≤ 87645734294846 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3152 c22250R_106_18 (by norm_num)

theorem c22250R_106_16 : rowsJ2 106 107 49 360 ≤ 92356421530794 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3151 c22250R_106_17 (by norm_num)

theorem c22250R_106_15 : rowsJ2 106 107 48 360 ≤ 98115689458934 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3150 c22250R_106_16 (by norm_num)

theorem c22250R_106_14 : rowsJ2 106 107 47 360 ≤ 105069724179252 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3149 c22250R_106_15 (by norm_num)

theorem c22250R_106_13 : rowsJ2 106 107 46 360 ≤ 113367549935679 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3148 c22250R_106_14 (by norm_num)

theorem c22250R_106_12 : rowsJ2 106 107 45 360 ≤ 123074928640118 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3147 c22250R_106_13 (by norm_num)

theorem c22250R_106_11 : rowsJ2 106 107 44 360 ≤ 134257735064796 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3146 c22250R_106_12 (by norm_num)

theorem c22250R_106_10 : rowsJ2 106 107 43 360 ≤ 146932495191820 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3145 c22250R_106_11 (by norm_num)

theorem c22250R_106_9 : rowsJ2 106 107 42 360 ≤ 161166722136729 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3144 c22250R_106_10 (by norm_num)

theorem c22250R_106_8 : rowsJ2 106 107 41 360 ≤ 174171328452617 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3143 c22250R_106_9 (by norm_num)

theorem c22250R_106_7 : rowsJ2 106 107 40 360 ≤ 185852262401876 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3142 c22250R_106_8 (by norm_num)

theorem c22250R_106_6 : rowsJ2 106 107 39 360 ≤ 196215554355500 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3141 c22250R_106_7 (by norm_num)

theorem c22250R_106_5 : rowsJ2 106 107 38 360 ≤ 204558126949807 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3140 c22250R_106_6 (by norm_num)

theorem c22250R_106_4 : rowsJ2 106 107 36 360 ≤ 216382216076633 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3139 c22250R_106_5 (by norm_num)

theorem c22250R_106_3 : rowsJ2 106 107 34 360 ≤ 223069208834472 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3138 c22250R_106_4 (by norm_num)

theorem c22250R_106_2 : rowsJ2 106 107 29 360 ≤ 226880385841180 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3137 c22250R_106_3 (by norm_num)

theorem c22250R_106_1 : rowsJ2 106 107 17 360 ≤ 226880385841180 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3136 c22250R_106_2 (by norm_num)

theorem c22250R_106_0 : rowsJ2 106 107 0 360 ≤ 226880385841180 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22250R_3135 c22250R_106_1 (by norm_num)

theorem hr22250R_106 : rows2 106 107 ≤ 226880385841180 := rows2_le_of_rowsJ2 106 107 c22250R_106_0

theorem c22250R_107_48 : rowsJ2 107 108 106 360 ≤ 19288435066874 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3233 rows22250R_3234 (by norm_num)

theorem c22250R_107_47 : rowsJ2 107 108 105 360 ≤ 27383963528330 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3232 c22250R_107_48 (by norm_num)

theorem c22250R_107_46 : rowsJ2 107 108 104 360 ≤ 34568532348370 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3231 c22250R_107_47 (by norm_num)

theorem c22250R_107_45 : rowsJ2 107 108 103 360 ≤ 40890267483243 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3230 c22250R_107_46 (by norm_num)

theorem c22250R_107_44 : rowsJ2 107 108 102 360 ≤ 46448367573416 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3229 c22250R_107_45 (by norm_num)

theorem c22250R_107_43 : rowsJ2 107 108 101 360 ≤ 51287402981619 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3228 c22250R_107_44 (by norm_num)

theorem c22250R_107_42 : rowsJ2 107 108 100 360 ≤ 55502207146390 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3227 c22250R_107_43 (by norm_num)

theorem c22250R_107_41 : rowsJ2 107 108 99 360 ≤ 59134253705913 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3226 c22250R_107_42 (by norm_num)

theorem c22250R_107_40 : rowsJ2 107 108 98 360 ≤ 62274494643037 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3225 c22250R_107_41 (by norm_num)

theorem c22250R_107_39 : rowsJ2 107 108 97 360 ≤ 64961718626224 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3224 c22250R_107_40 (by norm_num)

theorem c22250R_107_38 : rowsJ2 107 108 96 360 ≤ 67283434176589 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3223 c22250R_107_39 (by norm_num)

theorem c22250R_107_37 : rowsJ2 107 108 95 360 ≤ 69276116659742 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3222 c22250R_107_38 (by norm_num)

theorem c22250R_107_36 : rowsJ2 107 108 94 360 ≤ 71024230026619 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3221 c22250R_107_37 (by norm_num)

theorem c22250R_107_35 : rowsJ2 107 108 93 360 ≤ 72562273921300 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3220 c22250R_107_36 (by norm_num)

theorem c22250R_107_34 : rowsJ2 107 108 92 360 ≤ 73971060676738 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3219 c22250R_107_35 (by norm_num)

theorem c22250R_107_33 : rowsJ2 107 108 91 360 ≤ 75282532146025 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3218 c22250R_107_34 (by norm_num)

theorem c22250R_107_32 : rowsJ2 107 108 90 360 ≤ 76575319495887 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3217 c22250R_107_33 (by norm_num)

theorem c22250R_107_31 : rowsJ2 107 108 89 360 ≤ 77914544650990 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3216 c22250R_107_32 (by norm_num)

theorem c22250R_107_30 : rowsJ2 107 108 88 360 ≤ 79375674487820 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3215 c22250R_107_31 (by norm_num)

theorem c22250R_107_29 : rowsJ2 107 108 87 360 ≤ 80956298872102 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3214 c22250R_107_30 (by norm_num)

theorem c22250R_107_28 : rowsJ2 107 108 86 360 ≤ 82401127833566 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3213 c22250R_107_29 (by norm_num)

theorem c22250R_107_27 : rowsJ2 107 108 85 360 ≤ 83480440474502 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3212 c22250R_107_28 (by norm_num)

theorem c22250R_107_26 : rowsJ2 107 108 84 360 ≤ 84251733655942 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3211 c22250R_107_27 (by norm_num)

theorem c22250R_107_25 : rowsJ2 107 108 82 360 ≤ 85065178829844 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3210 c22250R_107_26 (by norm_num)

theorem c22250R_107_24 : rowsJ2 107 108 80 360 ≤ 85260850367470 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3209 c22250R_107_25 (by norm_num)

theorem c22250R_107_23 : rowsJ2 107 108 76 360 ≤ 85260850367470 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3208 c22250R_107_24 (by norm_num)

theorem c22250R_107_22 : rowsJ2 107 108 71 360 ≤ 85260850367470 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3207 c22250R_107_23 (by norm_num)

theorem c22250R_107_21 : rowsJ2 107 108 63 360 ≤ 85260850367470 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3206 c22250R_107_22 (by norm_num)

theorem c22250R_107_20 : rowsJ2 107 108 58 360 ≤ 85260850367470 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3205 c22250R_107_21 (by norm_num)

theorem c22250R_107_19 : rowsJ2 107 108 55 360 ≤ 85840154079835 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3204 c22250R_107_20 (by norm_num)

theorem c22250R_107_18 : rowsJ2 107 108 53 360 ≤ 88085870062038 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3203 c22250R_107_19 (by norm_num)

theorem c22250R_107_17 : rowsJ2 107 108 51 360 ≤ 92618399411618 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3202 c22250R_107_18 (by norm_num)

theorem c22250R_107_16 : rowsJ2 107 108 49 360 ≤ 100044430666168 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3201 c22250R_107_17 (by norm_num)

theorem c22250R_107_15 : rowsJ2 107 108 48 360 ≤ 105172936828512 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3200 c22250R_107_16 (by norm_num)

theorem c22250R_107_14 : rowsJ2 107 108 47 360 ≤ 111440917876366 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3199 c22250R_107_15 (by norm_num)

theorem c22250R_107_13 : rowsJ2 107 108 46 360 ≤ 118998593364287 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3198 c22250R_107_14 (by norm_num)

theorem c22250R_107_12 : rowsJ2 107 108 45 360 ≤ 127912409955778 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3197 c22250R_107_13 (by norm_num)

theorem c22250R_107_11 : rowsJ2 107 108 44 360 ≤ 138248852850337 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3196 c22250R_107_12 (by norm_num)

theorem c22250R_107_10 : rowsJ2 107 108 43 360 ≤ 150074557537411 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3195 c22250R_107_11 (by norm_num)

theorem c22250R_107_9 : rowsJ2 107 108 42 360 ≤ 163406629885896 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3194 c22250R_107_10 (by norm_num)

theorem c22250R_107_8 : rowsJ2 107 108 41 360 ≤ 176935872737729 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3193 c22250R_107_9 (by norm_num)

theorem c22250R_107_7 : rowsJ2 107 108 40 360 ≤ 189156651039048 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3192 c22250R_107_8 (by norm_num)

theorem c22250R_107_6 : rowsJ2 107 108 39 360 ≤ 200075109090189 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3191 c22250R_107_7 (by norm_num)

theorem c22250R_107_5 : rowsJ2 107 108 38 360 ≤ 209071269607616 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3190 c22250R_107_6 (by norm_num)

theorem c22250R_107_4 : rowsJ2 107 108 36 360 ≤ 221696115320089 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3189 c22250R_107_5 (by norm_num)

theorem c22250R_107_3 : rowsJ2 107 108 34 360 ≤ 229040920227387 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3188 c22250R_107_4 (by norm_num)

theorem c22250R_107_2 : rowsJ2 107 108 30 360 ≤ 233354341905509 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3187 c22250R_107_3 (by norm_num)

theorem c22250R_107_1 : rowsJ2 107 108 18 360 ≤ 233354341905509 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3186 c22250R_107_2 (by norm_num)

theorem c22250R_107_0 : rowsJ2 107 108 0 360 ≤ 233354341905509 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22250R_3185 c22250R_107_1 (by norm_num)

theorem hr22250R_107 : rows2 107 108 ≤ 233354341905509 := rows2_le_of_rowsJ2 107 108 c22250R_107_0

theorem c22250R_108_48 : rowsJ2 108 109 107 360 ≤ 22661490319244 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3283 rows22250R_3284 (by norm_num)

theorem c22250R_108_47 : rowsJ2 108 109 106 360 ≤ 32242508731520 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3282 c22250R_108_48 (by norm_num)

theorem c22250R_108_46 : rowsJ2 108 109 105 360 ≤ 40775789214566 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3281 c22250R_108_47 (by norm_num)

theorem c22250R_108_45 : rowsJ2 108 109 104 360 ≤ 48327402194932 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3280 c22250R_108_46 (by norm_num)

theorem c22250R_108_44 : rowsJ2 108 109 103 360 ≤ 54987219444108 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3279 c22250R_108_45 (by norm_num)

theorem c22250R_108_43 : rowsJ2 108 109 102 360 ≤ 60817117084707 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3278 c22250R_108_44 (by norm_num)

theorem c22250R_108_42 : rowsJ2 108 109 101 360 ≤ 65902297216422 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3277 c22250R_108_43 (by norm_num)

theorem c22250R_108_41 : rowsJ2 108 109 100 360 ≤ 70300960661380 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3276 c22250R_108_42 (by norm_num)

theorem c22250R_108_40 : rowsJ2 108 109 99 360 ≤ 74094166941155 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3275 c22250R_108_41 (by norm_num)

theorem c22250R_108_39 : rowsJ2 108 109 98 360 ≤ 77336905579099 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3274 c22250R_108_40 (by norm_num)

theorem c22250R_108_38 : rowsJ2 108 109 97 360 ≤ 80106567860585 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3273 c22250R_108_39 (by norm_num)

theorem c22250R_108_37 : rowsJ2 108 109 96 360 ≤ 82455349245090 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3272 c22250R_108_38 (by norm_num)

theorem c22250R_108_36 : rowsJ2 108 109 95 360 ≤ 84457402098966 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3271 c22250R_108_37 (by norm_num)

theorem c22250R_108_35 : rowsJ2 108 109 94 360 ≤ 86162505279364 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3270 c22250R_108_36 (by norm_num)

theorem c22250R_108_34 : rowsJ2 108 109 93 360 ≤ 87641963120641 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3269 c22250R_108_35 (by norm_num)

theorem c22250R_108_33 : rowsJ2 108 109 92 360 ≤ 88943481545871 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3268 c22250R_108_34 (by norm_num)

theorem c22250R_108_32 : rowsJ2 108 109 91 360 ≤ 90134901732523 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3267 c22250R_108_33 (by norm_num)

theorem c22250R_108_31 : rowsJ2 108 109 90 360 ≤ 91261280181569 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3266 c22250R_108_32 (by norm_num)

theorem c22250R_108_30 : rowsJ2 108 109 89 360 ≤ 92388459123544 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3265 c22250R_108_31 (by norm_num)

theorem c22250R_108_29 : rowsJ2 108 109 88 360 ≤ 93594620851609 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3264 c22250R_108_30 (by norm_num)

theorem c22250R_108_28 : rowsJ2 108 109 87 360 ≤ 94910140611665 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3263 c22250R_108_29 (by norm_num)

theorem c22250R_108_27 : rowsJ2 108 109 86 360 ≤ 96345399702823 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3262 c22250R_108_28 (by norm_num)

theorem c22250R_108_26 : rowsJ2 108 109 85 360 ≤ 97416079441166 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3261 c22250R_108_27 (by norm_num)

theorem c22250R_108_25 : rowsJ2 108 109 84 360 ≤ 98181564394493 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3260 c22250R_108_26 (by norm_num)

theorem c22250R_108_24 : rowsJ2 108 109 82 360 ≤ 98989892790716 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3259 c22250R_108_25 (by norm_num)

theorem c22250R_108_23 : rowsJ2 108 109 80 360 ≤ 99184324321399 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3258 c22250R_108_24 (by norm_num)

theorem c22250R_108_22 : rowsJ2 108 109 76 360 ≤ 99184324321399 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3257 c22250R_108_23 (by norm_num)

theorem c22250R_108_21 : rowsJ2 108 109 70 360 ≤ 99184324321399 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3256 c22250R_108_22 (by norm_num)

theorem c22250R_108_20 : rowsJ2 108 109 62 360 ≤ 99184324321399 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3255 c22250R_108_21 (by norm_num)

theorem c22250R_108_19 : rowsJ2 108 109 57 360 ≤ 99184324321399 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3254 c22250R_108_20 (by norm_num)

theorem c22250R_108_18 : rowsJ2 108 109 54 360 ≤ 100218026098330 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3253 c22250R_108_19 (by norm_num)

theorem c22250R_108_17 : rowsJ2 108 109 52 360 ≤ 102935563559740 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3252 c22250R_108_18 (by norm_num)

theorem c22250R_108_16 : rowsJ2 108 109 50 360 ≤ 107957778204968 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3251 c22250R_108_17 (by norm_num)

theorem c22250R_108_15 : rowsJ2 108 109 48 360 ≤ 116133091102852 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3250 c22250R_108_16 (by norm_num)

theorem c22250R_108_14 : rowsJ2 108 109 47 360 ≤ 121771015920785 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3249 c22250R_108_15 (by norm_num)

theorem c22250R_108_13 : rowsJ2 108 109 46 360 ≤ 128643575087156 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3248 c22250R_108_14 (by norm_num)

theorem c22250R_108_12 : rowsJ2 108 109 45 360 ≤ 136817970495559 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3247 c22250R_108_13 (by norm_num)

theorem c22250R_108_11 : rowsJ2 108 109 44 360 ≤ 146361364789421 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3246 c22250R_108_12 (by norm_num)

theorem c22250R_108_10 : rowsJ2 108 109 43 360 ≤ 157340996075682 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3245 c22250R_108_11 (by norm_num)

theorem c22250R_108_9 : rowsJ2 108 109 42 360 ≤ 169824291799833 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3244 c22250R_108_10 (by norm_num)

theorem c22250R_108_8 : rowsJ2 108 109 41 360 ≤ 183916087483040 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3243 c22250R_108_9 (by norm_num)

theorem c22250R_108_7 : rowsJ2 108 109 40 360 ≤ 196677411501770 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3242 c22250R_108_8 (by norm_num)

theorem c22250R_108_6 : rowsJ2 108 109 39 360 ≤ 208151627773413 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3241 c22250R_108_7 (by norm_num)

theorem c22250R_108_5 : rowsJ2 108 109 38 360 ≤ 217715131066904 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3240 c22250R_108_6 (by norm_num)

theorem c22250R_108_4 : rowsJ2 108 109 37 360 ≤ 225372041139217 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3239 c22250R_108_5 (by norm_num)

theorem c22250R_108_3 : rowsJ2 108 109 35 360 ≤ 235930011562184 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3238 c22250R_108_4 (by norm_num)

theorem c22250R_108_2 : rowsJ2 108 109 31 360 ≤ 243700188652800 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3237 c22250R_108_3 (by norm_num)

theorem c22250R_108_1 : rowsJ2 108 109 18 360 ≤ 244222829815600 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3236 c22250R_108_2 (by norm_num)

theorem c22250R_108_0 : rowsJ2 108 109 0 360 ≤ 244222829815600 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22250R_3235 c22250R_108_1 (by norm_num)

theorem hr22250R_108 : rows2 108 109 ≤ 244222829815600 := rows2_le_of_rowsJ2 108 109 c22250R_108_0

theorem c22250R_109_48 : rowsJ2 109 110 108 360 ≤ 26463561432224 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3333 rows22250R_3334 (by norm_num)

theorem c22250R_109_47 : rowsJ2 109 110 107 360 ≤ 37744842393950 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3332 c22250R_109_48 (by norm_num)

theorem c22250R_109_46 : rowsJ2 109 110 106 360 ≤ 47846889740384 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3331 c22250R_109_47 (by norm_num)

theorem c22250R_109_45 : rowsJ2 109 110 105 360 ≤ 56826144624771 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3330 c22250R_109_46 (by norm_num)

theorem c22250R_109_44 : rowsJ2 109 110 104 360 ≤ 64791506885587 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3329 c22250R_109_45 (by norm_num)

theorem c22250R_109_43 : rowsJ2 109 110 103 360 ≤ 71794881344179 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3328 c22250R_109_44 (by norm_num)

theorem c22250R_109_42 : rowsJ2 109 110 102 360 ≤ 77939791251399 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3327 c22250R_109_43 (by norm_num)

theorem c22250R_109_41 : rowsJ2 109 110 101 360 ≤ 83274177617539 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3326 c22250R_109_42 (by norm_num)

theorem c22250R_109_40 : rowsJ2 109 110 100 360 ≤ 87896780436159 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3325 c22250R_109_41 (by norm_num)

theorem c22250R_109_39 : rowsJ2 109 110 99 360 ≤ 91852085574347 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3324 c22250R_109_40 (by norm_num)

theorem c22250R_109_38 : rowsJ2 109 110 98 360 ≤ 95234581672499 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3323 c22250R_109_39 (by norm_num)

theorem c22250R_109_37 : rowsJ2 109 110 97 360 ≤ 98085753941101 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3322 c22250R_109_38 (by norm_num)

theorem c22250R_109_36 : rowsJ2 109 110 96 360 ≤ 100496319208433 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3321 c22250R_109_37 (by norm_num)

theorem c22250R_109_35 : rowsJ2 109 110 95 360 ≤ 102505170495681 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3320 c22250R_109_36 (by norm_num)

theorem c22250R_109_34 : rowsJ2 109 110 94 360 ≤ 104199687685700 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3319 c22250R_109_35 (by norm_num)

theorem c22250R_109_33 : rowsJ2 109 110 93 360 ≤ 105616540992248 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3318 c22250R_109_34 (by norm_num)

theorem c22250R_109_32 : rowsJ2 109 110 92 360 ≤ 106840170112933 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3317 c22250R_109_33 (by norm_num)

theorem c22250R_109_31 : rowsJ2 109 110 91 360 ≤ 107905358682628 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3316 c22250R_109_32 (by norm_num)

theorem c22250R_109_30 : rowsJ2 109 110 90 360 ≤ 108892996479693 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3315 c22250R_109_31 (by norm_num)

theorem c22250R_109_29 : rowsJ2 109 110 89 360 ≤ 109835396366176 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3314 c22250R_109_30 (by norm_num)

theorem c22250R_109_28 : rowsJ2 109 110 88 360 ≤ 110811369531182 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3313 c22250R_109_29 (by norm_num)

theorem c22250R_109_27 : rowsJ2 109 110 87 360 ≤ 111886561044457 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3312 c22250R_109_28 (by norm_num)

theorem c22250R_109_26 : rowsJ2 109 110 86 360 ≤ 113071335134992 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3311 c22250R_109_27 (by norm_num)

theorem c22250R_109_25 : rowsJ2 109 110 85 360 ≤ 114134628506234 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3310 c22250R_109_26 (by norm_num)

theorem c22250R_109_24 : rowsJ2 109 110 84 360 ≤ 114894409708597 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3309 c22250R_109_25 (by norm_num)

theorem c22250R_109_23 : rowsJ2 109 110 82 360 ≤ 115696611626951 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3308 c22250R_109_24 (by norm_num)

theorem c22250R_109_22 : rowsJ2 109 110 79 360 ≤ 115889818768028 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3307 c22250R_109_23 (by norm_num)

theorem c22250R_109_21 : rowsJ2 109 110 75 360 ≤ 115889818768028 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3306 c22250R_109_22 (by norm_num)

theorem c22250R_109_20 : rowsJ2 109 110 69 360 ≤ 115889818768028 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3305 c22250R_109_21 (by norm_num)

theorem c22250R_109_19 : rowsJ2 109 110 61 360 ≤ 115889818768028 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3304 c22250R_109_20 (by norm_num)

theorem c22250R_109_18 : rowsJ2 109 110 56 360 ≤ 115889818768028 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3303 c22250R_109_19 (by norm_num)

theorem c22250R_109_17 : rowsJ2 109 110 53 360 ≤ 117313620555279 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3302 c22250R_109_18 (by norm_num)

theorem c22250R_109_16 : rowsJ2 109 110 51 360 ≤ 120357501942136 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3301 c22250R_109_17 (by norm_num)

theorem c22250R_109_15 : rowsJ2 109 110 49 360 ≤ 125800418542644 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3300 c22250R_109_16 (by norm_num)

theorem c22250R_109_14 : rowsJ2 109 110 47 360 ≤ 134743589568633 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3299 c22250R_109_15 (by norm_num)

theorem c22250R_109_13 : rowsJ2 109 110 46 360 ≤ 140905269685381 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3298 c22250R_109_14 (by norm_num)

theorem c22250R_109_12 : rowsJ2 109 110 45 360 ≤ 148312650474654 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3297 c22250R_109_13 (by norm_num)

theorem c22250R_109_11 : rowsJ2 109 110 44 360 ≤ 157033624312907 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3296 c22250R_109_12 (by norm_num)

theorem c22250R_109_10 : rowsJ2 109 110 43 360 ≤ 167136080156092 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3295 c22250R_109_11 (by norm_num)

theorem c22250R_109_9 : rowsJ2 109 110 42 360 ≤ 178688020323189 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3294 c22250R_109_10 (by norm_num)

theorem c22250R_109_8 : rowsJ2 109 110 41 360 ≤ 191845217789697 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3293 c22250R_109_9 (by norm_num)

theorem c22250R_109_7 : rowsJ2 109 110 40 360 ≤ 205148933982255 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3292 c22250R_109_8 (by norm_num)

theorem c22250R_109_6 : rowsJ2 109 110 39 360 ≤ 217091147921506 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3291 c22250R_109_7 (by norm_num)

theorem c22250R_109_5 : rowsJ2 109 110 38 360 ≤ 227222515364497 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3290 c22250R_109_6 (by norm_num)

theorem c22250R_109_4 : rowsJ2 109 110 36 360 ≤ 241899528091812 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3289 c22250R_109_5 (by norm_num)

theorem c22250R_109_3 : rowsJ2 109 110 34 360 ≤ 250560997563381 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3288 c22250R_109_4 (by norm_num)

theorem c22250R_109_2 : rowsJ2 109 110 31 360 ≤ 255440863447913 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3287 c22250R_109_3 (by norm_num)

theorem c22250R_109_1 : rowsJ2 109 110 19 360 ≤ 256140019659377 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3286 c22250R_109_2 (by norm_num)

theorem c22250R_109_0 : rowsJ2 109 110 0 360 ≤ 256140019659377 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22250R_3285 c22250R_109_1 (by norm_num)

theorem hr22250R_109 : rows2 109 110 ≤ 256140019659377 := rows2_le_of_rowsJ2 109 110 c22250R_109_0

theorem c22250R_110_47 : rowsJ2 110 111 107 360 ≤ 260006140989762 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3382 rows22250R_3383 (by norm_num)

theorem c22250R_110_46 : rowsJ2 110 111 106 360 ≤ 270654402573010 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3381 c22250R_110_47 (by norm_num)

theorem c22250R_110_45 : rowsJ2 110 111 105 360 ≤ 280158276438201 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3380 c22250R_110_46 (by norm_num)

theorem c22250R_110_44 : rowsJ2 110 111 104 360 ≤ 288573861658385 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3379 c22250R_110_45 (by norm_num)

theorem c22250R_110_43 : rowsJ2 110 111 103 360 ≤ 295995969708637 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3378 c22250R_110_44 (by norm_num)

theorem c22250R_110_42 : rowsJ2 110 111 102 360 ≤ 302490044350237 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3377 c22250R_110_43 (by norm_num)

theorem c22250R_110_41 : rowsJ2 110 111 101 360 ≤ 308145755288691 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3376 c22250R_110_42 (by norm_num)

theorem c22250R_110_40 : rowsJ2 110 111 100 360 ≤ 313024468875115 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3375 c22250R_110_41 (by norm_num)

theorem c22250R_110_39 : rowsJ2 110 111 99 360 ≤ 317211295775390 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3374 c22250R_110_40 (by norm_num)

theorem c22250R_110_38 : rowsJ2 110 111 98 360 ≤ 320764038180736 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3373 c22250R_110_39 (by norm_num)

theorem c22250R_110_37 : rowsJ2 110 111 97 360 ≤ 323763769887113 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3372 c22250R_110_38 (by norm_num)

theorem c22250R_110_36 : rowsJ2 110 111 96 360 ≤ 326265188411755 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3371 c22250R_110_37 (by norm_num)

theorem c22250R_110_35 : rowsJ2 110 111 95 360 ≤ 328345801273846 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3370 c22250R_110_36 (by norm_num)

theorem c22250R_110_34 : rowsJ2 110 111 94 360 ≤ 330057615156449 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3369 c22250R_110_35 (by norm_num)

theorem c22250R_110_33 : rowsJ2 110 111 93 360 ≤ 331474997942636 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3368 c22250R_110_34 (by norm_num)

theorem c22250R_110_32 : rowsJ2 110 111 92 360 ≤ 332647640577642 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3367 c22250R_110_33 (by norm_num)

theorem c22250R_110_31 : rowsJ2 110 111 91 360 ≤ 333647160512185 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3366 c22250R_110_32 (by norm_num)

theorem c22250R_110_30 : rowsJ2 110 111 90 360 ≤ 334521275218247 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3365 c22250R_110_31 (by norm_num)

theorem c22250R_110_29 : rowsJ2 110 111 89 360 ≤ 335338234173683 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3364 c22250R_110_30 (by norm_num)

theorem c22250R_110_28 : rowsJ2 110 111 88 360 ≤ 336143202577631 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3363 c22250R_110_29 (by norm_num)

theorem c22250R_110_27 : rowsJ2 110 111 87 360 ≤ 337002527673734 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3362 c22250R_110_28 (by norm_num)

theorem c22250R_110_26 : rowsJ2 110 111 86 360 ≤ 337961275149065 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3361 c22250R_110_27 (by norm_num)

theorem c22250R_110_25 : rowsJ2 110 111 85 360 ≤ 339017308225827 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3360 c22250R_110_26 (by norm_num)

theorem c22250R_110_24 : rowsJ2 110 111 84 360 ≤ 339771498440390 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3359 c22250R_110_25 (by norm_num)

theorem c22250R_110_23 : rowsJ2 110 111 82 360 ≤ 340567681032537 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3358 c22250R_110_24 (by norm_num)

theorem c22250R_110_22 : rowsJ2 110 111 79 360 ≤ 340759679108151 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3357 c22250R_110_23 (by norm_num)

theorem c22250R_110_21 : rowsJ2 110 111 75 360 ≤ 340759679108151 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3356 c22250R_110_22 (by norm_num)

theorem c22250R_110_20 : rowsJ2 110 111 69 360 ≤ 340759679108151 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3355 c22250R_110_21 (by norm_num)

theorem c22250R_110_19 : rowsJ2 110 111 60 360 ≤ 340759679108151 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3354 c22250R_110_20 (by norm_num)

theorem c22250R_110_18 : rowsJ2 110 111 55 360 ≤ 340836231421557 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3353 c22250R_110_19 (by norm_num)

theorem c22250R_110_17 : rowsJ2 110 111 52 360 ≤ 342736445837861 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3352 c22250R_110_18 (by norm_num)

theorem c22250R_110_16 : rowsJ2 110 111 50 360 ≤ 346113615607178 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3351 c22250R_110_17 (by norm_num)

theorem c22250R_110_15 : rowsJ2 110 111 48 360 ≤ 352147181378810 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3350 c22250R_110_16 (by norm_num)

theorem c22250R_110_14 : rowsJ2 110 111 46 360 ≤ 362044327828657 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3349 c22250R_110_15 (by norm_num)

theorem c22250R_110_13 : rowsJ2 110 111 45 360 ≤ 368741233405259 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3348 c22250R_110_14 (by norm_num)

theorem c22250R_110_12 : rowsJ2 110 111 44 360 ≤ 376695358867560 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3347 c22250R_110_13 (by norm_num)

theorem c22250R_110_11 : rowsJ2 110 111 43 360 ≤ 385975315030326 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3346 c22250R_110_12 (by norm_num)

theorem c22250R_110_10 : rowsJ2 110 111 42 360 ≤ 396649746635464 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3345 c22250R_110_11 (by norm_num)

theorem c22250R_110_9 : rowsJ2 110 111 41 360 ≤ 408875424373399 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3344 c22250R_110_10 (by norm_num)

theorem c22250R_110_8 : rowsJ2 110 111 40 360 ≤ 422812962069953 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3343 c22250R_110_9 (by norm_num)

theorem c22250R_110_7 : rowsJ2 110 111 39 360 ≤ 435313996807029 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3342 c22250R_110_8 (by norm_num)

theorem c22250R_110_6 : rowsJ2 110 111 38 360 ≤ 445924951439885 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3341 c22250R_110_7 (by norm_num)

theorem c22250R_110_5 : rowsJ2 110 111 37 360 ≤ 454741020119419 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3340 c22250R_110_6 (by norm_num)

theorem c22250R_110_4 : rowsJ2 110 111 36 360 ≤ 461679841132375 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3339 c22250R_110_5 (by norm_num)

theorem c22250R_110_3 : rowsJ2 110 111 34 360 ≤ 471088683568233 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3338 c22250R_110_4 (by norm_num)

theorem c22250R_110_2 : rowsJ2 110 111 31 360 ≤ 476646911759847 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3337 c22250R_110_3 (by norm_num)

theorem c22250R_110_1 : rowsJ2 110 111 20 360 ≤ 477432174339493 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3336 c22250R_110_2 (by norm_num)

theorem c22250R_110_0 : rowsJ2 110 111 0 360 ≤ 477432174339493 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22250R_3335 c22250R_110_1 (by norm_num)

theorem hr22250R_110 : rows2 110 111 ≤ 477432174339493 := rows2_le_of_rowsJ2 110 111 c22250R_110_0

theorem c22250R_111_43 : rowsJ2 111 112 107 360 ≤ 358535098278255 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3427 rows22250R_3428 (by norm_num)

theorem c22250R_111_42 : rowsJ2 111 112 106 360 ≤ 369753867779684 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3426 c22250R_111_43 (by norm_num)

theorem c22250R_111_41 : rowsJ2 111 112 105 360 ≤ 379763348996792 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3425 c22250R_111_42 (by norm_num)

theorem c22250R_111_40 : rowsJ2 111 112 104 360 ≤ 388663480093520 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3424 c22250R_111_41 (by norm_num)

theorem c22250R_111_39 : rowsJ2 111 112 103 360 ≤ 396510027369186 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3423 c22250R_111_40 (by norm_num)

theorem c22250R_111_38 : rowsJ2 111 112 102 360 ≤ 403397513335682 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3422 c22250R_111_39 (by norm_num)

theorem c22250R_111_37 : rowsJ2 111 112 101 360 ≤ 409377582059076 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3421 c22250R_111_38 (by norm_num)

theorem c22250R_111_36 : rowsJ2 111 112 100 360 ≤ 414553239707659 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3420 c22250R_111_37 (by norm_num)

theorem c22250R_111_35 : rowsJ2 111 112 99 360 ≤ 418972274959667 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3419 c22250R_111_36 (by norm_num)

theorem c22250R_111_34 : rowsJ2 111 112 98 360 ≤ 422733031922192 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3418 c22250R_111_35 (by norm_num)

theorem c22250R_111_33 : rowsJ2 111 112 97 360 ≤ 425879947256029 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3417 c22250R_111_34 (by norm_num)

theorem c22250R_111_32 : rowsJ2 111 112 95 360 ≤ 430656414811112 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3416 c22250R_111_33 (by norm_num)

theorem c22250R_111_31 : rowsJ2 111 112 93 360 ≤ 433831178878994 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3415 c22250R_111_32 (by norm_num)

theorem c22250R_111_30 : rowsJ2 111 112 91 360 ≤ 435910782160452 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3414 c22250R_111_31 (by norm_num)

theorem c22250R_111_29 : rowsJ2 111 112 90 360 ≤ 436698658059969 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3413 c22250R_111_30 (by norm_num)

theorem c22250R_111_28 : rowsJ2 111 112 89 360 ≤ 437381863665775 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3412 c22250R_111_29 (by norm_num)

theorem c22250R_111_27 : rowsJ2 111 112 88 360 ≤ 438041443951891 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3411 c22250R_111_28 (by norm_num)

theorem c22250R_111_26 : rowsJ2 111 112 87 360 ≤ 438710136302076 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3410 c22250R_111_27 (by norm_num)

theorem c22250R_111_25 : rowsJ2 111 112 86 360 ≤ 439467014086134 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3409 c22250R_111_26 (by norm_num)

theorem c22250R_111_24 : rowsJ2 111 112 85 360 ≤ 440311074990376 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3408 c22250R_111_25 (by norm_num)

theorem c22250R_111_23 : rowsJ2 111 112 84 360 ≤ 441059775921662 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3407 c22250R_111_24 (by norm_num)

theorem c22250R_111_22 : rowsJ2 111 112 83 360 ≤ 441554176375068 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3406 c22250R_111_23 (by norm_num)

theorem c22250R_111_21 : rowsJ2 111 112 81 360 ≤ 441993000768345 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3405 c22250R_111_22 (by norm_num)

theorem c22250R_111_20 : rowsJ2 111 112 78 360 ≤ 442040848915122 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3404 c22250R_111_21 (by norm_num)

theorem c22250R_111_19 : rowsJ2 111 112 74 360 ≤ 442040848915122 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3403 c22250R_111_20 (by norm_num)

theorem c22250R_111_18 : rowsJ2 111 112 68 360 ≤ 442040848915122 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3402 c22250R_111_19 (by norm_num)

theorem c22250R_111_17 : rowsJ2 111 112 59 360 ≤ 442040848915122 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3401 c22250R_111_18 (by norm_num)

theorem c22250R_111_16 : rowsJ2 111 112 54 360 ≤ 442196562920088 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3400 c22250R_111_17 (by norm_num)

theorem c22250R_111_15 : rowsJ2 111 112 51 360 ≤ 444344957280665 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3399 c22250R_111_16 (by norm_num)

theorem c22250R_111_14 : rowsJ2 111 112 49 360 ≤ 447979768864539 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3398 c22250R_111_15 (by norm_num)

theorem c22250R_111_13 : rowsJ2 111 112 47 360 ≤ 454616735528412 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3397 c22250R_111_14 (by norm_num)

theorem c22250R_111_12 : rowsJ2 111 112 45 360 ≤ 465405557851275 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3396 c22250R_111_13 (by norm_num)

theorem c22250R_111_11 : rowsJ2 111 112 44 360 ≤ 472563529232180 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3395 c22250R_111_12 (by norm_num)

theorem c22250R_111_10 : rowsJ2 111 112 43 360 ≤ 480989782709646 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3394 c22250R_111_11 (by norm_num)

theorem c22250R_111_9 : rowsJ2 111 112 42 360 ≤ 490753656519690 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3393 c22250R_111_10 (by norm_num)

theorem c22250R_111_8 : rowsJ2 111 112 41 360 ≤ 502012982817528 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3392 c22250R_111_9 (by norm_num)

theorem c22250R_111_7 : rowsJ2 111 112 40 360 ≤ 514929354490127 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3391 c22250R_111_8 (by norm_num)

theorem c22250R_111_6 : rowsJ2 111 112 39 360 ≤ 527991182857228 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3390 c22250R_111_7 (by norm_num)

theorem c22250R_111_5 : rowsJ2 111 112 38 360 ≤ 539082519940114 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3389 c22250R_111_6 (by norm_num)

theorem c22250R_111_4 : rowsJ2 111 112 37 360 ≤ 548389589869939 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3388 c22250R_111_5 (by norm_num)

theorem c22250R_111_3 : rowsJ2 111 112 35 360 ≤ 561687587441580 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3387 c22250R_111_4 (by norm_num)

theorem c22250R_111_2 : rowsJ2 111 112 32 360 ≤ 571399196517978 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3386 c22250R_111_3 (by norm_num)

theorem c22250R_111_1 : rowsJ2 111 112 21 360 ≤ 573368042595996 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3385 c22250R_111_2 (by norm_num)

theorem c22250R_111_0 : rowsJ2 111 112 0 360 ≤ 573368042595996 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22250R_3384 c22250R_111_1 (by norm_num)

theorem hr22250R_111 : rows2 111 112 ≤ 573368042595996 := rows2_le_of_rowsJ2 111 112 c22250R_111_0

theorem c22250R_112_39 : rowsJ2 112 113 106 360 ≤ 552500825842060 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3468 rows22250R_3469 (by norm_num)

theorem c22250R_112_38 : rowsJ2 112 113 105 360 ≤ 563069092466902 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3467 c22250R_112_39 (by norm_num)

theorem c22250R_112_37 : rowsJ2 112 113 104 360 ≤ 572463852359514 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3466 c22250R_112_38 (by norm_num)

theorem c22250R_112_36 : rowsJ2 112 113 103 360 ≤ 580784701254148 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3465 c22250R_112_37 (by norm_num)

theorem c22250R_112_35 : rowsJ2 112 113 102 360 ≤ 588087084722809 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3464 c22250R_112_36 (by norm_num)

theorem c22250R_112_34 : rowsJ2 112 113 101 360 ≤ 594465251958824 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3463 c22250R_112_35 (by norm_num)

theorem c22250R_112_33 : rowsJ2 112 113 100 360 ≤ 599970590213619 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3462 c22250R_112_34 (by norm_num)

theorem c22250R_112_32 : rowsJ2 112 113 99 360 ≤ 604692613117902 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3461 c22250R_112_33 (by norm_num)

theorem c22250R_112_31 : rowsJ2 112 113 98 360 ≤ 608692226948753 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3460 c22250R_112_32 (by norm_num)

theorem c22250R_112_30 : rowsJ2 112 113 96 360 ≤ 614836886471400 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3459 c22250R_112_31 (by norm_num)

theorem c22250R_112_29 : rowsJ2 112 113 94 360 ≤ 618959882654249 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3458 c22250R_112_30 (by norm_num)

theorem c22250R_112_28 : rowsJ2 112 113 92 360 ≤ 621590647630239 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3457 c22250R_112_29 (by norm_num)

theorem c22250R_112_27 : rowsJ2 112 113 90 360 ≤ 623236077576679 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3456 c22250R_112_28 (by norm_num)

theorem c22250R_112_26 : rowsJ2 112 113 88 360 ≤ 624383581502722 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3455 c22250R_112_27 (by norm_num)

theorem c22250R_112_25 : rowsJ2 112 113 87 360 ≤ 624920101749936 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3454 c22250R_112_26 (by norm_num)

theorem c22250R_112_24 : rowsJ2 112 113 86 360 ≤ 625500052434381 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3453 c22250R_112_25 (by norm_num)

theorem c22250R_112_23 : rowsJ2 112 113 85 360 ≤ 626156004572798 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3452 c22250R_112_24 (by norm_num)

theorem c22250R_112_22 : rowsJ2 112 113 84 360 ≤ 626899316525740 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3451 c22250R_112_23 (by norm_num)

theorem c22250R_112_21 : rowsJ2 112 113 83 360 ≤ 627389707617325 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3450 c22250R_112_22 (by norm_num)

theorem c22250R_112_20 : rowsJ2 112 113 81 360 ≤ 627825858231518 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3449 c22250R_112_21 (by norm_num)

theorem c22250R_112_19 : rowsJ2 112 113 78 360 ≤ 627873410651977 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3448 c22250R_112_20 (by norm_num)

theorem c22250R_112_18 : rowsJ2 112 113 74 360 ≤ 627873410651977 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3447 c22250R_112_19 (by norm_num)

theorem c22250R_112_17 : rowsJ2 112 113 67 360 ≤ 627873410651977 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3446 c22250R_112_18 (by norm_num)

theorem c22250R_112_16 : rowsJ2 112 113 58 360 ≤ 627934680749080 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3445 c22250R_112_17 (by norm_num)

theorem c22250R_112_15 : rowsJ2 112 113 53 360 ≤ 628250670413756 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3444 c22250R_112_16 (by norm_num)

theorem c22250R_112_14 : rowsJ2 112 113 50 360 ≤ 630652588615160 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3443 c22250R_112_15 (by norm_num)

theorem c22250R_112_13 : rowsJ2 112 113 48 360 ≤ 634713548974329 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3442 c22250R_112_14 (by norm_num)

theorem c22250R_112_12 : rowsJ2 112 113 46 360 ≤ 642138606676733 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3441 c22250R_112_13 (by norm_num)

theorem c22250R_112_11 : rowsJ2 112 113 44 360 ≤ 653838997420459 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3440 c22250R_112_12 (by norm_num)

theorem c22250R_112_10 : rowsJ2 112 113 43 360 ≤ 661468600155956 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3439 c22250R_112_11 (by norm_num)

theorem c22250R_112_9 : rowsJ2 112 113 42 360 ≤ 670377996447152 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3438 c22250R_112_10 (by norm_num)

theorem c22250R_112_8 : rowsJ2 112 113 41 360 ≤ 680726168740984 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3437 c22250R_112_9 (by norm_num)

theorem c22250R_112_7 : rowsJ2 112 113 40 360 ≤ 692675774293293 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3436 c22250R_112_8 (by norm_num)

theorem c22250R_112_6 : rowsJ2 112 113 39 360 ≤ 706393528537191 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3435 c22250R_112_7 (by norm_num)

theorem c22250R_112_5 : rowsJ2 112 113 38 360 ≤ 717965609125534 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3434 c22250R_112_6 (by norm_num)

theorem c22250R_112_4 : rowsJ2 112 113 37 360 ≤ 727764406964743 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3433 c22250R_112_5 (by norm_num)

theorem c22250R_112_3 : rowsJ2 112 113 35 360 ≤ 742073696785332 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3432 c22250R_112_4 (by norm_num)

theorem c22250R_112_2 : rowsJ2 112 113 32 360 ≤ 752808949850373 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3431 c22250R_112_3 (by norm_num)

theorem c22250R_112_1 : rowsJ2 112 113 23 360 ≤ 755122506091175 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3430 c22250R_112_2 (by norm_num)

theorem c22250R_112_0 : rowsJ2 112 113 0 360 ≤ 755122506091175 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22250R_3429 c22250R_112_1 (by norm_num)

theorem hr22250R_112 : rows2 112 113 ≤ 755122506091175 := rows2_le_of_rowsJ2 112 113 c22250R_112_0

theorem c22250R_113_38 : rowsJ2 113 114 106 360 ≤ 642567835904494 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3508 rows22250R_3509 (by norm_num)

theorem c22250R_113_37 : rowsJ2 113 114 105 360 ≤ 653676647198698 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3507 c22250R_113_38 (by norm_num)

theorem c22250R_113_36 : rowsJ2 113 114 104 360 ≤ 663588220112433 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3506 c22250R_113_37 (by norm_num)

theorem c22250R_113_35 : rowsJ2 113 114 103 360 ≤ 672362277432571 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3505 c22250R_113_36 (by norm_num)

theorem c22250R_113_34 : rowsJ2 113 114 102 360 ≤ 680098085336156 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3504 c22250R_113_35 (by norm_num)

theorem c22250R_113_33 : rowsJ2 113 114 101 360 ≤ 686850778376326 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3503 c22250R_113_34 (by norm_num)

theorem c22250R_113_32 : rowsJ2 113 114 100 360 ≤ 692714345712703 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3502 c22250R_113_33 (by norm_num)

theorem c22250R_113_31 : rowsJ2 113 114 99 360 ≤ 697739927974198 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3501 c22250R_113_32 (by norm_num)

theorem c22250R_113_30 : rowsJ2 113 114 98 360 ≤ 702016844506573 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3500 c22250R_113_31 (by norm_num)

theorem c22250R_113_29 : rowsJ2 113 114 96 360 ≤ 708565709831592 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3499 c22250R_113_30 (by norm_num)

theorem c22250R_113_28 : rowsJ2 113 114 94 360 ≤ 712929929573497 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3498 c22250R_113_29 (by norm_num)

theorem c22250R_113_27 : rowsJ2 113 114 92 360 ≤ 715651255012507 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3497 c22250R_113_28 (by norm_num)

theorem c22250R_113_26 : rowsJ2 113 114 90 360 ≤ 717247702781068 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3496 c22250R_113_27 (by norm_num)

theorem c22250R_113_25 : rowsJ2 113 114 88 360 ≤ 718216738677681 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3495 c22250R_113_26 (by norm_num)

theorem c22250R_113_24 : rowsJ2 113 114 86 360 ≤ 719037214230926 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3494 c22250R_113_25 (by norm_num)

theorem c22250R_113_23 : rowsJ2 113 114 85 360 ≤ 719529720178937 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3493 c22250R_113_24 (by norm_num)

theorem c22250R_113_22 : rowsJ2 113 114 84 360 ≤ 720098382598594 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3492 c22250R_113_23 (by norm_num)

theorem c22250R_113_21 : rowsJ2 113 114 83 360 ≤ 720584844876050 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3491 c22250R_113_22 (by norm_num)

theorem c22250R_113_20 : rowsJ2 113 114 81 360 ≤ 721018354855217 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3490 c22250R_113_21 (by norm_num)

theorem c22250R_113_19 : rowsJ2 113 114 78 360 ≤ 721065615182386 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3489 c22250R_113_20 (by norm_num)

theorem c22250R_113_18 : rowsJ2 113 114 74 360 ≤ 721065615182386 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3488 c22250R_113_19 (by norm_num)

theorem c22250R_113_17 : rowsJ2 113 114 67 360 ≤ 721065615182386 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3487 c22250R_113_18 (by norm_num)

theorem c22250R_113_16 : rowsJ2 113 114 57 360 ≤ 721250151720586 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3486 c22250R_113_17 (by norm_num)

theorem c22250R_113_15 : rowsJ2 113 114 52 360 ≤ 721567277849162 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3485 c22250R_113_16 (by norm_num)

theorem c22250R_113_14 : rowsJ2 113 114 49 360 ≤ 724059331968702 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3484 c22250R_113_15 (by norm_num)

theorem c22250R_113_13 : rowsJ2 113 114 47 360 ≤ 728553041627567 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3483 c22250R_113_14 (by norm_num)

theorem c22250R_113_12 : rowsJ2 113 114 45 360 ≤ 736696606298857 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3482 c22250R_113_13 (by norm_num)

theorem c22250R_113_11 : rowsJ2 113 114 43 360 ≤ 749151176682898 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3481 c22250R_113_12 (by norm_num)

theorem c22250R_113_10 : rowsJ2 113 114 42 360 ≤ 757172907610125 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3480 c22250R_113_11 (by norm_num)

theorem c22250R_113_9 : rowsJ2 113 114 41 360 ≤ 766574785198921 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3479 c22250R_113_10 (by norm_num)

theorem c22250R_113_8 : rowsJ2 113 114 40 360 ≤ 777520598390574 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3478 c22250R_113_9 (by norm_num)

theorem c22250R_113_7 : rowsJ2 113 114 39 360 ≤ 790178107776610 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3477 c22250R_113_8 (by norm_num)

theorem c22250R_113_6 : rowsJ2 113 114 38 360 ≤ 802324844684459 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3476 c22250R_113_7 (by norm_num)

theorem c22250R_113_5 : rowsJ2 113 114 37 360 ≤ 812524301853590 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3475 c22250R_113_6 (by norm_num)

theorem c22250R_113_4 : rowsJ2 113 114 36 360 ≤ 821059838700632 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3474 c22250R_113_5 (by norm_num)

theorem c22250R_113_3 : rowsJ2 113 114 34 360 ≤ 833002263918099 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3473 c22250R_113_4 (by norm_num)

theorem c22250R_113_2 : rowsJ2 113 114 32 360 ≤ 839611922379704 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3472 c22250R_113_3 (by norm_num)

theorem c22250R_113_1 : rowsJ2 113 114 24 360 ≤ 842453215599874 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3471 c22250R_113_2 (by norm_num)

theorem c22250R_113_0 : rowsJ2 113 114 0 360 ≤ 842453215599874 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22250R_3470 c22250R_113_1 (by norm_num)

theorem hr22250R_113 : rows2 113 114 ≤ 842453215599874 := rows2_le_of_rowsJ2 113 114 c22250R_113_0

theorem c22250R_114_35 : rowsJ2 114 115 105 360 ≤ 826504299578808 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3545 rows22250R_3546 (by norm_num)

theorem c22250R_114_34 : rowsJ2 114 115 104 360 ≤ 836944102096490 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3544 c22250R_114_35 (by norm_num)

theorem c22250R_114_33 : rowsJ2 114 115 103 360 ≤ 846223451632312 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3543 c22250R_114_34 (by norm_num)

theorem c22250R_114_32 : rowsJ2 114 115 102 360 ≤ 854401703519243 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3542 c22250R_114_33 (by norm_num)

theorem c22250R_114_31 : rowsJ2 114 115 101 360 ≤ 861577810118191 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3541 c22250R_114_32 (by norm_num)

theorem c22250R_114_30 : rowsJ2 114 115 100 360 ≤ 867806607607662 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3540 c22250R_114_31 (by norm_num)

theorem c22250R_114_29 : rowsJ2 114 115 99 360 ≤ 873181841419531 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3539 c22250R_114_30 (by norm_num)

theorem c22250R_114_28 : rowsJ2 114 115 98 360 ≤ 877754418842759 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3538 c22250R_114_29 (by norm_num)

theorem c22250R_114_27 : rowsJ2 114 115 96 360 ≤ 884806531030170 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3537 c22250R_114_28 (by norm_num)

theorem c22250R_114_26 : rowsJ2 114 115 94 360 ≤ 889506982474794 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3536 c22250R_114_27 (by norm_num)

theorem c22250R_114_25 : rowsJ2 114 115 92 360 ≤ 892410405674046 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3535 c22250R_114_26 (by norm_num)

theorem c22250R_114_24 : rowsJ2 114 115 90 360 ≤ 894046437659669 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3534 c22250R_114_25 (by norm_num)

theorem c22250R_114_23 : rowsJ2 114 115 88 360 ≤ 894923047679951 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3533 c22250R_114_24 (by norm_num)

theorem c22250R_114_22 : rowsJ2 114 115 86 360 ≤ 895529576483189 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3532 c22250R_114_23 (by norm_num)

theorem c22250R_114_21 : rowsJ2 114 115 84 360 ≤ 896300337009724 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3531 c22250R_114_22 (by norm_num)

theorem c22250R_114_20 : rowsJ2 114 115 82 360 ≤ 897072442330480 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3530 c22250R_114_21 (by norm_num)

theorem c22250R_114_19 : rowsJ2 114 115 80 360 ≤ 897259751772429 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3529 c22250R_114_20 (by norm_num)

theorem c22250R_114_18 : rowsJ2 114 115 77 360 ≤ 897259751772429 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3528 c22250R_114_19 (by norm_num)

theorem c22250R_114_17 : rowsJ2 114 115 73 360 ≤ 897259751772429 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3527 c22250R_114_18 (by norm_num)

theorem c22250R_114_16 : rowsJ2 114 115 66 360 ≤ 897362870671283 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3526 c22250R_114_17 (by norm_num)

theorem c22250R_114_15 : rowsJ2 114 115 56 360 ≤ 897754171642896 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3525 c22250R_114_16 (by norm_num)

theorem c22250R_114_14 : rowsJ2 114 115 51 360 ≤ 898072480898613 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3524 c22250R_114_15 (by norm_num)

theorem c22250R_114_13 : rowsJ2 114 115 48 360 ≤ 900821715982675 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3523 c22250R_114_14 (by norm_num)

theorem c22250R_114_12 : rowsJ2 114 115 46 360 ≤ 905931347552562 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3522 c22250R_114_13 (by norm_num)

theorem c22250R_114_11 : rowsJ2 114 115 44 360 ≤ 914809563354398 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3521 c22250R_114_12 (by norm_num)

theorem c22250R_114_10 : rowsJ2 114 115 42 360 ≤ 928035896098349 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3520 c22250R_114_11 (by norm_num)

theorem c22250R_114_9 : rowsJ2 114 115 41 360 ≤ 936549024502837 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3519 c22250R_114_10 (by norm_num)

theorem c22250R_114_8 : rowsJ2 114 115 40 360 ≤ 946547650565311 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3518 c22250R_114_9 (by norm_num)

theorem c22250R_114_7 : rowsJ2 114 115 39 360 ≤ 958200670273342 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3517 c22250R_114_8 (by norm_num)

theorem c22250R_114_6 : rowsJ2 114 115 38 360 ≤ 970924189799784 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3516 c22250R_114_7 (by norm_num)

theorem c22250R_114_5 : rowsJ2 114 115 37 360 ≤ 981617068247865 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3515 c22250R_114_6 (by norm_num)

theorem c22250R_114_4 : rowsJ2 114 115 36 360 ≤ 990563869140502 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3514 c22250R_114_5 (by norm_num)

theorem c22250R_114_3 : rowsJ2 114 115 34 360 ≤ 1003449128906233 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3513 c22250R_114_4 (by norm_num)

theorem c22250R_114_2 : rowsJ2 114 115 32 360 ≤ 1010660888383304 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3512 c22250R_114_3 (by norm_num)

theorem c22250R_114_1 : rowsJ2 114 115 26 360 ≤ 1014211724924509 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3511 c22250R_114_2 (by norm_num)

theorem c22250R_114_0 : rowsJ2 114 115 0 360 ≤ 1014211724924509 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22250R_3510 c22250R_114_1 (by norm_num)

theorem hr22250R_114 : rows2 114 115 ≤ 1014211724924509 := rows2_le_of_rowsJ2 114 115 c22250R_114_0

theorem c22250R_115_34 : rowsJ2 115 116 105 360 ≤ 908463797449694 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3581 rows22250R_3582 (by norm_num)

theorem c22250R_115_33 : rowsJ2 115 116 104 360 ≤ 919455844234452 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3580 c22250R_115_34 (by norm_num)

theorem c22250R_115_32 : rowsJ2 115 116 103 360 ≤ 929219990948282 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3579 c22250R_115_33 (by norm_num)

theorem c22250R_115_31 : rowsJ2 115 116 102 360 ≤ 937860701967699 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3578 c22250R_115_32 (by norm_num)

theorem c22250R_115_30 : rowsJ2 115 116 101 360 ≤ 945436974864112 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3577 c22250R_115_31 (by norm_num)

theorem c22250R_115_29 : rowsJ2 115 116 100 360 ≤ 952047461504055 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3576 c22250R_115_30 (by norm_num)

theorem c22250R_115_28 : rowsJ2 115 116 99 360 ≤ 957746709877048 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3575 c22250R_115_29 (by norm_num)

theorem c22250R_115_27 : rowsJ2 115 116 98 360 ≤ 962628235513997 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3574 c22250R_115_28 (by norm_num)

theorem c22250R_115_26 : rowsJ2 115 116 96 360 ≤ 970179151828504 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3573 c22250R_115_27 (by norm_num)

theorem c22250R_115_25 : rowsJ2 115 116 94 360 ≤ 975244831653632 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3572 c22250R_115_26 (by norm_num)

theorem c22250R_115_24 : rowsJ2 115 116 92 360 ≤ 978354780547852 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3571 c22250R_115_25 (by norm_num)

theorem c22250R_115_23 : rowsJ2 115 116 90 360 ≤ 980050752829105 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3570 c22250R_115_24 (by norm_num)

theorem c22250R_115_22 : rowsJ2 115 116 88 360 ≤ 980851660196503 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3569 c22250R_115_23 (by norm_num)

theorem c22250R_115_21 : rowsJ2 115 116 86 360 ≤ 981256743610229 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3568 c22250R_115_22 (by norm_num)

theorem c22250R_115_20 : rowsJ2 115 116 84 360 ≤ 981783187265811 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3567 c22250R_115_21 (by norm_num)

theorem c22250R_115_19 : rowsJ2 115 116 82 360 ≤ 982415269844520 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3566 c22250R_115_20 (by norm_num)

theorem c22250R_115_18 : rowsJ2 115 116 79 360 ≤ 982601442691384 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3565 c22250R_115_19 (by norm_num)

theorem c22250R_115_17 : rowsJ2 115 116 76 360 ≤ 982601442691384 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3564 c22250R_115_18 (by norm_num)

theorem c22250R_115_16 : rowsJ2 115 116 72 360 ≤ 982601442691384 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3563 c22250R_115_17 (by norm_num)

theorem c22250R_115_15 : rowsJ2 115 116 65 360 ≤ 983160175426273 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3562 c22250R_115_16 (by norm_num)

theorem c22250R_115_14 : rowsJ2 115 116 55 360 ≤ 983532472415730 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3561 c22250R_115_15 (by norm_num)

theorem c22250R_115_13 : rowsJ2 115 116 50 360 ≤ 983852012416732 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3560 c22250R_115_14 (by norm_num)

theorem c22250R_115_12 : rowsJ2 115 116 47 360 ≤ 987116491822933 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3559 c22250R_115_13 (by norm_num)

theorem c22250R_115_11 : rowsJ2 115 116 45 360 ≤ 992944299186310 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3558 c22250R_115_12 (by norm_num)

theorem c22250R_115_10 : rowsJ2 115 116 43 360 ≤ 1002574041807812 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3557 c22250R_115_11 (by norm_num)

theorem c22250R_115_9 : rowsJ2 115 116 41 360 ≤ 1016680902410128 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3556 c22250R_115_10 (by norm_num)

theorem c22250R_115_8 : rowsJ2 115 116 40 360 ≤ 1025790226606392 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3555 c22250R_115_9 (by norm_num)

theorem c22250R_115_7 : rowsJ2 115 116 39 360 ≤ 1036495719333103 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3554 c22250R_115_8 (by norm_num)

theorem c22250R_115_6 : rowsJ2 115 116 38 360 ≤ 1048209947279191 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3553 c22250R_115_7 (by norm_num)

theorem c22250R_115_5 : rowsJ2 115 116 37 360 ≤ 1059396647651722 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3552 c22250R_115_6 (by norm_num)

theorem c22250R_115_4 : rowsJ2 115 116 36 360 ≤ 1068755559021688 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3551 c22250R_115_5 (by norm_num)

theorem c22250R_115_3 : rowsJ2 115 116 34 360 ≤ 1082587181468701 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3550 c22250R_115_4 (by norm_num)

theorem c22250R_115_2 : rowsJ2 115 116 32 360 ≤ 1090402651198961 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3549 c22250R_115_3 (by norm_num)

theorem c22250R_115_1 : rowsJ2 115 116 26 360 ≤ 1094758736800143 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3548 c22250R_115_2 (by norm_num)

theorem c22250R_115_0 : rowsJ2 115 116 0 360 ≤ 1094758736800143 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22250R_3547 c22250R_115_1 (by norm_num)

theorem hr22250R_115 : rows2 115 116 ≤ 1094758736800143 := rows2_le_of_rowsJ2 115 116 c22250R_115_0

theorem c22250R_116_32 : rowsJ2 116 117 104 360 ≤ 1082739287075523 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3615 rows22250R_3616 (by norm_num)

theorem c22250R_116_31 : rowsJ2 116 117 103 360 ≤ 1093042740917288 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3614 c22250R_116_32 (by norm_num)

theorem c22250R_116_30 : rowsJ2 116 117 102 360 ≤ 1102156128621653 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3613 c22250R_116_31 (by norm_num)

theorem c22250R_116_29 : rowsJ2 116 117 101 360 ≤ 1110183554844991 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3612 c22250R_116_30 (by norm_num)

theorem c22250R_116_28 : rowsJ2 116 117 100 360 ≤ 1117183672079171 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3611 c22250R_116_29 (by norm_num)

theorem c22250R_116_27 : rowsJ2 116 117 99 360 ≤ 1123254848096739 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3610 c22250R_116_28 (by norm_num)

theorem c22250R_116_26 : rowsJ2 116 117 98 360 ≤ 1128451356032191 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3609 c22250R_116_27 (by norm_num)

theorem c22250R_116_25 : rowsJ2 116 117 96 360 ≤ 1136550751962783 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3608 c22250R_116_26 (by norm_num)

theorem c22250R_116_24 : rowsJ2 116 117 94 360 ≤ 1142040288435105 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3607 c22250R_116_25 (by norm_num)

theorem c22250R_116_23 : rowsJ2 116 117 92 360 ≤ 1145449453023163 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3606 c22250R_116_24 (by norm_num)

theorem c22250R_116_22 : rowsJ2 116 117 90 360 ≤ 1147294753102101 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3605 c22250R_116_23 (by norm_num)

theorem c22250R_116_21 : rowsJ2 116 117 88 360 ≤ 1148106532825911 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3604 c22250R_116_22 (by norm_num)

theorem c22250R_116_20 : rowsJ2 116 117 86 360 ≤ 1148394371428139 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3603 c22250R_116_21 (by norm_num)

theorem c22250R_116_19 : rowsJ2 116 117 84 360 ≤ 1148722140239854 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3602 c22250R_116_20 (by norm_num)

theorem c22250R_116_18 : rowsJ2 116 117 82 360 ≤ 1149238126283402 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3601 c22250R_116_19 (by norm_num)

theorem c22250R_116_17 : rowsJ2 116 117 79 360 ≤ 1149422100986127 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3600 c22250R_116_18 (by norm_num)

theorem c22250R_116_16 : rowsJ2 116 117 75 360 ≤ 1149422100986127 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3599 c22250R_116_17 (by norm_num)

theorem c22250R_116_15 : rowsJ2 116 117 70 360 ≤ 1149422100986127 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3598 c22250R_116_16 (by norm_num)

theorem c22250R_116_14 : rowsJ2 116 117 64 360 ≤ 1150812661852876 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3597 c22250R_116_15 (by norm_num)

theorem c22250R_116_13 : rowsJ2 116 117 54 360 ≤ 1151106124423029 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3596 c22250R_116_14 (by norm_num)

theorem c22250R_116_12 : rowsJ2 116 117 49 360 ≤ 1151509565836182 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3595 c22250R_116_13 (by norm_num)

theorem c22250R_116_11 : rowsJ2 116 117 46 360 ≤ 1155561375352945 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3594 c22250R_116_12 (by norm_num)

theorem c22250R_116_10 : rowsJ2 116 117 44 360 ≤ 1162123651644346 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3593 c22250R_116_11 (by norm_num)

theorem c22250R_116_9 : rowsJ2 116 117 42 360 ≤ 1172522563879485 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3592 c22250R_116_10 (by norm_num)

theorem c22250R_116_8 : rowsJ2 116 117 40 360 ≤ 1187715642629936 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3591 c22250R_116_9 (by norm_num)

theorem c22250R_116_7 : rowsJ2 116 117 39 360 ≤ 1197531870177734 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3590 c22250R_116_8 (by norm_num)

theorem c22250R_116_6 : rowsJ2 116 117 38 360 ≤ 1208293990464856 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3589 c22250R_116_7 (by norm_num)

theorem c22250R_116_5 : rowsJ2 116 117 37 360 ≤ 1220071709620640 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3588 c22250R_116_6 (by norm_num)

theorem c22250R_116_4 : rowsJ2 116 117 36 360 ≤ 1229841456616465 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3587 c22250R_116_5 (by norm_num)

theorem c22250R_116_3 : rowsJ2 116 117 34 360 ≤ 1244527418642732 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3586 c22250R_116_4 (by norm_num)

theorem c22250R_116_2 : rowsJ2 116 117 32 360 ≤ 1253041029075487 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3585 c22250R_116_3 (by norm_num)

theorem c22250R_116_1 : rowsJ2 116 117 27 360 ≤ 1258296390549625 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3584 c22250R_116_2 (by norm_num)

theorem c22250R_116_0 : rowsJ2 116 117 0 360 ≤ 1258296390549625 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22250R_3583 c22250R_116_1 (by norm_num)

theorem hr22250R_116 : rows2 116 117 ≤ 1258296390549625 := rows2_le_of_rowsJ2 116 117 c22250R_116_0

theorem c22250R_117_30 : rowsJ2 117 118 104 360 ≤ 1156919368551519 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3647 rows22250R_3648 (by norm_num)

theorem c22250R_117_29 : rowsJ2 117 118 103 360 ≤ 1167742364724812 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3646 c22250R_117_30 (by norm_num)

theorem c22250R_117_28 : rowsJ2 117 118 102 360 ≤ 1177350097473448 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3645 c22250R_117_29 (by norm_num)

theorem c22250R_117_27 : rowsJ2 117 118 101 360 ≤ 1185805849913838 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3644 c22250R_117_28 (by norm_num)

theorem c22250R_117_26 : rowsJ2 117 118 100 360 ≤ 1193213380322766 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3643 c22250R_117_27 (by norm_num)

theorem c22250R_117_25 : rowsJ2 117 118 99 360 ≤ 1199631006270536 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3642 c22250R_117_26 (by norm_num)

theorem c22250R_117_24 : rowsJ2 117 118 97 360 ≤ 1209844846414951 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3641 c22250R_117_25 (by norm_num)

theorem c22250R_117_23 : rowsJ2 117 118 95 360 ≤ 1217037087075906 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3640 c22250R_117_24 (by norm_num)

theorem c22250R_117_22 : rowsJ2 117 118 93 360 ≤ 1221764844448427 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3639 c22250R_117_23 (by norm_num)

theorem c22250R_117_21 : rowsJ2 117 118 91 360 ≤ 1224556813644475 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3638 c22250R_117_22 (by norm_num)

theorem c22250R_117_20 : rowsJ2 117 118 88 360 ≤ 1226228427288438 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3637 c22250R_117_21 (by norm_num)

theorem c22250R_117_19 : rowsJ2 117 118 85 360 ≤ 1226481722660157 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3636 c22250R_117_20 (by norm_num)

theorem c22250R_117_18 : rowsJ2 117 118 83 360 ≤ 1226725630360752 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3635 c22250R_117_19 (by norm_num)

theorem c22250R_117_17 : rowsJ2 117 118 81 360 ≤ 1227045535295694 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3634 c22250R_117_18 (by norm_num)

theorem c22250R_117_16 : rowsJ2 117 118 78 360 ≤ 1227091662273144 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3633 c22250R_117_17 (by norm_num)

theorem c22250R_117_15 : rowsJ2 117 118 74 360 ≤ 1227091662273144 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3632 c22250R_117_16 (by norm_num)

theorem c22250R_117_14 : rowsJ2 117 118 69 360 ≤ 1227281520675024 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3631 c22250R_117_15 (by norm_num)

theorem c22250R_117_13 : rowsJ2 117 118 64 360 ≤ 1229302252928493 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3630 c22250R_117_14 (by norm_num)

theorem c22250R_117_12 : rowsJ2 117 118 53 360 ≤ 1229723615544128 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3629 c22250R_117_13 (by norm_num)

theorem c22250R_117_11 : rowsJ2 117 118 48 360 ≤ 1230381354284934 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3628 c22250R_117_12 (by norm_num)

theorem c22250R_117_10 : rowsJ2 117 118 45 360 ≤ 1235415405952074 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3627 c22250R_117_11 (by norm_num)

theorem c22250R_117_9 : rowsJ2 117 118 43 360 ≤ 1242729193506974 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3626 c22250R_117_10 (by norm_num)

theorem c22250R_117_8 : rowsJ2 117 118 41 360 ≤ 1254007216680924 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3625 c22250R_117_9 (by norm_num)

theorem c22250R_117_7 : rowsJ2 117 118 39 360 ≤ 1270503817170673 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3624 c22250R_117_8 (by norm_num)

theorem c22250R_117_6 : rowsJ2 117 118 38 360 ≤ 1280372327435152 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3623 c22250R_117_7 (by norm_num)

theorem c22250R_117_5 : rowsJ2 117 118 37 360 ≤ 1291193172140314 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3622 c22250R_117_6 (by norm_num)

theorem c22250R_117_4 : rowsJ2 117 118 36 360 ≤ 1301469724750294 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3621 c22250R_117_5 (by norm_num)

theorem c22250R_117_3 : rowsJ2 117 118 34 360 ≤ 1316916005198734 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3620 c22250R_117_4 (by norm_num)

theorem c22250R_117_2 : rowsJ2 117 118 32 360 ≤ 1326224393228174 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3619 c22250R_117_3 (by norm_num)

theorem c22250R_117_1 : rowsJ2 117 118 27 360 ≤ 1332383946765749 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3618 c22250R_117_2 (by norm_num)

theorem c22250R_117_0 : rowsJ2 117 118 0 360 ≤ 1332383946765749 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22250R_3617 c22250R_117_1 (by norm_num)

theorem hr22250R_117 : rows2 117 118 ≤ 1332383946765749 := rows2_le_of_rowsJ2 117 118 c22250R_117_0

theorem c22250R_118_30 : rowsJ2 118 119 103 360 ≤ 1321876427443581 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3679 rows22250R_3680 (by norm_num)

theorem c22250R_118_29 : rowsJ2 118 119 102 360 ≤ 1331990076011035 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3678 c22250R_118_30 (by norm_num)

theorem c22250R_118_28 : rowsJ2 118 119 101 360 ≤ 1340927429905067 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3677 c22250R_118_29 (by norm_num)

theorem c22250R_118_27 : rowsJ2 118 119 100 360 ≤ 1348751374503411 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3676 c22250R_118_28 (by norm_num)

theorem c22250R_118_26 : rowsJ2 118 119 99 360 ≤ 1355565338181627 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3675 c22250R_118_27 (by norm_num)

theorem c22250R_118_25 : rowsJ2 118 119 98 360 ≤ 1361427316954447 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3674 c22250R_118_26 (by norm_num)

theorem c22250R_118_24 : rowsJ2 118 119 96 360 ≤ 1370642612213144 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3673 c22250R_118_25 (by norm_num)

theorem c22250R_118_23 : rowsJ2 118 119 94 360 ≤ 1376985250616330 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3672 c22250R_118_24 (by norm_num)

theorem c22250R_118_22 : rowsJ2 118 119 92 360 ≤ 1381011171316552 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3671 c22250R_118_23 (by norm_num)

theorem c22250R_118_21 : rowsJ2 118 119 89 360 ≤ 1383859329894252 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3670 c22250R_118_22 (by norm_num)

theorem c22250R_118_20 : rowsJ2 118 119 86 360 ≤ 1384363456579560 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3669 c22250R_118_21 (by norm_num)

theorem c22250R_118_19 : rowsJ2 118 119 83 360 ≤ 1384502930819711 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3668 c22250R_118_20 (by norm_num)

theorem c22250R_118_18 : rowsJ2 118 119 81 360 ≤ 1384742397431189 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3667 c22250R_118_19 (by norm_num)

theorem c22250R_118_17 : rowsJ2 118 119 79 360 ≤ 1384788249513985 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3666 c22250R_118_18 (by norm_num)

theorem c22250R_118_16 : rowsJ2 118 119 76 360 ≤ 1384788249513985 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3665 c22250R_118_17 (by norm_num)

theorem c22250R_118_15 : rowsJ2 118 119 72 360 ≤ 1384788249513985 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3664 c22250R_118_16 (by norm_num)

theorem c22250R_118_14 : rowsJ2 118 119 68 360 ≤ 1385948374725774 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3663 c22250R_118_15 (by norm_num)

theorem c22250R_118_13 : rowsJ2 118 119 63 360 ≤ 1388519000724726 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3662 c22250R_118_14 (by norm_num)

theorem c22250R_118_12 : rowsJ2 118 119 52 360 ≤ 1388819609810013 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3661 c22250R_118_13 (by norm_num)

theorem c22250R_118_11 : rowsJ2 118 119 47 360 ≤ 1389995251262603 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3660 c22250R_118_12 (by norm_num)

theorem c22250R_118_10 : rowsJ2 118 119 44 360 ≤ 1396124412276738 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3659 c22250R_118_11 (by norm_num)

theorem c22250R_118_9 : rowsJ2 118 119 42 360 ≤ 1404207539600707 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3658 c22250R_118_10 (by norm_num)

theorem c22250R_118_8 : rowsJ2 118 119 40 360 ≤ 1416572807860759 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3657 c22250R_118_9 (by norm_num)

theorem c22250R_118_7 : rowsJ2 118 119 38 360 ≤ 1433825783713338 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3656 c22250R_118_8 (by norm_num)

theorem c22250R_118_6 : rowsJ2 118 119 37 360 ≤ 1443748498989586 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3655 c22250R_118_7 (by norm_num)

theorem c22250R_118_5 : rowsJ2 118 119 36 360 ≤ 1454630223962342 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3654 c22250R_118_6 (by norm_num)

theorem c22250R_118_4 : rowsJ2 118 119 35 360 ≤ 1463528409704231 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3653 c22250R_118_5 (by norm_num)

theorem c22250R_118_3 : rowsJ2 118 119 33 360 ≤ 1476665860256002 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3652 c22250R_118_4 (by norm_num)

theorem c22250R_118_2 : rowsJ2 118 119 31 360 ≤ 1483980773017584 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3651 c22250R_118_3 (by norm_num)

theorem c22250R_118_1 : rowsJ2 118 119 27 360 ≤ 1488100160167995 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3650 c22250R_118_2 (by norm_num)

theorem c22250R_118_0 : rowsJ2 118 119 0 360 ≤ 1488100160167995 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22250R_3649 c22250R_118_1 (by norm_num)

theorem hr22250R_118 : rows2 118 119 ≤ 1488100160167995 := rows2_le_of_rowsJ2 118 119 c22250R_118_0

theorem c22250R_119_29 : rowsJ2 119 120 103 360 ≤ 1388582751149621 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3710 rows22250R_3711 (by norm_num)

theorem c22250R_119_28 : rowsJ2 119 120 102 360 ≤ 1399225826243151 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3709 c22250R_119_29 (by norm_num)

theorem c22250R_119_27 : rowsJ2 119 120 101 360 ≤ 1408622487390647 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3708 c22250R_119_28 (by norm_num)

theorem c22250R_119_26 : rowsJ2 119 120 100 360 ≤ 1416882099195852 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3707 c22250R_119_27 (by norm_num)

theorem c22250R_119_25 : rowsJ2 119 120 99 360 ≤ 1424067159401735 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3706 c22250R_119_26 (by norm_num)

theorem c22250R_119_24 : rowsJ2 119 120 98 360 ≤ 1430280780349407 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3705 c22250R_119_25 (by norm_num)

theorem c22250R_119_23 : rowsJ2 119 120 96 360 ≤ 1440064365846971 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3704 c22250R_119_24 (by norm_num)

theorem c22250R_119_22 : rowsJ2 119 120 94 360 ≤ 1446836678542711 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3703 c22250R_119_23 (by norm_num)

theorem c22250R_119_21 : rowsJ2 119 120 92 360 ≤ 1451167794276153 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3702 c22250R_119_22 (by norm_num)

theorem c22250R_119_20 : rowsJ2 119 120 89 360 ≤ 1454258179525178 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3701 c22250R_119_21 (by norm_num)

theorem c22250R_119_19 : rowsJ2 119 120 86 360 ≤ 1454797287506964 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3700 c22250R_119_20 (by norm_num)

theorem c22250R_119_18 : rowsJ2 119 120 83 360 ≤ 1454832054024105 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3699 c22250R_119_19 (by norm_num)

theorem c22250R_119_17 : rowsJ2 119 120 81 360 ≤ 1454946429998399 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3698 c22250R_119_18 (by norm_num)

theorem c22250R_119_16 : rowsJ2 119 120 78 360 ≤ 1454992010443612 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3697 c22250R_119_17 (by norm_num)

theorem c22250R_119_15 : rowsJ2 119 120 74 360 ≤ 1454992010443612 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3696 c22250R_119_16 (by norm_num)

theorem c22250R_119_14 : rowsJ2 119 120 70 360 ≤ 1455717501836678 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3695 c22250R_119_15 (by norm_num)

theorem c22250R_119_13 : rowsJ2 119 120 67 360 ≤ 1457805413114077 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3694 c22250R_119_14 (by norm_num)

theorem c22250R_119_12 : rowsJ2 119 120 62 360 ≤ 1460515637816259 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3693 c22250R_119_13 (by norm_num)

theorem c22250R_119_11 : rowsJ2 119 120 51 360 ≤ 1460690235409497 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3692 c22250R_119_12 (by norm_num)

theorem c22250R_119_10 : rowsJ2 119 120 46 360 ≤ 1462403052416186 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3691 c22250R_119_11 (by norm_num)

theorem c22250R_119_9 : rowsJ2 119 120 43 360 ≤ 1469385723727477 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3690 c22250R_119_10 (by norm_num)

theorem c22250R_119_8 : rowsJ2 119 120 41 360 ≤ 1478166535497052 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3689 c22250R_119_9 (by norm_num)

theorem c22250R_119_7 : rowsJ2 119 120 39 360 ≤ 1491651964399656 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3688 c22250R_119_8 (by norm_num)

theorem c22250R_119_6 : rowsJ2 119 120 37 360 ≤ 1508999250249085 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3687 c22250R_119_7 (by norm_num)

theorem c22250R_119_5 : rowsJ2 119 120 36 360 ≤ 1518978147143869 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3686 c22250R_119_6 (by norm_num)

theorem c22250R_119_4 : rowsJ2 119 120 35 360 ≤ 1528395995386829 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3685 c22250R_119_5 (by norm_num)

theorem c22250R_119_3 : rowsJ2 119 120 34 360 ≤ 1536041906357746 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3684 c22250R_119_4 (by norm_num)

theorem c22250R_119_2 : rowsJ2 119 120 32 360 ≤ 1546945862238661 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3683 c22250R_119_3 (by norm_num)

theorem c22250R_119_1 : rowsJ2 119 120 28 360 ≤ 1554923382900515 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3682 c22250R_119_2 (by norm_num)

theorem c22250R_119_0 : rowsJ2 119 120 0 360 ≤ 1555108541718514 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22250R_3681 c22250R_119_1 (by norm_num)

theorem hr22250R_119 : rows2 119 120 ≤ 1555108541718514 := rows2_le_of_rowsJ2 119 120 c22250R_119_0

theorem c22250R_120_27 : rowsJ2 120 121 102 360 ≤ 1544539808907595 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3739 rows22250R_3740 (by norm_num)

theorem c22250R_120_26 : rowsJ2 120 121 101 360 ≤ 1554451554229719 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3738 c22250R_120_27 (by norm_num)

theorem c22250R_120_25 : rowsJ2 120 121 100 360 ≤ 1563157031566423 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3737 c22250R_120_26 (by norm_num)

theorem c22250R_120_24 : rowsJ2 120 121 99 360 ≤ 1570765223493763 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3736 c22250R_120_25 (by norm_num)

theorem c22250R_120_23 : rowsJ2 120 121 97 360 ≤ 1582978935110542 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3735 c22250R_120_24 (by norm_num)

theorem c22250R_120_22 : rowsJ2 120 121 95 360 ≤ 1591732803946762 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3734 c22250R_120_23 (by norm_num)

theorem c22250R_120_21 : rowsJ2 120 121 93 360 ≤ 1597628877590850 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3733 c22250R_120_22 (by norm_num)

theorem c22250R_120_20 : rowsJ2 120 121 91 360 ≤ 1601236032685273 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3732 c22250R_120_21 (by norm_num)

theorem c22250R_120_19 : rowsJ2 120 121 88 360 ≤ 1603524725948429 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3731 c22250R_120_20 (by norm_num)

theorem c22250R_120_18 : rowsJ2 120 121 85 360 ≤ 1603718911509034 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3730 c22250R_120_19 (by norm_num)

theorem c22250R_120_17 : rowsJ2 120 121 82 360 ≤ 1603730396883704 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3729 c22250R_120_18 (by norm_num)

theorem c22250R_120_16 : rowsJ2 120 121 79 360 ≤ 1603798497927562 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3728 c22250R_120_17 (by norm_num)

theorem c22250R_120_15 : rowsJ2 120 121 76 360 ≤ 1603798497927562 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3727 c22250R_120_16 (by norm_num)

theorem c22250R_120_14 : rowsJ2 120 121 72 360 ≤ 1604100435476976 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3726 c22250R_120_15 (by norm_num)

theorem c22250R_120_13 : rowsJ2 120 121 69 360 ≤ 1606212747191305 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3725 c22250R_120_14 (by norm_num)

theorem c22250R_120_12 : rowsJ2 120 121 66 360 ≤ 1609017210239061 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3724 c22250R_120_13 (by norm_num)

theorem c22250R_120_11 : rowsJ2 120 121 62 360 ≤ 1611448417566699 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3723 c22250R_120_12 (by norm_num)

theorem c22250R_120_10 : rowsJ2 120 121 50 360 ≤ 1611756491970319 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3722 c22250R_120_11 (by norm_num)

theorem c22250R_120_9 : rowsJ2 120 121 45 360 ≤ 1614287340884733 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3721 c22250R_120_10 (by norm_num)

theorem c22250R_120_8 : rowsJ2 120 121 42 360 ≤ 1622143923227320 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3720 c22250R_120_9 (by norm_num)

theorem c22250R_120_7 : rowsJ2 120 121 40 360 ≤ 1631828834532288 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3719 c22250R_120_8 (by norm_num)

theorem c22250R_120_6 : rowsJ2 120 121 38 360 ≤ 1645970469018645 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3718 c22250R_120_7 (by norm_num)

theorem c22250R_120_5 : rowsJ2 120 121 36 360 ≤ 1663415483160842 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3717 c22250R_120_6 (by norm_num)

theorem c22250R_120_4 : rowsJ2 120 121 35 360 ≤ 1673452595462055 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3716 c22250R_120_5 (by norm_num)

theorem c22250R_120_3 : rowsJ2 120 121 34 360 ≤ 1681532542613006 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3715 c22250R_120_4 (by norm_num)

theorem c22250R_120_2 : rowsJ2 120 121 32 360 ≤ 1693139433390631 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3714 c22250R_120_3 (by norm_num)

theorem c22250R_120_1 : rowsJ2 120 121 28 360 ≤ 1702029154743775 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3713 c22250R_120_2 (by norm_num)

theorem c22250R_120_0 : rowsJ2 120 121 0 360 ≤ 1702403443693671 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22250R_3712 c22250R_120_1 (by norm_num)

theorem hr22250R_120 : rows2 120 121 ≤ 1702403443693671 := rows2_le_of_rowsJ2 120 121 c22250R_120_0

theorem c22250R_121_27 : rowsJ2 121 122 102 360 ≤ 1415981055118285 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3768 rows22250R_3769 (by norm_num)

theorem c22250R_121_26 : rowsJ2 121 122 101 360 ≤ 1426386257669864 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3767 c22250R_121_27 (by norm_num)

theorem c22250R_121_25 : rowsJ2 121 122 100 360 ≤ 1435558492328307 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3766 c22250R_121_26 (by norm_num)

theorem c22250R_121_24 : rowsJ2 121 122 99 360 ≤ 1443564904063070 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3765 c22250R_121_25 (by norm_num)

theorem c22250R_121_23 : rowsJ2 121 122 98 360 ≤ 1450514107272479 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3764 c22250R_121_24 (by norm_num)

theorem c22250R_121_22 : rowsJ2 121 122 96 360 ≤ 1461528696934484 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3763 c22250R_121_23 (by norm_num)

theorem c22250R_121_21 : rowsJ2 121 122 94 360 ≤ 1469240098284302 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3762 c22250R_121_22 (by norm_num)

theorem c22250R_121_20 : rowsJ2 121 122 92 360 ≤ 1474248693176684 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3761 c22250R_121_21 (by norm_num)

theorem c22250R_121_19 : rowsJ2 121 122 89 360 ≤ 1477923140707636 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3760 c22250R_121_20 (by norm_num)

theorem c22250R_121_18 : rowsJ2 121 122 86 360 ≤ 1478598184261394 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3759 c22250R_121_19 (by norm_num)

theorem c22250R_121_17 : rowsJ2 121 122 83 360 ≤ 1478598184261394 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3758 c22250R_121_18 (by norm_num)

theorem c22250R_121_16 : rowsJ2 121 122 80 360 ≤ 1478609510367408 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3757 c22250R_121_17 (by norm_num)

theorem c22250R_121_15 : rowsJ2 121 122 77 360 ≤ 1478609510367408 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3756 c22250R_121_16 (by norm_num)

theorem c22250R_121_14 : rowsJ2 121 122 74 360 ≤ 1478609510367408 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3755 c22250R_121_15 (by norm_num)

theorem c22250R_121_13 : rowsJ2 121 122 71 360 ≤ 1480361664581539 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3754 c22250R_121_14 (by norm_num)

theorem c22250R_121_12 : rowsJ2 121 122 69 360 ≤ 1482433988267905 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3753 c22250R_121_13 (by norm_num)

theorem c22250R_121_11 : rowsJ2 121 122 66 360 ≤ 1485820155420389 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3752 c22250R_121_12 (by norm_num)

theorem c22250R_121_10 : rowsJ2 121 122 61 360 ≤ 1488993523227586 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3751 c22250R_121_11 (by norm_num)

theorem c22250R_121_9 : rowsJ2 121 122 49 360 ≤ 1489172505483088 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3750 c22250R_121_10 (by norm_num)

theorem c22250R_121_8 : rowsJ2 121 122 44 360 ≤ 1492361858987366 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3749 c22250R_121_9 (by norm_num)

theorem c22250R_121_7 : rowsJ2 121 122 41 360 ≤ 1500926363564182 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3748 c22250R_121_8 (by norm_num)

theorem c22250R_121_6 : rowsJ2 121 122 39 360 ≤ 1511540944344470 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3747 c22250R_121_7 (by norm_num)

theorem c22250R_121_5 : rowsJ2 121 122 37 360 ≤ 1525760880490182 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3746 c22250R_121_6 (by norm_num)

theorem c22250R_121_4 : rowsJ2 121 122 35 360 ≤ 1543307139599895 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3745 c22250R_121_5 (by norm_num)

theorem c22250R_121_3 : rowsJ2 121 122 33 360 ≤ 1558791119562693 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3744 c22250R_121_4 (by norm_num)

theorem c22250R_121_2 : rowsJ2 121 122 31 360 ≤ 1568263841927475 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3743 c22250R_121_3 (by norm_num)

theorem c22250R_121_1 : rowsJ2 121 122 28 360 ≤ 1574034532592537 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3742 c22250R_121_2 (by norm_num)

theorem c22250R_121_0 : rowsJ2 121 122 0 360 ≤ 1574696018582904 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22250R_3741 c22250R_121_1 (by norm_num)

theorem hr22250R_121 : rows2 121 122 ≤ 1574696018582904 := rows2_le_of_rowsJ2 121 122 c22250R_121_0

theorem c22250R_122_26 : rowsJ2 122 123 101 360 ≤ 1407825591020901 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3796 rows22250R_3797 (by norm_num)

theorem c22250R_122_25 : rowsJ2 122 123 100 360 ≤ 1417476138351406 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3795 c22250R_122_26 (by norm_num)

theorem c22250R_122_24 : rowsJ2 122 123 99 360 ≤ 1425935147147128 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3794 c22250R_122_25 (by norm_num)

theorem c22250R_122_23 : rowsJ2 122 123 97 360 ≤ 1439586945700256 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3793 c22250R_122_24 (by norm_num)

theorem c22250R_122_22 : rowsJ2 122 123 95 360 ≤ 1449458982454283 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3792 c22250R_122_23 (by norm_num)

theorem c22250R_122_21 : rowsJ2 122 123 93 360 ≤ 1456186949196097 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3791 c22250R_122_22 (by norm_num)

theorem c22250R_122_20 : rowsJ2 122 123 91 360 ≤ 1460369702511478 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3790 c22250R_122_21 (by norm_num)

theorem c22250R_122_19 : rowsJ2 122 123 88 360 ≤ 1463098981813194 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3789 c22250R_122_20 (by norm_num)

theorem c22250R_122_18 : rowsJ2 122 123 85 360 ≤ 1463339325042035 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3788 c22250R_122_19 (by norm_num)

theorem c22250R_122_17 : rowsJ2 122 123 82 360 ≤ 1463339325042035 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3787 c22250R_122_18 (by norm_num)

theorem c22250R_122_16 : rowsJ2 122 123 79 360 ≤ 1463339325042035 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3786 c22250R_122_17 (by norm_num)

theorem c22250R_122_15 : rowsJ2 122 123 76 360 ≤ 1463339325042035 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3785 c22250R_122_16 (by norm_num)

theorem c22250R_122_14 : rowsJ2 122 123 73 360 ≤ 1464390690435055 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3784 c22250R_122_15 (by norm_num)

theorem c22250R_122_13 : rowsJ2 122 123 71 360 ≤ 1466447741540193 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3783 c22250R_122_14 (by norm_num)

theorem c22250R_122_12 : rowsJ2 122 123 69 360 ≤ 1469062796946923 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3782 c22250R_122_13 (by norm_num)

theorem c22250R_122_11 : rowsJ2 122 123 67 360 ≤ 1471806784717414 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3781 c22250R_122_12 (by norm_num)

theorem c22250R_122_10 : rowsJ2 122 123 64 360 ≤ 1475263918954577 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3780 c22250R_122_11 (by norm_num)

theorem c22250R_122_9 : rowsJ2 122 123 55 360 ≤ 1477249119957704 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3779 c22250R_122_10 (by norm_num)

theorem c22250R_122_8 : rowsJ2 122 123 46 360 ≤ 1477703728415769 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3778 c22250R_122_9 (by norm_num)

theorem c22250R_122_7 : rowsJ2 122 123 42 360 ≤ 1483608961258274 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3777 c22250R_122_8 (by norm_num)

theorem c22250R_122_6 : rowsJ2 122 123 39 360 ≤ 1495996681326623 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3776 c22250R_122_7 (by norm_num)

theorem c22250R_122_5 : rowsJ2 122 123 37 360 ≤ 1508703130834973 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3775 c22250R_122_6 (by norm_num)

theorem c22250R_122_4 : rowsJ2 122 123 35 360 ≤ 1524652309570635 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3774 c22250R_122_5 (by norm_num)

theorem c22250R_122_3 : rowsJ2 122 123 33 360 ≤ 1541214995040841 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3773 c22250R_122_4 (by norm_num)

theorem c22250R_122_2 : rowsJ2 122 123 31 360 ≤ 1551409992465743 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3772 c22250R_122_3 (by norm_num)

theorem c22250R_122_1 : rowsJ2 122 123 28 360 ≤ 1557728220294767 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3771 c22250R_122_2 (by norm_num)

theorem c22250R_122_0 : rowsJ2 122 123 0 360 ≤ 1558678670810076 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22250R_3770 c22250R_122_1 (by norm_num)

theorem hr22250R_122 : rows2 122 123 ≤ 1558678670810076 := rows2_le_of_rowsJ2 122 123 c22250R_122_0

theorem c22250R_123_27 : rowsJ2 123 124 101 360 ≤ 1309584813673956 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3825 rows22250R_3826 (by norm_num)

theorem c22250R_123_26 : rowsJ2 123 124 100 360 ≤ 1319736397965584 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3824 c22250R_123_27 (by norm_num)

theorem c22250R_123_25 : rowsJ2 123 124 99 360 ≤ 1328623532599833 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3823 c22250R_123_26 (by norm_num)

theorem c22250R_123_24 : rowsJ2 123 124 98 360 ≤ 1336360884671804 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3822 c22250R_123_25 (by norm_num)

theorem c22250R_123_23 : rowsJ2 123 124 96 360 ≤ 1348693031023887 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3821 c22250R_123_24 (by norm_num)

theorem c22250R_123_22 : rowsJ2 123 124 94 360 ≤ 1357408134533084 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3820 c22250R_123_23 (by norm_num)

theorem c22250R_123_21 : rowsJ2 123 124 92 360 ≤ 1363139851088784 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3819 c22250R_123_22 (by norm_num)

theorem c22250R_123_20 : rowsJ2 123 124 89 360 ≤ 1367436768223123 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3818 c22250R_123_21 (by norm_num)

theorem c22250R_123_19 : rowsJ2 123 124 86 360 ≤ 1368256464283497 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3817 c22250R_123_20 (by norm_num)

theorem c22250R_123_18 : rowsJ2 123 124 83 360 ≤ 1368256464283497 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3816 c22250R_123_19 (by norm_num)

theorem c22250R_123_17 : rowsJ2 123 124 80 360 ≤ 1368256464283497 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3815 c22250R_123_18 (by norm_num)

theorem c22250R_123_16 : rowsJ2 123 124 77 360 ≤ 1368256464283497 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3814 c22250R_123_17 (by norm_num)

theorem c22250R_123_15 : rowsJ2 123 124 74 360 ≤ 1369407771345671 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3813 c22250R_123_16 (by norm_num)

theorem c22250R_123_14 : rowsJ2 123 124 72 360 ≤ 1371702989338384 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3812 c22250R_123_15 (by norm_num)

theorem c22250R_123_13 : rowsJ2 123 124 70 360 ≤ 1374686049129409 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3811 c22250R_123_14 (by norm_num)

theorem c22250R_123_12 : rowsJ2 123 124 68 360 ≤ 1377921250028611 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3810 c22250R_123_13 (by norm_num)

theorem c22250R_123_11 : rowsJ2 123 124 66 360 ≤ 1380989254544593 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3809 c22250R_123_12 (by norm_num)

theorem c22250R_123_10 : rowsJ2 123 124 64 360 ≤ 1383483534238270 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3808 c22250R_123_11 (by norm_num)

theorem c22250R_123_9 : rowsJ2 123 124 60 360 ≤ 1385758829948307 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3807 c22250R_123_10 (by norm_num)

theorem c22250R_123_8 : rowsJ2 123 124 47 360 ≤ 1385942394117152 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3806 c22250R_123_9 (by norm_num)

theorem c22250R_123_7 : rowsJ2 123 124 42 360 ≤ 1390489923416477 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3805 c22250R_123_8 (by norm_num)

theorem c22250R_123_6 : rowsJ2 123 124 39 360 ≤ 1400909747912515 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3804 c22250R_123_7 (by norm_num)

theorem c22250R_123_5 : rowsJ2 123 124 37 360 ≤ 1412139484451642 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3803 c22250R_123_6 (by norm_num)

theorem c22250R_123_4 : rowsJ2 123 124 35 360 ≤ 1426524510141067 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3802 c22250R_123_5 (by norm_num)

theorem c22250R_123_3 : rowsJ2 123 124 33 360 ≤ 1442843125575811 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3801 c22250R_123_4 (by norm_num)

theorem c22250R_123_2 : rowsJ2 123 124 31 360 ≤ 1453762102580242 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3800 c22250R_123_3 (by norm_num)

theorem c22250R_123_1 : rowsJ2 123 124 28 360 ≤ 1460726809543865 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3799 c22250R_123_2 (by norm_num)

theorem c22250R_123_0 : rowsJ2 123 124 0 360 ≤ 1461968099090283 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22250R_3798 c22250R_123_1 (by norm_num)

theorem hr22250R_123 : rows2 123 124 ≤ 1461968099090283 := rows2_le_of_rowsJ2 123 124 c22250R_123_0

theorem c22250R_124_26 : rowsJ2 124 125 100 360 ≤ 1302083745933177 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3853 rows22250R_3854 (by norm_num)

theorem c22250R_124_25 : rowsJ2 124 125 99 360 ≤ 1311455946170687 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3852 c22250R_124_26 (by norm_num)

theorem c22250R_124_24 : rowsJ2 124 125 98 360 ≤ 1319606450777518 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3851 c22250R_124_25 (by norm_num)

theorem c22250R_124_23 : rowsJ2 124 125 96 360 ≤ 1332651021439735 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3850 c22250R_124_24 (by norm_num)

theorem c22250R_124_22 : rowsJ2 124 125 94 360 ≤ 1341912925026277 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3849 c22250R_124_23 (by norm_num)

theorem c22250R_124_21 : rowsJ2 124 125 92 360 ≤ 1348043690705007 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3848 c22250R_124_22 (by norm_num)

theorem c22250R_124_20 : rowsJ2 124 125 89 360 ≤ 1352706540762799 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3847 c22250R_124_21 (by norm_num)

theorem c22250R_124_19 : rowsJ2 124 125 86 360 ≤ 1353621540572827 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3846 c22250R_124_20 (by norm_num)

theorem c22250R_124_18 : rowsJ2 124 125 83 360 ≤ 1353621540572827 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3845 c22250R_124_19 (by norm_num)

theorem c22250R_124_17 : rowsJ2 124 125 80 360 ≤ 1353621540572827 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3844 c22250R_124_18 (by norm_num)

theorem c22250R_124_16 : rowsJ2 124 125 77 360 ≤ 1353621540572827 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3843 c22250R_124_17 (by norm_num)

theorem c22250R_124_15 : rowsJ2 124 125 75 360 ≤ 1354895983079536 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3842 c22250R_124_16 (by norm_num)

theorem c22250R_124_14 : rowsJ2 124 125 73 360 ≤ 1357455896049230 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3841 c22250R_124_15 (by norm_num)

theorem c22250R_124_13 : rowsJ2 124 125 71 360 ≤ 1360836051936727 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3840 c22250R_124_14 (by norm_num)

theorem c22250R_124_12 : rowsJ2 124 125 69 360 ≤ 1364593465189959 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3839 c22250R_124_13 (by norm_num)

theorem c22250R_124_11 : rowsJ2 124 125 67 360 ≤ 1368303144119860 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3838 c22250R_124_12 (by norm_num)

theorem c22250R_124_10 : rowsJ2 124 125 65 360 ≤ 1371554346425149 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3837 c22250R_124_11 (by norm_num)

theorem c22250R_124_9 : rowsJ2 124 125 63 360 ≤ 1373947230930647 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3836 c22250R_124_10 (by norm_num)

theorem c22250R_124_8 : rowsJ2 124 125 53 360 ≤ 1375983054714635 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3835 c22250R_124_9 (by norm_num)

theorem c22250R_124_7 : rowsJ2 124 125 44 360 ≤ 1376919109879329 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3834 c22250R_124_8 (by norm_num)

theorem c22250R_124_6 : rowsJ2 124 125 40 360 ≤ 1384062444026149 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3833 c22250R_124_7 (by norm_num)

theorem c22250R_124_5 : rowsJ2 124 125 37 360 ≤ 1397685708739909 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3832 c22250R_124_6 (by norm_num)

theorem c22250R_124_4 : rowsJ2 124 125 35 360 ≤ 1410540557649242 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3831 c22250R_124_5 (by norm_num)

theorem c22250R_124_3 : rowsJ2 124 125 33 360 ≤ 1426684869153440 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3830 c22250R_124_4 (by norm_num)

theorem c22250R_124_2 : rowsJ2 124 125 31 360 ≤ 1438427234657329 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3829 c22250R_124_3 (by norm_num)

theorem c22250R_124_1 : rowsJ2 124 125 27 360 ≤ 1447083828533309 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3828 c22250R_124_2 (by norm_num)

theorem c22250R_124_0 : rowsJ2 124 125 0 360 ≤ 1447667925267427 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22250R_3827 c22250R_124_1 (by norm_num)

theorem hr22250R_124 : rows2 124 125 ≤ 1447667925267427 := rows2_le_of_rowsJ2 124 125 c22250R_124_0

theorem c22250R_125_28 : rowsJ2 125 126 100 360 ≤ 1206087608560871 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3883 rows22250R_3884 (by norm_num)

theorem c22250R_125_27 : rowsJ2 125 126 98 360 ≤ 1224504425085623 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3882 c22250R_125_28 (by norm_num)

theorem c22250R_125_26 : rowsJ2 125 126 96 360 ≤ 1238249412076421 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3881 c22250R_125_27 (by norm_num)

theorem c22250R_125_25 : rowsJ2 125 126 94 360 ≤ 1248039229967087 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3880 c22250R_125_26 (by norm_num)

theorem c22250R_125_24 : rowsJ2 125 126 92 360 ≤ 1254544154273501 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3879 c22250R_125_25 (by norm_num)

theorem c22250R_125_23 : rowsJ2 125 126 89 360 ≤ 1259505620012349 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3878 c22250R_125_24 (by norm_num)

theorem c22250R_125_22 : rowsJ2 125 126 86 360 ≤ 1260479504477079 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3877 c22250R_125_23 (by norm_num)

theorem c22250R_125_21 : rowsJ2 125 126 83 360 ≤ 1260479504477079 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3876 c22250R_125_22 (by norm_num)

theorem c22250R_125_20 : rowsJ2 125 126 80 360 ≤ 1260479504477079 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3875 c22250R_125_21 (by norm_num)

theorem c22250R_125_19 : rowsJ2 125 126 77 360 ≤ 1260957616401301 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3874 c22250R_125_20 (by norm_num)

theorem c22250R_125_18 : rowsJ2 125 126 75 360 ≤ 1263114019405124 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3873 c22250R_125_19 (by norm_num)

theorem c22250R_125_17 : rowsJ2 125 126 73 360 ≤ 1266459447799334 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3872 c22250R_125_18 (by norm_num)

theorem c22250R_125_16 : rowsJ2 125 126 72 360 ≤ 1268435022004810 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3871 c22250R_125_17 (by norm_num)

theorem c22250R_125_15 : rowsJ2 125 126 71 360 ≤ 1270531394712913 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3870 c22250R_125_16 (by norm_num)

theorem c22250R_125_14 : rowsJ2 125 126 70 360 ≤ 1272703778713835 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3869 c22250R_125_15 (by norm_num)

theorem c22250R_125_13 : rowsJ2 125 126 69 360 ≤ 1274889257066278 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3868 c22250R_125_14 (by norm_num)

theorem c22250R_125_12 : rowsJ2 125 126 68 360 ≤ 1277045024611130 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3867 c22250R_125_13 (by norm_num)

theorem c22250R_125_11 : rowsJ2 125 126 67 360 ≤ 1279110113845270 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3866 c22250R_125_12 (by norm_num)

theorem c22250R_125_10 : rowsJ2 125 126 65 360 ≤ 1282785003542136 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3865 c22250R_125_11 (by norm_num)

theorem c22250R_125_9 : rowsJ2 125 126 63 360 ≤ 1285515593977630 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3864 c22250R_125_10 (by norm_num)

theorem c22250R_125_8 : rowsJ2 125 126 52 360 ≤ 1288037614384635 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3863 c22250R_125_9 (by norm_num)

theorem c22250R_125_7 : rowsJ2 125 126 43 360 ≤ 1288978290113043 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3862 c22250R_125_8 (by norm_num)

theorem c22250R_125_6 : rowsJ2 125 126 39 360 ≤ 1296755512594711 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3861 c22250R_125_7 (by norm_num)

theorem c22250R_125_5 : rowsJ2 125 126 36 360 ≤ 1310457099397996 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3860 c22250R_125_6 (by norm_num)

theorem c22250R_125_4 : rowsJ2 125 126 34 360 ≤ 1323390089308551 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3859 c22250R_125_5 (by norm_num)

theorem c22250R_125_3 : rowsJ2 125 126 32 360 ≤ 1338242244612961 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3858 c22250R_125_4 (by norm_num)

theorem c22250R_125_2 : rowsJ2 125 126 30 360 ≤ 1347892245878854 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3857 c22250R_125_3 (by norm_num)

theorem c22250R_125_1 : rowsJ2 125 126 27 360 ≤ 1353336702557854 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3856 c22250R_125_2 (by norm_num)

theorem c22250R_125_0 : rowsJ2 125 126 0 360 ≤ 1354118929721771 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22250R_3855 c22250R_125_1 (by norm_num)

theorem hr22250R_125 : rows2 125 126 ≤ 1354118929721771 := rows2_le_of_rowsJ2 125 126 c22250R_125_0

theorem c22250R_126_29 : rowsJ2 126 127 99 360 ≤ 1199194145978036 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3914 rows22250R_3915 (by norm_num)

theorem c22250R_126_28 : rowsJ2 126 127 97 360 ≤ 1216043852227148 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3913 c22250R_126_29 (by norm_num)

theorem c22250R_126_27 : rowsJ2 126 127 95 360 ≤ 1228396746921695 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3912 c22250R_126_28 (by norm_num)

theorem c22250R_126_26 : rowsJ2 126 127 93 360 ≤ 1236966446256564 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3911 c22250R_126_27 (by norm_num)

theorem c22250R_126_25 : rowsJ2 126 127 91 360 ≤ 1242420910145559 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3910 c22250R_126_26 (by norm_num)

theorem c22250R_126_24 : rowsJ2 126 127 88 360 ≤ 1246121403010858 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3909 c22250R_126_25 (by norm_num)

theorem c22250R_126_23 : rowsJ2 126 127 85 360 ≤ 1246463270598610 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3908 c22250R_126_24 (by norm_num)

theorem c22250R_126_22 : rowsJ2 126 127 82 360 ≤ 1246463270598610 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3907 c22250R_126_23 (by norm_num)

theorem c22250R_126_21 : rowsJ2 126 127 79 360 ≤ 1246463270598610 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3906 c22250R_126_22 (by norm_num)

theorem c22250R_126_20 : rowsJ2 126 127 77 360 ≤ 1247920292958752 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3905 c22250R_126_21 (by norm_num)

theorem c22250R_126_19 : rowsJ2 126 127 75 360 ≤ 1251008504790147 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3904 c22250R_126_20 (by norm_num)

theorem c22250R_126_18 : rowsJ2 126 127 74 360 ≤ 1252993931765622 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3903 c22250R_126_19 (by norm_num)

theorem c22250R_126_17 : rowsJ2 126 127 73 360 ≤ 1255188979930060 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3902 c22250R_126_18 (by norm_num)

theorem c22250R_126_16 : rowsJ2 126 127 72 360 ≤ 1257546655857955 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3901 c22250R_126_17 (by norm_num)

theorem c22250R_126_15 : rowsJ2 126 127 71 360 ≤ 1260001977040989 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3900 c22250R_126_16 (by norm_num)

theorem c22250R_126_14 : rowsJ2 126 127 70 360 ≤ 1262510394121289 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3899 c22250R_126_15 (by norm_num)

theorem c22250R_126_13 : rowsJ2 126 127 69 360 ≤ 1265009317807106 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3898 c22250R_126_14 (by norm_num)

theorem c22250R_126_12 : rowsJ2 126 127 68 360 ≤ 1267456142900665 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3897 c22250R_126_13 (by norm_num)

theorem c22250R_126_11 : rowsJ2 126 127 67 360 ≤ 1269790191906088 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3896 c22250R_126_12 (by norm_num)

theorem c22250R_126_10 : rowsJ2 126 127 65 360 ≤ 1273937456635947 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3895 c22250R_126_11 (by norm_num)

theorem c22250R_126_9 : rowsJ2 126 127 63 360 ≤ 1277054325068750 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3894 c22250R_126_10 (by norm_num)

theorem c22250R_126_8 : rowsJ2 126 127 58 360 ≤ 1280112307062906 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3893 c22250R_126_9 (by norm_num)

theorem c22250R_126_7 : rowsJ2 126 127 44 360 ≤ 1280328195995113 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3892 c22250R_126_8 (by norm_num)

theorem c22250R_126_6 : rowsJ2 126 127 39 360 ≤ 1286434696534931 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3891 c22250R_126_7 (by norm_num)

theorem c22250R_126_5 : rowsJ2 126 127 36 360 ≤ 1298041244761326 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3890 c22250R_126_6 (by norm_num)

theorem c22250R_126_4 : rowsJ2 126 127 34 360 ≤ 1309472333577761 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3889 c22250R_126_5 (by norm_num)

theorem c22250R_126_3 : rowsJ2 126 127 32 360 ≤ 1324127493356595 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3888 c22250R_126_4 (by norm_num)

theorem c22250R_126_2 : rowsJ2 126 127 30 360 ≤ 1334621400242924 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3887 c22250R_126_3 (by norm_num)

theorem c22250R_126_1 : rowsJ2 126 127 27 360 ≤ 1340829446343140 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3886 c22250R_126_2 (by norm_num)

theorem c22250R_126_0 : rowsJ2 126 127 0 360 ≤ 1341708735083220 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22250R_3885 c22250R_126_1 (by norm_num)

theorem hr22250R_126 : rows2 126 127 ≤ 1341708735083220 := rows2_le_of_rowsJ2 126 127 c22250R_126_0

theorem c22250R_127_30 : rowsJ2 127 128 99 360 ≤ 1105376576932763 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3946 rows22250R_3947 (by norm_num)

theorem c22250R_127_29 : rowsJ2 127 128 97 360 ≤ 1123082163964061 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3945 c22250R_127_30 (by norm_num)

theorem c22250R_127_28 : rowsJ2 127 128 95 360 ≤ 1136093238868365 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3944 c22250R_127_29 (by norm_num)

theorem c22250R_127_27 : rowsJ2 127 128 93 360 ≤ 1145145454571490 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3943 c22250R_127_28 (by norm_num)

theorem c22250R_127_26 : rowsJ2 127 128 91 360 ≤ 1150926230795126 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3942 c22250R_127_27 (by norm_num)

theorem c22250R_127_25 : rowsJ2 127 128 88 360 ≤ 1154870884931233 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3941 c22250R_127_26 (by norm_num)

theorem c22250R_127_24 : rowsJ2 127 128 85 360 ≤ 1155219687372521 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3940 c22250R_127_25 (by norm_num)

theorem c22250R_127_23 : rowsJ2 127 128 82 360 ≤ 1155219687372521 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3939 c22250R_127_24 (by norm_num)

theorem c22250R_127_22 : rowsJ2 127 128 79 360 ≤ 1155647418717544 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3938 c22250R_127_23 (by norm_num)

theorem c22250R_127_21 : rowsJ2 127 128 77 360 ≤ 1157962581147493 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3937 c22250R_127_22 (by norm_num)

theorem c22250R_127_20 : rowsJ2 127 128 76 360 ≤ 1159825957156594 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3936 c22250R_127_21 (by norm_num)

theorem c22250R_127_19 : rowsJ2 127 128 75 360 ≤ 1161992088418465 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3935 c22250R_127_20 (by norm_num)

theorem c22250R_127_18 : rowsJ2 127 128 74 360 ≤ 1164411292138633 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3934 c22250R_127_19 (by norm_num)

theorem c22250R_127_17 : rowsJ2 127 128 73 360 ≤ 1167016060846486 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3933 c22250R_127_18 (by norm_num)

theorem c22250R_127_16 : rowsJ2 127 128 72 360 ≤ 1169759683788511 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3932 c22250R_127_17 (by norm_num)

theorem c22250R_127_15 : rowsJ2 127 128 71 360 ≤ 1172577548963831 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3931 c22250R_127_16 (by norm_num)

theorem c22250R_127_14 : rowsJ2 127 128 70 360 ≤ 1175425348150174 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3930 c22250R_127_15 (by norm_num)

theorem c22250R_127_13 : rowsJ2 127 128 69 360 ≤ 1178240821515726 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3929 c22250R_127_14 (by norm_num)

theorem c22250R_127_12 : rowsJ2 127 128 68 360 ≤ 1180981566636762 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3928 c22250R_127_13 (by norm_num)

theorem c22250R_127_11 : rowsJ2 127 128 67 360 ≤ 1183587197390858 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3927 c22250R_127_12 (by norm_num)

theorem c22250R_127_10 : rowsJ2 127 128 66 360 ≤ 1186016777696620 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3926 c22250R_127_11 (by norm_num)

theorem c22250R_127_9 : rowsJ2 127 128 64 360 ≤ 1190131102959541 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3925 c22250R_127_10 (by norm_num)

theorem c22250R_127_8 : rowsJ2 127 128 62 360 ≤ 1192970053405576 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3924 c22250R_127_9 (by norm_num)

theorem c22250R_127_7 : rowsJ2 127 128 50 360 ≤ 1195558084043519 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3923 c22250R_127_8 (by norm_num)

theorem c22250R_127_6 : rowsJ2 127 128 41 360 ≤ 1196606833111594 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3922 c22250R_127_7 (by norm_num)

theorem c22250R_127_5 : rowsJ2 127 128 37 360 ≤ 1205581808324652 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3921 c22250R_127_6 (by norm_num)

theorem c22250R_127_4 : rowsJ2 127 128 34 360 ≤ 1219448328112988 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3920 c22250R_127_5 (by norm_num)

theorem c22250R_127_3 : rowsJ2 127 128 32 360 ≤ 1232545886481508 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3919 c22250R_127_4 (by norm_num)

theorem c22250R_127_2 : rowsJ2 127 128 30 360 ≤ 1243888582186027 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3918 c22250R_127_3 (by norm_num)

theorem c22250R_127_1 : rowsJ2 127 128 27 360 ≤ 1251064750399711 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3917 c22250R_127_2 (by norm_num)

theorem c22250R_127_0 : rowsJ2 127 128 0 360 ≤ 1252041370459490 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22250R_3916 c22250R_127_1 (by norm_num)

theorem hr22250R_127 : rows2 127 128 ≤ 1252041370459490 := rows2_le_of_rowsJ2 127 128 c22250R_127_0

theorem c22250R_128_31 : rowsJ2 128 129 98 360 ≤ 1099044916966760 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3979 rows22250R_3980 (by norm_num)

theorem c22250R_128_30 : rowsJ2 128 129 96 360 ≤ 1115129116417292 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3978 c22250R_128_31 (by norm_num)

theorem c22250R_128_29 : rowsJ2 128 129 94 360 ≤ 1126699819656717 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3977 c22250R_128_30 (by norm_num)

theorem c22250R_128_28 : rowsJ2 128 129 92 360 ≤ 1134489493003997 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3976 c22250R_128_29 (by norm_num)

theorem c22250R_128_27 : rowsJ2 128 129 89 360 ≤ 1140576970641172 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3975 c22250R_128_28 (by norm_num)

theorem c22250R_128_26 : rowsJ2 128 129 86 360 ≤ 1141822492018363 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3974 c22250R_128_27 (by norm_num)

theorem c22250R_128_25 : rowsJ2 128 129 83 360 ≤ 1141822492018363 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3973 c22250R_128_26 (by norm_num)

theorem c22250R_128_24 : rowsJ2 128 129 80 360 ≤ 1142223118667094 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3972 c22250R_128_25 (by norm_num)

theorem c22250R_128_23 : rowsJ2 128 129 78 360 ≤ 1144359146286204 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3971 c22250R_128_24 (by norm_num)

theorem c22250R_128_22 : rowsJ2 128 129 77 360 ≤ 1146173384699843 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3970 c22250R_128_23 (by norm_num)

theorem c22250R_128_21 : rowsJ2 128 129 76 360 ≤ 1148545773826779 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3969 c22250R_128_22 (by norm_num)

theorem c22250R_128_20 : rowsJ2 128 129 75 360 ≤ 1151196007702168 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3968 c22250R_128_21 (by norm_num)

theorem c22250R_128_19 : rowsJ2 128 129 74 360 ≤ 1154074739048274 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3967 c22250R_128_20 (by norm_num)

theorem c22250R_128_18 : rowsJ2 128 129 73 360 ≤ 1157114881516129 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3966 c22250R_128_19 (by norm_num)

theorem c22250R_128_17 : rowsJ2 128 129 72 360 ≤ 1160270014056334 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3965 c22250R_128_18 (by norm_num)

theorem c22250R_128_16 : rowsJ2 128 129 71 360 ≤ 1163475900771102 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3964 c22250R_128_17 (by norm_num)

theorem c22250R_128_15 : rowsJ2 128 129 70 360 ≤ 1166688481198375 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3963 c22250R_128_16 (by norm_num)

theorem c22250R_128_14 : rowsJ2 128 129 69 360 ≤ 1169845830191655 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3962 c22250R_128_15 (by norm_num)

theorem c22250R_128_13 : rowsJ2 128 129 68 360 ≤ 1172905754365346 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3961 c22250R_128_14 (by norm_num)

theorem c22250R_128_12 : rowsJ2 128 129 67 360 ≤ 1175808163869552 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3960 c22250R_128_13 (by norm_num)

theorem c22250R_128_11 : rowsJ2 128 129 66 360 ≤ 1178512295612917 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3959 c22250R_128_12 (by norm_num)

theorem c22250R_128_10 : rowsJ2 128 129 65 360 ≤ 1180959470056150 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3958 c22250R_128_11 (by norm_num)

theorem c22250R_128_9 : rowsJ2 128 129 64 360 ≤ 1183109962029535 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3957 c22250R_128_10 (by norm_num)

theorem c22250R_128_8 : rowsJ2 128 129 62 360 ≤ 1186345521780814 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3956 c22250R_128_9 (by norm_num)

theorem c22250R_128_7 : rowsJ2 128 129 57 360 ≤ 1189484097201713 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3955 c22250R_128_8 (by norm_num)

theorem c22250R_128_6 : rowsJ2 128 129 42 360 ≤ 1189704205599057 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3954 c22250R_128_7 (by norm_num)

theorem c22250R_128_5 : rowsJ2 128 129 37 360 ≤ 1197098301020761 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3953 c22250R_128_6 (by norm_num)

theorem c22250R_128_4 : rowsJ2 128 129 34 360 ≤ 1208845366150865 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3952 c22250R_128_5 (by norm_num)

theorem c22250R_128_3 : rowsJ2 128 129 32 360 ≤ 1220422660381720 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3951 c22250R_128_4 (by norm_num)

theorem c22250R_128_2 : rowsJ2 128 129 30 360 ≤ 1232721060974230 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3950 c22250R_128_3 (by norm_num)

theorem c22250R_128_1 : rowsJ2 128 129 27 360 ≤ 1240969847331326 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3949 c22250R_128_2 (by norm_num)

theorem c22250R_128_0 : rowsJ2 128 129 0 360 ≤ 1242040073761792 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22250R_3948 c22250R_128_1 (by norm_num)

theorem hr22250R_128 : rows2 128 129 ≤ 1242040073761792 := rows2_le_of_rowsJ2 128 129 c22250R_128_0

theorem c22250R_129_29 : rowsJ2 129 130 97 360 ≤ 1016421880481223 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_4010 rows22250R_4011 (by norm_num)

theorem c22250R_129_28 : rowsJ2 129 130 95 360 ≤ 1030863673847728 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_4009 c22250R_129_29 (by norm_num)

theorem c22250R_129_27 : rowsJ2 129 130 93 360 ≤ 1040974691649209 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_4008 c22250R_129_28 (by norm_num)

theorem c22250R_129_26 : rowsJ2 129 130 90 360 ≤ 1049609096364548 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_4007 c22250R_129_27 (by norm_num)

theorem c22250R_129_25 : rowsJ2 129 130 87 360 ≤ 1052389890573772 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_4006 c22250R_129_26 (by norm_num)

theorem c22250R_129_24 : rowsJ2 129 130 83 360 ≤ 1052389890573772 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_4005 c22250R_129_25 (by norm_num)

theorem c22250R_129_23 : rowsJ2 129 130 80 360 ≤ 1053499406771422 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_4004 c22250R_129_24 (by norm_num)

theorem c22250R_129_22 : rowsJ2 129 130 78 360 ≤ 1056347345291236 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_4003 c22250R_129_23 (by norm_num)

theorem c22250R_129_21 : rowsJ2 129 130 77 360 ≤ 1058518773438976 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_4002 c22250R_129_22 (by norm_num)

theorem c22250R_129_20 : rowsJ2 129 130 76 360 ≤ 1061249183438157 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_4001 c22250R_129_21 (by norm_num)

theorem c22250R_129_19 : rowsJ2 129 130 75 360 ≤ 1064388781110537 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_4000 c22250R_129_20 (by norm_num)

theorem c22250R_129_18 : rowsJ2 129 130 74 360 ≤ 1067732013943912 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3999 c22250R_129_19 (by norm_num)

theorem c22250R_129_17 : rowsJ2 129 130 73 360 ≤ 1071212220471328 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3998 c22250R_129_18 (by norm_num)

theorem c22250R_129_16 : rowsJ2 129 130 72 360 ≤ 1074783274009111 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3997 c22250R_129_17 (by norm_num)

theorem c22250R_129_15 : rowsJ2 129 130 71 360 ≤ 1078381317912328 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3996 c22250R_129_16 (by norm_num)

theorem c22250R_129_14 : rowsJ2 129 130 70 360 ≤ 1081962543540504 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3995 c22250R_129_15 (by norm_num)

theorem c22250R_129_13 : rowsJ2 129 130 69 360 ≤ 1085465363017258 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3994 c22250R_129_14 (by norm_num)

theorem c22250R_129_12 : rowsJ2 129 130 68 360 ≤ 1088847795499291 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3993 c22250R_129_13 (by norm_num)

theorem c22250R_129_11 : rowsJ2 129 130 67 360 ≤ 1092050049468204 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3992 c22250R_129_12 (by norm_num)

theorem c22250R_129_10 : rowsJ2 129 130 66 360 ≤ 1095031537806575 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3991 c22250R_129_11 (by norm_num)

theorem c22250R_129_9 : rowsJ2 129 130 65 360 ≤ 1097733842898331 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3990 c22250R_129_10 (by norm_num)

theorem c22250R_129_8 : rowsJ2 129 130 63 360 ≤ 1102124725494960 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3989 c22250R_129_9 (by norm_num)

theorem c22250R_129_7 : rowsJ2 129 130 61 360 ≤ 1105038325026864 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3988 c22250R_129_8 (by norm_num)

theorem c22250R_129_6 : rowsJ2 129 130 48 360 ≤ 1107695362993507 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3987 c22250R_129_7 (by norm_num)

theorem c22250R_129_5 : rowsJ2 129 130 39 360 ≤ 1109673982605943 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3986 c22250R_129_6 (by norm_num)

theorem c22250R_129_4 : rowsJ2 129 130 35 360 ≤ 1119065863879822 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3985 c22250R_129_5 (by norm_num)

theorem c22250R_129_3 : rowsJ2 129 130 32 360 ≤ 1133108932242006 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3984 c22250R_129_4 (by norm_num)

theorem c22250R_129_2 : rowsJ2 129 130 30 360 ≤ 1145087645026260 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3983 c22250R_129_3 (by norm_num)

theorem c22250R_129_1 : rowsJ2 129 130 27 360 ≤ 1154416344665949 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3982 c22250R_129_2 (by norm_num)

theorem c22250R_129_0 : rowsJ2 129 130 0 360 ≤ 1155681756986644 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22250R_3981 c22250R_129_1 (by norm_num)

theorem hr22250R_129 : rows2 129 130 ≤ 1155681756986644 := rows2_le_of_rowsJ2 129 130 c22250R_129_0

theorem c22250R_130_30 : rowsJ2 130 131 96 360 ≤ 1009743820773312 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4042 rows22250R_4043 (by norm_num)

theorem c22250R_130_29 : rowsJ2 130 131 94 360 ≤ 1022600702944140 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4041 c22250R_130_30 (by norm_num)

theorem c22250R_130_28 : rowsJ2 130 131 91 360 ≤ 1034348371391318 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4040 c22250R_130_29 (by norm_num)

theorem c22250R_130_27 : rowsJ2 130 131 88 360 ≤ 1039160342273725 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4039 c22250R_130_28 (by norm_num)

theorem c22250R_130_26 : rowsJ2 130 131 84 360 ≤ 1039618040770696 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4038 c22250R_130_27 (by norm_num)

theorem c22250R_130_25 : rowsJ2 130 131 81 360 ≤ 1040629740207528 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4037 c22250R_130_26 (by norm_num)

theorem c22250R_130_24 : rowsJ2 130 131 79 360 ≤ 1043230615451201 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4036 c22250R_130_25 (by norm_num)

theorem c22250R_130_23 : rowsJ2 130 131 78 360 ≤ 1045225229735228 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4035 c22250R_130_24 (by norm_num)

theorem c22250R_130_22 : rowsJ2 130 131 77 360 ≤ 1047729063202601 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4034 c22250R_130_23 (by norm_num)

theorem c22250R_130_21 : rowsJ2 130 131 76 360 ≤ 1050792746274563 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4033 c22250R_130_22 (by norm_num)

theorem c22250R_130_20 : rowsJ2 130 131 75 360 ≤ 1054448610433767 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4032 c22250R_130_21 (by norm_num)

theorem c22250R_130_19 : rowsJ2 130 131 74 360 ≤ 1058283116932164 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4031 c22250R_130_20 (by norm_num)

theorem c22250R_130_18 : rowsJ2 130 131 73 360 ≤ 1062230036274033 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4030 c22250R_130_19 (by norm_num)

theorem c22250R_130_17 : rowsJ2 130 131 72 360 ≤ 1066243544151028 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4029 c22250R_130_18 (by norm_num)

theorem c22250R_130_16 : rowsJ2 130 131 71 360 ≤ 1070260169732481 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4028 c22250R_130_17 (by norm_num)

theorem c22250R_130_15 : rowsJ2 130 131 70 360 ≤ 1074236363700041 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4027 c22250R_130_16 (by norm_num)

theorem c22250R_130_14 : rowsJ2 130 131 69 360 ≤ 1078110881543101 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4026 c22250R_130_15 (by norm_num)

theorem c22250R_130_13 : rowsJ2 130 131 68 360 ≤ 1081841962011576 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4025 c22250R_130_14 (by norm_num)

theorem c22250R_130_12 : rowsJ2 130 131 67 360 ≤ 1085370117603841 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4024 c22250R_130_13 (by norm_num)

theorem c22250R_130_11 : rowsJ2 130 131 66 360 ≤ 1088654943830757 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4023 c22250R_130_12 (by norm_num)

theorem c22250R_130_10 : rowsJ2 130 131 65 360 ≤ 1091638290323906 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4022 c22250R_130_11 (by norm_num)

theorem c22250R_130_9 : rowsJ2 130 131 64 360 ≤ 1094280721500468 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4021 c22250R_130_10 (by norm_num)

theorem c22250R_130_8 : rowsJ2 130 131 63 360 ≤ 1096525042709529 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4020 c22250R_130_9 (by norm_num)

theorem c22250R_130_7 : rowsJ2 130 131 61 360 ≤ 1099846274965351 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4019 c22250R_130_8 (by norm_num)

theorem c22250R_130_6 : rowsJ2 130 131 56 360 ≤ 1103069110012621 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4018 c22250R_130_7 (by norm_num)

theorem c22250R_130_5 : rowsJ2 130 131 40 360 ≤ 1103700758596023 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4017 c22250R_130_6 (by norm_num)

theorem c22250R_130_4 : rowsJ2 130 131 35 360 ≤ 1112015212363015 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4016 c22250R_130_5 (by norm_num)

theorem c22250R_130_3 : rowsJ2 130 131 32 360 ≤ 1123912639623904 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4015 c22250R_130_4 (by norm_num)

theorem c22250R_130_2 : rowsJ2 130 131 30 360 ≤ 1135646429319099 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4014 c22250R_130_3 (by norm_num)

theorem c22250R_130_1 : rowsJ2 130 131 27 360 ≤ 1146058991573396 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4013 c22250R_130_2 (by norm_num)

theorem c22250R_130_0 : rowsJ2 130 131 0 360 ≤ 1147724357556921 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22250R_4012 c22250R_130_1 (by norm_num)

theorem hr22250R_130 : rows2 130 131 ≤ 1147724357556921 := rows2_le_of_rowsJ2 130 131 c22250R_130_0

theorem c22250R_131_29 : rowsJ2 131 132 95 360 ≤ 927856117007355 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4073 rows22250R_4074 (by norm_num)

theorem c22250R_131_28 : rowsJ2 131 132 93 360 ≤ 939106525141309 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4072 c22250R_131_29 (by norm_num)

theorem c22250R_131_27 : rowsJ2 131 132 90 360 ≤ 948795163720351 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4071 c22250R_131_28 (by norm_num)

theorem c22250R_131_26 : rowsJ2 131 132 87 360 ≤ 951961352388886 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4070 c22250R_131_27 (by norm_num)

theorem c22250R_131_25 : rowsJ2 131 132 83 360 ≤ 952244555498024 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4069 c22250R_131_26 (by norm_num)

theorem c22250R_131_24 : rowsJ2 131 132 81 360 ≤ 953824358589985 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4068 c22250R_131_25 (by norm_num)

theorem c22250R_131_23 : rowsJ2 131 132 79 360 ≤ 956995876322792 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4067 c22250R_131_24 (by norm_num)

theorem c22250R_131_22 : rowsJ2 131 132 78 360 ≤ 959276835822056 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4066 c22250R_131_23 (by norm_num)

theorem c22250R_131_21 : rowsJ2 131 132 77 360 ≤ 962067776547346 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4065 c22250R_131_22 (by norm_num)

theorem c22250R_131_20 : rowsJ2 131 132 76 360 ≤ 965419306653455 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4064 c22250R_131_21 (by norm_num)

theorem c22250R_131_19 : rowsJ2 131 132 75 360 ≤ 969363841438230 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4063 c22250R_131_20 (by norm_num)

theorem c22250R_131_18 : rowsJ2 131 132 74 360 ≤ 973695277363677 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4062 c22250R_131_19 (by norm_num)

theorem c22250R_131_17 : rowsJ2 131 132 73 360 ≤ 978114251809353 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4061 c22250R_131_18 (by norm_num)

theorem c22250R_131_16 : rowsJ2 131 132 72 360 ≤ 982575248488663 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4060 c22250R_131_17 (by norm_num)

theorem c22250R_131_15 : rowsJ2 131 132 71 360 ≤ 987015186502189 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4059 c22250R_131_16 (by norm_num)

theorem c22250R_131_14 : rowsJ2 131 132 70 360 ≤ 991390780788817 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4058 c22250R_131_15 (by norm_num)

theorem c22250R_131_13 : rowsJ2 131 132 69 360 ≤ 995641133651177 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4057 c22250R_131_14 (by norm_num)

theorem c22250R_131_12 : rowsJ2 131 132 68 360 ≤ 999724707712453 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4056 c22250R_131_13 (by norm_num)

theorem c22250R_131_11 : rowsJ2 131 132 67 360 ≤ 1003582322317063 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4055 c22250R_131_12 (by norm_num)

theorem c22250R_131_10 : rowsJ2 131 132 66 360 ≤ 1007173759277343 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4054 c22250R_131_11 (by norm_num)

theorem c22250R_131_9 : rowsJ2 131 132 65 360 ≤ 1010441137727343 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4053 c22250R_131_10 (by norm_num)

theorem c22250R_131_8 : rowsJ2 131 132 64 360 ≤ 1013345173137635 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4052 c22250R_131_9 (by norm_num)

theorem c22250R_131_7 : rowsJ2 131 132 62 360 ≤ 1017889655768815 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4051 c22250R_131_8 (by norm_num)

theorem c22250R_131_6 : rowsJ2 131 132 59 360 ≤ 1021885477032325 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4050 c22250R_131_7 (by norm_num)

theorem c22250R_131_5 : rowsJ2 131 132 43 360 ≤ 1023610488434693 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4049 c22250R_131_6 (by norm_num)

theorem c22250R_131_4 : rowsJ2 131 132 36 360 ≤ 1028135789619813 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4048 c22250R_131_5 (by norm_num)

theorem c22250R_131_3 : rowsJ2 131 132 32 360 ≤ 1040062100410803 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4047 c22250R_131_4 (by norm_num)

theorem c22250R_131_2 : rowsJ2 131 132 29 360 ≤ 1055352702656973 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4046 c22250R_131_3 (by norm_num)

theorem c22250R_131_1 : rowsJ2 131 132 26 360 ≤ 1063274075214519 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4045 c22250R_131_2 (by norm_num)

theorem c22250R_131_0 : rowsJ2 131 132 0 360 ≤ 1063969399799740 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22250R_4044 c22250R_131_1 (by norm_num)

theorem hr22250R_131 : rows2 131 132 ≤ 1063969399799740 := rows2_le_of_rowsJ2 131 132 c22250R_131_0

theorem c22250R_132_30 : rowsJ2 132 133 94 360 ≤ 920773289051340 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4105 rows22250R_4106 (by norm_num)

theorem c22250R_132_29 : rowsJ2 132 133 92 360 ≤ 930477438074081 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4104 c22250R_132_30 (by norm_num)

theorem c22250R_132_28 : rowsJ2 132 133 89 360 ≤ 938203330638782 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4103 c22250R_132_29 (by norm_num)

theorem c22250R_132_27 : rowsJ2 132 133 85 360 ≤ 939827651232430 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4102 c22250R_132_28 (by norm_num)

theorem c22250R_132_26 : rowsJ2 132 133 82 360 ≤ 941501199135548 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4101 c22250R_132_27 (by norm_num)

theorem c22250R_132_25 : rowsJ2 132 133 80 360 ≤ 944361062032298 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4100 c22250R_132_26 (by norm_num)

theorem c22250R_132_24 : rowsJ2 132 133 79 360 ≤ 946424322075237 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4099 c22250R_132_25 (by norm_num)

theorem c22250R_132_23 : rowsJ2 132 133 78 360 ≤ 948968031475962 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4098 c22250R_132_24 (by norm_num)

theorem c22250R_132_22 : rowsJ2 132 133 77 360 ≤ 952022526693938 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4097 c22250R_132_23 (by norm_num)

theorem c22250R_132_21 : rowsJ2 132 133 76 360 ≤ 955638394634779 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4096 c22250R_132_22 (by norm_num)

theorem c22250R_132_20 : rowsJ2 132 133 75 360 ≤ 959848134284766 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4095 c22250R_132_21 (by norm_num)

theorem c22250R_132_19 : rowsJ2 132 133 74 360 ≤ 964704372749493 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4094 c22250R_132_20 (by norm_num)

theorem c22250R_132_18 : rowsJ2 132 133 73 360 ≤ 969623124008879 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4093 c22250R_132_19 (by norm_num)

theorem c22250R_132_17 : rowsJ2 132 133 72 360 ≤ 974559188905533 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4092 c22250R_132_18 (by norm_num)

theorem c22250R_132_16 : rowsJ2 132 133 71 360 ≤ 979449884109499 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4091 c22250R_132_17 (by norm_num)

theorem c22250R_132_15 : rowsJ2 132 133 70 360 ≤ 984252197299239 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4090 c22250R_132_16 (by norm_num)

theorem c22250R_132_14 : rowsJ2 132 133 69 360 ≤ 988905584654007 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4089 c22250R_132_15 (by norm_num)

theorem c22250R_132_13 : rowsJ2 132 133 68 360 ≤ 993368740601334 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4088 c22250R_132_14 (by norm_num)

theorem c22250R_132_12 : rowsJ2 132 133 67 360 ≤ 997582797889141 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4087 c22250R_132_13 (by norm_num)

theorem c22250R_132_11 : rowsJ2 132 133 66 360 ≤ 1001507732076443 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4086 c22250R_132_12 (by norm_num)

theorem c22250R_132_10 : rowsJ2 132 133 65 360 ≤ 1005085937912234 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4085 c22250R_132_11 (by norm_num)

theorem c22250R_132_9 : rowsJ2 132 133 64 360 ≤ 1008278288938137 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4084 c22250R_132_10 (by norm_num)

theorem c22250R_132_8 : rowsJ2 132 133 63 360 ≤ 1011028064877638 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4083 c22250R_132_9 (by norm_num)

theorem c22250R_132_7 : rowsJ2 132 133 62 360 ≤ 1013332513820487 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4082 c22250R_132_8 (by norm_num)

theorem c22250R_132_6 : rowsJ2 132 133 59 360 ≤ 1017922307664677 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4081 c22250R_132_7 (by norm_num)

theorem c22250R_132_5 : rowsJ2 132 133 45 360 ≤ 1020184634225734 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4080 c22250R_132_6 (by norm_num)

theorem c22250R_132_4 : rowsJ2 132 133 36 360 ≤ 1023465920541095 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4079 c22250R_132_5 (by norm_num)

theorem c22250R_132_3 : rowsJ2 132 133 32 360 ≤ 1033036721591686 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4078 c22250R_132_4 (by norm_num)

theorem c22250R_132_2 : rowsJ2 132 133 29 360 ≤ 1047368033325934 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4077 c22250R_132_3 (by norm_num)

theorem c22250R_132_1 : rowsJ2 132 133 26 360 ≤ 1056193024995274 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4076 c22250R_132_2 (by norm_num)

theorem c22250R_132_0 : rowsJ2 132 133 0 360 ≤ 1057297965769775 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22250R_4075 c22250R_132_1 (by norm_num)

theorem hr22250R_132 : rows2 132 133 ≤ 1057297965769775 := rows2_le_of_rowsJ2 132 133 c22250R_132_0

theorem c22250R_133_31 : rowsJ2 133 134 95 360 ≤ 826982999666934 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4138 rows22250R_4139 (by norm_num)

theorem c22250R_133_30 : rowsJ2 133 134 93 360 ≤ 839462020610057 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4137 c22250R_133_31 (by norm_num)

theorem c22250R_133_29 : rowsJ2 133 134 90 360 ≤ 850285261574427 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4136 c22250R_133_30 (by norm_num)

theorem c22250R_133_28 : rowsJ2 133 134 87 360 ≤ 853865367522575 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4135 c22250R_133_29 (by norm_num)

theorem c22250R_133_27 : rowsJ2 133 134 84 360 ≤ 854553995569596 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4134 c22250R_133_28 (by norm_num)

theorem c22250R_133_26 : rowsJ2 133 134 82 360 ≤ 856400386589128 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4133 c22250R_133_27 (by norm_num)

theorem c22250R_133_25 : rowsJ2 133 134 80 360 ≤ 859694005335267 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4132 c22250R_133_26 (by norm_num)

theorem c22250R_133_24 : rowsJ2 133 134 79 360 ≤ 861975030590094 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4131 c22250R_133_25 (by norm_num)

theorem c22250R_133_23 : rowsJ2 133 134 78 360 ≤ 864737103866575 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4130 c22250R_133_24 (by norm_num)

theorem c22250R_133_22 : rowsJ2 133 134 77 360 ≤ 868010645054945 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4129 c22250R_133_23 (by norm_num)

theorem c22250R_133_21 : rowsJ2 133 134 76 360 ≤ 871846218184726 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4128 c22250R_133_22 (by norm_num)

theorem c22250R_133_20 : rowsJ2 133 134 75 360 ≤ 876276403115619 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4127 c22250R_133_21 (by norm_num)

theorem c22250R_133_19 : rowsJ2 133 134 74 360 ≤ 881353802853609 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4126 c22250R_133_20 (by norm_num)

theorem c22250R_133_18 : rowsJ2 133 134 73 360 ≤ 886778390348163 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4125 c22250R_133_19 (by norm_num)

theorem c22250R_133_17 : rowsJ2 133 134 72 360 ≤ 892195243749576 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4124 c22250R_133_18 (by norm_num)

theorem c22250R_133_16 : rowsJ2 133 134 71 360 ≤ 897542082499487 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4123 c22250R_133_17 (by norm_num)

theorem c22250R_133_15 : rowsJ2 133 134 70 360 ≤ 902776172936691 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4122 c22250R_133_16 (by norm_num)

theorem c22250R_133_14 : rowsJ2 133 134 69 360 ≤ 907837329530252 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4121 c22250R_133_15 (by norm_num)

theorem c22250R_133_13 : rowsJ2 133 134 68 360 ≤ 912684483666147 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4120 c22250R_133_14 (by norm_num)

theorem c22250R_133_12 : rowsJ2 133 134 67 360 ≤ 917259085185634 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4119 c22250R_133_13 (by norm_num)

theorem c22250R_133_11 : rowsJ2 133 134 66 360 ≤ 921521307843262 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4118 c22250R_133_12 (by norm_num)

theorem c22250R_133_10 : rowsJ2 133 134 65 360 ≤ 925413825025379 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4117 c22250R_133_11 (by norm_num)

theorem c22250R_133_9 : rowsJ2 133 134 64 360 ≤ 928897672140335 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4116 c22250R_133_10 (by norm_num)

theorem c22250R_133_8 : rowsJ2 133 134 63 360 ≤ 931916371362005 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4115 c22250R_133_9 (by norm_num)

theorem c22250R_133_7 : rowsJ2 133 134 62 360 ≤ 934467102320822 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4114 c22250R_133_8 (by norm_num)

theorem c22250R_133_6 : rowsJ2 133 134 60 360 ≤ 938301372840717 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4113 c22250R_133_7 (by norm_num)

theorem c22250R_133_5 : rowsJ2 133 134 55 360 ≤ 942251791785585 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4112 c22250R_133_6 (by norm_num)

theorem c22250R_133_4 : rowsJ2 133 134 37 360 ≤ 943727907259243 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4111 c22250R_133_5 (by norm_num)

theorem c22250R_133_3 : rowsJ2 133 134 32 360 ≤ 952200540482629 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4110 c22250R_133_4 (by norm_num)

theorem c22250R_133_2 : rowsJ2 133 134 29 360 ≤ 964343366119336 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4109 c22250R_133_3 (by norm_num)

theorem c22250R_133_1 : rowsJ2 133 134 26 360 ≤ 974075858542938 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4108 c22250R_133_2 (by norm_num)

theorem c22250R_133_0 : rowsJ2 133 134 0 360 ≤ 975700673756980 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22250R_4107 c22250R_133_1 (by norm_num)

theorem hr22250R_133 : rows2 133 134 ≤ 975700673756980 := rows2_le_of_rowsJ2 133 134 c22250R_133_0

theorem c22250R_134_30 : rowsJ2 134 135 93 360 ≤ 827102173235611 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4170 rows22250R_4171 (by norm_num)

theorem c22250R_134_29 : rowsJ2 134 135 90 360 ≤ 838546110255621 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4169 c22250R_134_30 (by norm_num)

theorem c22250R_134_28 : rowsJ2 134 135 86 360 ≤ 842581074156301 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4168 c22250R_134_29 (by norm_num)

theorem c22250R_134_27 : rowsJ2 134 135 83 360 ≤ 844604992858940 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4167 c22250R_134_28 (by norm_num)

theorem c22250R_134_26 : rowsJ2 134 135 81 360 ≤ 847525442186735 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4166 c22250R_134_27 (by norm_num)

theorem c22250R_134_25 : rowsJ2 134 135 80 360 ≤ 849568733057894 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4165 c22250R_134_26 (by norm_num)

theorem c22250R_134_24 : rowsJ2 134 135 79 360 ≤ 852044990608678 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4164 c22250R_134_25 (by norm_num)

theorem c22250R_134_23 : rowsJ2 134 135 78 360 ≤ 855002944306475 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4163 c22250R_134_24 (by norm_num)

theorem c22250R_134_22 : rowsJ2 134 135 77 360 ≤ 858473097376207 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4162 c22250R_134_23 (by norm_num)

theorem c22250R_134_21 : rowsJ2 134 135 76 360 ≤ 862505992054265 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4161 c22250R_134_22 (by norm_num)

theorem c22250R_134_20 : rowsJ2 134 135 75 360 ≤ 867134289052991 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4160 c22250R_134_21 (by norm_num)

theorem c22250R_134_19 : rowsJ2 134 135 74 360 ≤ 872410568428592 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4159 c22250R_134_20 (by norm_num)

theorem c22250R_134_18 : rowsJ2 134 135 73 360 ≤ 878369871385276 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4158 c22250R_134_19 (by norm_num)

theorem c22250R_134_17 : rowsJ2 134 135 72 360 ≤ 884296220926850 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4157 c22250R_134_18 (by norm_num)

theorem c22250R_134_16 : rowsJ2 134 135 71 360 ≤ 890127748111378 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4156 c22250R_134_17 (by norm_num)

theorem c22250R_134_15 : rowsJ2 134 135 70 360 ≤ 895822007525172 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4155 c22250R_134_16 (by norm_num)

theorem c22250R_134_14 : rowsJ2 134 135 69 360 ≤ 901319180072089 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4154 c22250R_134_15 (by norm_num)

theorem c22250R_134_13 : rowsJ2 134 135 68 360 ≤ 906578443015924 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4153 c22250R_134_14 (by norm_num)

theorem c22250R_134_12 : rowsJ2 134 135 67 360 ≤ 911541570820877 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4152 c22250R_134_13 (by norm_num)

theorem c22250R_134_11 : rowsJ2 134 135 66 360 ≤ 916168943768559 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4151 c22250R_134_12 (by norm_num)

theorem c22250R_134_10 : rowsJ2 134 135 65 360 ≤ 920403520871327 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4150 c22250R_134_11 (by norm_num)

theorem c22250R_134_9 : rowsJ2 134 135 64 360 ≤ 924206507218584 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4149 c22250R_134_10 (by norm_num)

theorem c22250R_134_8 : rowsJ2 134 135 63 360 ≤ 927521673948163 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4148 c22250R_134_9 (by norm_num)

theorem c22250R_134_7 : rowsJ2 134 135 62 360 ≤ 930346141723625 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4147 c22250R_134_8 (by norm_num)

theorem c22250R_134_6 : rowsJ2 134 135 60 360 ≤ 934658572573654 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4146 c22250R_134_7 (by norm_num)

theorem c22250R_134_5 : rowsJ2 134 135 57 360 ≤ 938333134123585 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4145 c22250R_134_6 (by norm_num)

theorem c22250R_134_4 : rowsJ2 134 135 40 360 ≤ 939755133229651 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4144 c22250R_134_5 (by norm_num)

theorem c22250R_134_3 : rowsJ2 134 135 33 360 ≤ 944909779094795 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4143 c22250R_134_4 (by norm_num)

theorem c22250R_134_2 : rowsJ2 134 135 29 360 ≤ 957081297689198 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4142 c22250R_134_3 (by norm_num)

theorem c22250R_134_1 : rowsJ2 134 135 26 360 ≤ 967724453871308 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4141 c22250R_134_2 (by norm_num)

theorem c22250R_134_0 : rowsJ2 134 135 0 360 ≤ 969977596429808 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22250R_4140 c22250R_134_1 (by norm_num)

theorem hr22250R_134 : rows2 134 135 ≤ 969977596429808 := rows2_le_of_rowsJ2 134 135 c22250R_134_0

theorem c22250R_135_31 : rowsJ2 135 136 94 360 ≤ 735773984427629 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4203 rows22250R_4204 (by norm_num)

theorem c22250R_135_30 : rowsJ2 135 136 91 360 ≤ 751067562549984 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4202 c22250R_135_31 (by norm_num)

theorem c22250R_135_29 : rowsJ2 135 136 88 360 ≤ 757490254276270 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4201 c22250R_135_30 (by norm_num)

theorem c22250R_135_28 : rowsJ2 135 136 85 360 ≤ 759138443944624 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4200 c22250R_135_29 (by norm_num)

theorem c22250R_135_27 : rowsJ2 135 136 83 360 ≤ 761054729552607 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4199 c22250R_135_28 (by norm_num)

theorem c22250R_135_26 : rowsJ2 135 136 81 360 ≤ 764275884099140 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4198 c22250R_135_27 (by norm_num)

theorem c22250R_135_25 : rowsJ2 135 136 80 360 ≤ 766470244095136 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4197 c22250R_135_26 (by norm_num)

theorem c22250R_135_24 : rowsJ2 135 136 79 360 ≤ 769098124881118 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4196 c22250R_135_25 (by norm_num)

theorem c22250R_135_23 : rowsJ2 135 136 78 360 ≤ 772208233827163 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4195 c22250R_135_24 (by norm_num)

theorem c22250R_135_22 : rowsJ2 135 136 77 360 ≤ 775831154779176 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4194 c22250R_135_23 (by norm_num)

theorem c22250R_135_21 : rowsJ2 135 136 76 360 ≤ 780017406564621 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4193 c22250R_135_22 (by norm_num)

theorem c22250R_135_20 : rowsJ2 135 136 75 360 ≤ 784799727983060 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4192 c22250R_135_21 (by norm_num)

theorem c22250R_135_19 : rowsJ2 135 136 74 360 ≤ 790230674461107 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4191 c22250R_135_20 (by norm_num)

theorem c22250R_135_18 : rowsJ2 135 136 73 360 ≤ 796345362905111 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4190 c22250R_135_19 (by norm_num)

theorem c22250R_135_17 : rowsJ2 135 136 72 360 ≤ 802787684028474 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4189 c22250R_135_18 (by norm_num)

theorem c22250R_135_16 : rowsJ2 135 136 71 360 ≤ 809110008348356 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4188 c22250R_135_17 (by norm_num)

theorem c22250R_135_15 : rowsJ2 135 136 70 360 ≤ 815270185735668 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4187 c22250R_135_16 (by norm_num)

theorem c22250R_135_14 : rowsJ2 135 136 69 360 ≤ 821208769028466 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4186 c22250R_135_15 (by norm_num)

theorem c22250R_135_13 : rowsJ2 135 136 68 360 ≤ 826885187510809 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4185 c22250R_135_14 (by norm_num)

theorem c22250R_135_12 : rowsJ2 135 136 67 360 ≤ 832241544925645 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4184 c22250R_135_13 (by norm_num)

theorem c22250R_135_11 : rowsJ2 135 136 66 360 ≤ 837238433406325 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4183 c22250R_135_12 (by norm_num)

theorem c22250R_135_10 : rowsJ2 135 136 65 360 ≤ 841819101473642 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4182 c22250R_135_11 (by norm_num)

theorem c22250R_135_9 : rowsJ2 135 136 64 360 ≤ 845944928470295 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4181 c22250R_135_10 (by norm_num)

theorem c22250R_135_8 : rowsJ2 135 136 63 360 ≤ 849559937666596 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4180 c22250R_135_9 (by norm_num)

theorem c22250R_135_7 : rowsJ2 135 136 62 360 ≤ 852661196732337 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4179 c22250R_135_8 (by norm_num)

theorem c22250R_135_6 : rowsJ2 135 136 60 360 ≤ 857456966333394 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4178 c22250R_135_7 (by norm_num)

theorem c22250R_135_5 : rowsJ2 135 136 58 360 ≤ 860615543620216 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4177 c22250R_135_6 (by norm_num)

theorem c22250R_135_4 : rowsJ2 135 136 42 360 ≤ 863499210665315 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4176 c22250R_135_5 (by norm_num)

theorem c22250R_135_3 : rowsJ2 135 136 33 360 ≤ 867064071380692 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4175 c22250R_135_4 (by norm_num)

theorem c22250R_135_2 : rowsJ2 135 136 29 360 ≤ 876832626686480 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4174 c22250R_135_3 (by norm_num)

theorem c22250R_135_1 : rowsJ2 135 136 26 360 ≤ 887280060021759 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4173 c22250R_135_2 (by norm_num)

theorem c22250R_135_0 : rowsJ2 135 136 0 360 ≤ 890168065631275 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22250R_4172 c22250R_135_1 (by norm_num)

theorem hr22250R_135 : rows2 135 136 ≤ 890168065631275 := rows2_le_of_rowsJ2 135 136 c22250R_135_0

theorem c22250R_136_30 : rowsJ2 136 137 91 360 ≤ 739830387517867 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4235 rows22250R_4236 (by norm_num)

theorem c22250R_136_29 : rowsJ2 136 137 88 360 ≤ 746765440814931 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4234 c22250R_136_30 (by norm_num)

theorem c22250R_136_28 : rowsJ2 136 137 85 360 ≤ 748854417020784 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4233 c22250R_136_29 (by norm_num)

theorem c22250R_136_27 : rowsJ2 136 137 83 360 ≤ 751026124377117 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4232 c22250R_136_28 (by norm_num)

theorem c22250R_136_26 : rowsJ2 136 137 81 360 ≤ 754504642927180 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4231 c22250R_136_27 (by norm_num)

theorem c22250R_136_25 : rowsJ2 136 137 80 360 ≤ 756828483678709 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4230 c22250R_136_26 (by norm_num)

theorem c22250R_136_24 : rowsJ2 136 137 79 360 ≤ 759586454425568 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4229 c22250R_136_25 (by norm_num)

theorem c22250R_136_23 : rowsJ2 136 137 78 360 ≤ 762827241519681 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4228 c22250R_136_24 (by norm_num)

theorem c22250R_136_22 : rowsJ2 136 137 77 360 ≤ 766581509422841 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4227 c22250R_136_23 (by norm_num)

theorem c22250R_136_21 : rowsJ2 136 137 76 360 ≤ 770899754692866 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4226 c22250R_136_22 (by norm_num)

theorem c22250R_136_20 : rowsJ2 136 137 75 360 ≤ 775814794290880 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4225 c22250R_136_21 (by norm_num)

theorem c22250R_136_19 : rowsJ2 136 137 74 360 ≤ 781379160224829 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4224 c22250R_136_20 (by norm_num)

theorem c22250R_136_18 : rowsJ2 136 137 73 360 ≤ 787628045268146 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4223 c22250R_136_19 (by norm_num)

theorem c22250R_136_17 : rowsJ2 136 137 72 360 ≤ 794616263668400 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4222 c22250R_136_18 (by norm_num)

theorem c22250R_136_16 : rowsJ2 136 137 71 360 ≤ 801459117356186 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4221 c22250R_136_17 (by norm_num)

theorem c22250R_136_15 : rowsJ2 136 137 70 360 ≤ 808114762322864 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4220 c22250R_136_16 (by norm_num)

theorem c22250R_136_14 : rowsJ2 136 137 69 360 ≤ 814524132699945 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4219 c22250R_136_15 (by norm_num)

theorem c22250R_136_13 : rowsJ2 136 137 68 360 ≤ 820646919825434 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4218 c22250R_136_14 (by norm_num)

theorem c22250R_136_12 : rowsJ2 136 137 67 360 ≤ 826425565339128 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4217 c22250R_136_13 (by norm_num)

theorem c22250R_136_11 : rowsJ2 136 137 66 360 ≤ 831820882554657 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4216 c22250R_136_12 (by norm_num)

theorem c22250R_136_10 : rowsJ2 136 137 65 360 ≤ 836776417468449 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4215 c22250R_136_11 (by norm_num)

theorem c22250R_136_9 : rowsJ2 136 137 64 360 ≤ 841253732385136 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4214 c22250R_136_10 (by norm_num)

theorem c22250R_136_8 : rowsJ2 136 137 63 360 ≤ 845197110103046 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4213 c22250R_136_9 (by norm_num)

theorem c22250R_136_7 : rowsJ2 136 137 62 360 ≤ 848603575526233 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4212 c22250R_136_8 (by norm_num)

theorem c22250R_136_6 : rowsJ2 136 137 60 360 ≤ 853939229281974 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4211 c22250R_136_7 (by norm_num)

theorem c22250R_136_5 : rowsJ2 136 137 58 360 ≤ 857541670386290 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4210 c22250R_136_6 (by norm_num)

theorem c22250R_136_4 : rowsJ2 136 137 53 360 ≤ 861041278445148 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4209 c22250R_136_5 (by norm_num)

theorem c22250R_136_3 : rowsJ2 136 137 34 360 ≤ 862580955301532 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4208 c22250R_136_4 (by norm_num)

theorem c22250R_136_2 : rowsJ2 136 137 29 360 ≤ 871228333399271 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4207 c22250R_136_3 (by norm_num)

theorem c22250R_136_1 : rowsJ2 136 137 25 360 ≤ 883506870516176 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4206 c22250R_136_2 (by norm_num)

theorem c22250R_136_0 : rowsJ2 136 137 0 360 ≤ 885083736333576 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22250R_4205 c22250R_136_1 (by norm_num)

theorem hr22250R_136 : rows2 136 137 ≤ 885083736333576 := rows2_le_of_rowsJ2 136 137 c22250R_136_0

theorem c22250R_137_30 : rowsJ2 137 138 91 360 ≤ 657331563555949 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4267 rows22250R_4268 (by norm_num)

theorem c22250R_137_29 : rowsJ2 137 138 88 360 ≤ 664790941139315 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4266 c22250R_137_30 (by norm_num)

theorem c22250R_137_28 : rowsJ2 137 138 85 360 ≤ 667148678250586 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4265 c22250R_137_29 (by norm_num)

theorem c22250R_137_27 : rowsJ2 137 138 83 360 ≤ 669490631170786 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4264 c22250R_137_28 (by norm_num)

theorem c22250R_137_26 : rowsJ2 137 138 81 360 ≤ 673140918908921 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4263 c22250R_137_27 (by norm_num)

theorem c22250R_137_25 : rowsJ2 137 138 80 360 ≤ 675551281119390 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4262 c22250R_137_26 (by norm_num)

theorem c22250R_137_24 : rowsJ2 137 138 79 360 ≤ 678396271484459 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4261 c22250R_137_25 (by norm_num)

theorem c22250R_137_23 : rowsJ2 137 138 78 360 ≤ 681724553787059 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4260 c22250R_137_24 (by norm_num)

theorem c22250R_137_22 : rowsJ2 137 138 77 360 ≤ 685566870425984 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4259 c22250R_137_23 (by norm_num)

theorem c22250R_137_21 : rowsJ2 137 138 76 360 ≤ 689973694073359 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4258 c22250R_137_22 (by norm_num)

theorem c22250R_137_20 : rowsJ2 137 138 75 360 ≤ 694977917123063 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4257 c22250R_137_21 (by norm_num)

theorem c22250R_137_19 : rowsJ2 137 138 74 360 ≤ 700632046486572 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4256 c22250R_137_20 (by norm_num)

theorem c22250R_137_18 : rowsJ2 137 138 73 360 ≤ 706971348028205 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4255 c22250R_137_19 (by norm_num)

theorem c22250R_137_17 : rowsJ2 137 138 72 360 ≤ 714050609775442 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4254 c22250R_137_18 (by norm_num)

theorem c22250R_137_16 : rowsJ2 137 138 71 360 ≤ 721420897699079 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4253 c22250R_137_17 (by norm_num)

theorem c22250R_137_15 : rowsJ2 137 138 70 360 ≤ 728578520911202 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4252 c22250R_137_16 (by norm_num)

theorem c22250R_137_14 : rowsJ2 137 138 69 360 ≤ 735464801563743 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4251 c22250R_137_15 (by norm_num)

theorem c22250R_137_13 : rowsJ2 137 138 68 360 ≤ 742039700312771 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4250 c22250R_137_14 (by norm_num)

theorem c22250R_137_12 : rowsJ2 137 138 67 360 ≤ 748246002439884 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4249 c22250R_137_13 (by norm_num)

theorem c22250R_137_11 : rowsJ2 137 138 66 360 ≤ 754044748756136 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4248 c22250R_137_12 (by norm_num)

theorem c22250R_137_10 : rowsJ2 137 138 65 360 ≤ 759379787583734 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4247 c22250R_137_11 (by norm_num)

theorem c22250R_137_9 : rowsJ2 137 138 64 360 ≤ 764212869640308 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4246 c22250R_137_10 (by norm_num)

theorem c22250R_137_8 : rowsJ2 137 138 63 360 ≤ 768488541281392 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4245 c22250R_137_9 (by norm_num)

theorem c22250R_137_7 : rowsJ2 137 138 62 360 ≤ 772203791329851 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4244 c22250R_137_8 (by norm_num)

theorem c22250R_137_6 : rowsJ2 137 138 61 360 ≤ 775391401387738 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4243 c22250R_137_7 (by norm_num)

theorem c22250R_137_5 : rowsJ2 137 138 59 360 ≤ 780321543848845 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4242 c22250R_137_6 (by norm_num)

theorem c22250R_137_4 : rowsJ2 137 138 55 360 ≤ 785451460794321 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4241 c22250R_137_5 (by norm_num)

theorem c22250R_137_3 : rowsJ2 137 138 35 360 ≤ 786868709389517 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4240 c22250R_137_4 (by norm_num)

theorem c22250R_137_2 : rowsJ2 137 138 29 360 ≤ 793932319125279 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4239 c22250R_137_3 (by norm_num)

theorem c22250R_137_1 : rowsJ2 137 138 25 360 ≤ 805228704571487 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4238 c22250R_137_2 (by norm_num)

theorem c22250R_137_0 : rowsJ2 137 138 0 360 ≤ 807346991746320 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22250R_4237 c22250R_137_1 (by norm_num)

theorem hr22250R_137 : rows2 137 138 ≤ 807346991746320 := rows2_le_of_rowsJ2 137 138 c22250R_137_0

theorem c22250R_138_30 : rowsJ2 138 139 91 360 ≤ 648510075569821 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4299 rows22250R_4300 (by norm_num)

theorem c22250R_138_29 : rowsJ2 138 139 88 360 ≤ 656573335539454 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4298 c22250R_138_30 (by norm_num)

theorem c22250R_138_28 : rowsJ2 138 139 85 360 ≤ 659185296798281 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4297 c22250R_138_29 (by norm_num)

theorem c22250R_138_27 : rowsJ2 138 139 83 360 ≤ 661655679769763 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4296 c22250R_138_28 (by norm_num)

theorem c22250R_138_26 : rowsJ2 138 139 81 360 ≤ 665436163288699 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4295 c22250R_138_27 (by norm_num)

theorem c22250R_138_25 : rowsJ2 138 139 80 360 ≤ 667912352429557 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4294 c22250R_138_26 (by norm_num)

theorem c22250R_138_24 : rowsJ2 138 139 79 360 ≤ 670823729692540 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4293 c22250R_138_25 (by norm_num)

theorem c22250R_138_23 : rowsJ2 138 139 78 360 ≤ 674218937413176 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4292 c22250R_138_24 (by norm_num)

theorem c22250R_138_22 : rowsJ2 138 139 77 360 ≤ 678128796002198 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4291 c22250R_138_23 (by norm_num)

theorem c22250R_138_21 : rowsJ2 138 139 76 360 ≤ 682603755432305 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4290 c22250R_138_22 (by norm_num)

theorem c22250R_138_20 : rowsJ2 138 139 75 360 ≤ 687676783688798 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4289 c22250R_138_21 (by norm_num)

theorem c22250R_138_19 : rowsJ2 138 139 74 360 ≤ 693400363849487 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4288 c22250R_138_20 (by norm_num)

theorem c22250R_138_18 : rowsJ2 138 139 73 360 ≤ 699809835123510 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4287 c22250R_138_19 (by norm_num)

theorem c22250R_138_17 : rowsJ2 138 139 72 360 ≤ 706959960670044 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4286 c22250R_138_18 (by norm_num)

theorem c22250R_138_16 : rowsJ2 138 139 71 360 ≤ 714888697908405 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4285 c22250R_138_17 (by norm_num)

theorem c22250R_138_15 : rowsJ2 138 139 70 360 ≤ 722579099499305 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4284 c22250R_138_16 (by norm_num)

theorem c22250R_138_14 : rowsJ2 138 139 69 360 ≤ 729972886344336 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4283 c22250R_138_15 (by norm_num)

theorem c22250R_138_13 : rowsJ2 138 139 68 360 ≤ 737030299712347 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4282 c22250R_138_14 (by norm_num)

theorem c22250R_138_12 : rowsJ2 138 139 67 360 ≤ 743694478369286 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4281 c22250R_138_13 (by norm_num)

theorem c22250R_138_11 : rowsJ2 138 139 66 360 ≤ 749926701077813 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4280 c22250R_138_12 (by norm_num)

theorem c22250R_138_10 : rowsJ2 138 139 65 360 ≤ 755671127550724 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4279 c22250R_138_11 (by norm_num)

theorem c22250R_138_9 : rowsJ2 138 139 64 360 ≤ 760889706634749 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4278 c22250R_138_10 (by norm_num)

theorem c22250R_138_8 : rowsJ2 138 139 63 360 ≤ 765527256624948 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4277 c22250R_138_9 (by norm_num)

theorem c22250R_138_7 : rowsJ2 138 139 62 360 ≤ 769580741329383 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4276 c22250R_138_8 (by norm_num)

theorem c22250R_138_6 : rowsJ2 138 139 61 360 ≤ 773082709093279 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4275 c22250R_138_7 (by norm_num)

theorem c22250R_138_5 : rowsJ2 138 139 59 360 ≤ 778568879139031 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4274 c22250R_138_6 (by norm_num)

theorem c22250R_138_4 : rowsJ2 138 139 56 360 ≤ 783555305085858 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4273 c22250R_138_5 (by norm_num)

theorem c22250R_138_3 : rowsJ2 138 139 36 360 ≤ 786016471000204 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4272 c22250R_138_4 (by norm_num)

theorem c22250R_138_2 : rowsJ2 138 139 29 360 ≤ 791312301179032 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4271 c22250R_138_3 (by norm_num)

theorem c22250R_138_1 : rowsJ2 138 139 25 360 ≤ 801900940497916 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4270 c22250R_138_2 (by norm_num)

theorem c22250R_138_0 : rowsJ2 138 139 0 360 ≤ 804453503790972 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22250R_4269 c22250R_138_1 (by norm_num)

theorem hr22250R_138 : rows2 138 139 ≤ 804453503790972 := rows2_le_of_rowsJ2 138 139 c22250R_138_0

theorem c22250R_139_31 : rowsJ2 139 140 91 360 ≤ 568140973124534 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4332 rows22250R_4333 (by norm_num)

theorem c22250R_139_30 : rowsJ2 139 140 88 360 ≤ 576653827278410 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4331 c22250R_139_31 (by norm_num)

theorem c22250R_139_29 : rowsJ2 139 140 85 360 ≤ 579348000761419 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4330 c22250R_139_30 (by norm_num)

theorem c22250R_139_28 : rowsJ2 139 140 83 360 ≤ 581862457460364 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4329 c22250R_139_29 (by norm_num)

theorem c22250R_139_27 : rowsJ2 139 140 81 360 ≤ 585688375598018 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4328 c22250R_139_28 (by norm_num)

theorem c22250R_139_26 : rowsJ2 139 140 80 360 ≤ 588187854369873 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4327 c22250R_139_27 (by norm_num)

theorem c22250R_139_25 : rowsJ2 139 140 79 360 ≤ 591122973647051 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4326 c22250R_139_26 (by norm_num)

theorem c22250R_139_24 : rowsJ2 139 140 78 360 ≤ 594542352752848 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4325 c22250R_139_25 (by norm_num)

theorem c22250R_139_23 : rowsJ2 139 140 77 360 ≤ 598476887452808 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4324 c22250R_139_24 (by norm_num)

theorem c22250R_139_22 : rowsJ2 139 140 76 360 ≤ 602977003392422 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4323 c22250R_139_23 (by norm_num)

theorem c22250R_139_21 : rowsJ2 139 140 75 360 ≤ 608075741443154 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4322 c22250R_139_22 (by norm_num)

theorem c22250R_139_20 : rowsJ2 139 140 74 360 ≤ 613825559161984 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4321 c22250R_139_21 (by norm_num)

theorem c22250R_139_19 : rowsJ2 139 140 73 360 ≤ 620261866352271 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4320 c22250R_139_20 (by norm_num)

theorem c22250R_139_18 : rowsJ2 139 140 72 360 ≤ 627439399561803 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4319 c22250R_139_19 (by norm_num)

theorem c22250R_139_17 : rowsJ2 139 140 71 360 ≤ 635396184669618 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4318 c22250R_139_18 (by norm_num)

theorem c22250R_139_16 : rowsJ2 139 140 70 360 ≤ 643626715625260 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4317 c22250R_139_17 (by norm_num)

theorem c22250R_139_15 : rowsJ2 139 140 69 360 ≤ 651534935859538 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4316 c22250R_139_16 (by norm_num)

theorem c22250R_139_14 : rowsJ2 139 140 68 360 ≤ 659081375796009 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4315 c22250R_139_15 (by norm_num)

theorem c22250R_139_13 : rowsJ2 139 140 67 360 ≤ 666209534663358 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4314 c22250R_139_14 (by norm_num)

theorem c22250R_139_12 : rowsJ2 139 140 66 360 ≤ 672880936621541 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4313 c22250R_139_13 (by norm_num)

theorem c22250R_139_11 : rowsJ2 139 140 65 360 ≤ 679040058717577 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4312 c22250R_139_12 (by norm_num)

theorem c22250R_139_10 : rowsJ2 139 140 64 360 ≤ 684649054376264 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4311 c22250R_139_11 (by norm_num)

theorem c22250R_139_9 : rowsJ2 139 140 63 360 ≤ 689653018831977 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4310 c22250R_139_10 (by norm_num)

theorem c22250R_139_8 : rowsJ2 139 140 62 360 ≤ 694048898381152 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4309 c22250R_139_9 (by norm_num)

theorem c22250R_139_7 : rowsJ2 139 140 61 360 ≤ 697869017201765 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4308 c22250R_139_8 (by norm_num)

theorem c22250R_139_6 : rowsJ2 139 140 60 360 ≤ 701146974349264 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4307 c22250R_139_7 (by norm_num)

theorem c22250R_139_5 : rowsJ2 139 140 58 360 ≤ 706217731119615 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4306 c22250R_139_6 (by norm_num)

theorem c22250R_139_4 : rowsJ2 139 140 56 360 ≤ 709559084723372 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4305 c22250R_139_5 (by norm_num)

theorem c22250R_139_3 : rowsJ2 139 140 38 360 ≤ 712611999011644 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4304 c22250R_139_4 (by norm_num)

theorem c22250R_139_2 : rowsJ2 139 140 29 360 ≤ 716275459314928 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4303 c22250R_139_3 (by norm_num)

theorem c22250R_139_1 : rowsJ2 139 140 25 360 ≤ 725349607229264 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4302 c22250R_139_2 (by norm_num)

theorem c22250R_139_0 : rowsJ2 139 140 0 360 ≤ 728339727519894 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22250R_4301 c22250R_139_1 (by norm_num)

theorem hr22250R_139 : rows2 139 140 ≤ 728339727519894 := rows2_le_of_rowsJ2 139 140 c22250R_139_0

theorem c22250R_140_30 : rowsJ2 140 141 88 360 ≤ 570732088537464 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4364 rows22250R_4365 (by norm_num)

theorem c22250R_140_29 : rowsJ2 140 141 85 360 ≤ 573497765967531 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4363 c22250R_140_30 (by norm_num)

theorem c22250R_140_28 : rowsJ2 140 141 83 360 ≤ 576016034422071 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4362 c22250R_140_29 (by norm_num)

theorem c22250R_140_27 : rowsJ2 140 141 81 360 ≤ 579847393980254 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4361 c22250R_140_28 (by norm_num)

theorem c22250R_140_26 : rowsJ2 140 141 80 360 ≤ 582350268065498 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4360 c22250R_140_27 (by norm_num)

theorem c22250R_140_25 : rowsJ2 140 141 79 360 ≤ 585289303659325 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4359 c22250R_140_26 (by norm_num)

theorem c22250R_140_24 : rowsJ2 140 141 78 360 ≤ 588713098227112 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4358 c22250R_140_25 (by norm_num)

theorem c22250R_140_23 : rowsJ2 140 141 77 360 ≤ 592652623033103 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4357 c22250R_140_24 (by norm_num)

theorem c22250R_140_22 : rowsJ2 140 141 76 360 ≤ 597158280619366 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4356 c22250R_140_23 (by norm_num)

theorem c22250R_140_21 : rowsJ2 140 141 75 360 ≤ 602263184975785 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4355 c22250R_140_22 (by norm_num)

theorem c22250R_140_20 : rowsJ2 140 141 74 360 ≤ 608019769443919 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4354 c22250R_140_21 (by norm_num)

theorem c22250R_140_19 : rowsJ2 140 141 73 360 ≤ 614463514753653 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4353 c22250R_140_20 (by norm_num)

theorem c22250R_140_18 : rowsJ2 140 141 72 360 ≤ 621649132241247 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4352 c22250R_140_19 (by norm_num)

theorem c22250R_140_17 : rowsJ2 140 141 71 360 ≤ 629614716690321 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4351 c22250R_140_18 (by norm_num)

theorem c22250R_140_16 : rowsJ2 140 141 70 360 ≤ 638417529261985 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4350 c22250R_140_17 (by norm_num)

theorem c22250R_140_15 : rowsJ2 140 141 69 360 ≤ 646872096873740 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4349 c22250R_140_16 (by norm_num)

theorem c22250R_140_14 : rowsJ2 140 141 68 360 ≤ 654939251831435 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4348 c22250R_140_15 (by norm_num)

theorem c22250R_140_13 : rowsJ2 140 141 67 360 ≤ 662562865052453 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4347 c22250R_140_14 (by norm_num)

theorem c22250R_140_12 : rowsJ2 140 141 66 360 ≤ 669704717823873 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4346 c22250R_140_13 (by norm_num)

theorem c22250R_140_11 : rowsJ2 140 141 65 360 ≤ 676309614828406 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4345 c22250R_140_12 (by norm_num)

theorem c22250R_140_10 : rowsJ2 140 141 64 360 ≤ 682339924923849 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4344 c22250R_140_11 (by norm_num)

theorem c22250R_140_9 : rowsJ2 140 141 63 360 ≤ 687741029774926 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4343 c22250R_140_10 (by norm_num)

theorem c22250R_140_8 : rowsJ2 140 141 62 360 ≤ 692509870189489 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4342 c22250R_140_9 (by norm_num)

theorem c22250R_140_7 : rowsJ2 140 141 61 360 ≤ 696678559836961 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4341 c22250R_140_8 (by norm_num)

theorem c22250R_140_6 : rowsJ2 140 141 60 360 ≤ 700280461988257 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4340 c22250R_140_7 (by norm_num)

theorem c22250R_140_5 : rowsJ2 140 141 58 360 ≤ 705924158944308 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4339 c22250R_140_6 (by norm_num)

theorem c22250R_140_4 : rowsJ2 140 141 56 360 ≤ 709736466065019 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4338 c22250R_140_5 (by norm_num)

theorem c22250R_140_3 : rowsJ2 140 141 51 360 ≤ 713442824888604 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4337 c22250R_140_4 (by norm_num)

theorem c22250R_140_2 : rowsJ2 140 141 30 360 ≤ 715029343006087 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4336 c22250R_140_3 (by norm_num)

theorem c22250R_140_1 : rowsJ2 140 141 25 360 ≤ 723938454849303 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4335 c22250R_140_2 (by norm_num)

theorem c22250R_140_0 : rowsJ2 140 141 0 360 ≤ 727363305197307 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22250R_4334 c22250R_140_1 (by norm_num)

theorem hr22250R_140 : rows2 140 141 ≤ 727363305197307 := rows2_le_of_rowsJ2 140 141 c22250R_140_0

theorem c22250R_141_31 : rowsJ2 141 142 88 360 ≤ 492659058838225 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4397 rows22250R_4398 (by norm_num)

theorem c22250R_141_30 : rowsJ2 141 142 85 360 ≤ 495323866029457 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4396 c22250R_141_31 (by norm_num)

theorem c22250R_141_29 : rowsJ2 141 142 83 360 ≤ 497762191962227 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4395 c22250R_141_30 (by norm_num)

theorem c22250R_141_28 : rowsJ2 141 142 81 360 ≤ 501514847713156 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4394 c22250R_141_29 (by norm_num)

theorem c22250R_141_27 : rowsJ2 141 142 80 360 ≤ 503978892953398 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4393 c22250R_141_28 (by norm_num)

theorem c22250R_141_26 : rowsJ2 141 142 79 360 ≤ 506879516567524 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4392 c22250R_141_27 (by norm_num)

theorem c22250R_141_25 : rowsJ2 141 142 78 360 ≤ 510265292572212 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4391 c22250R_141_26 (by norm_num)

theorem c22250R_141_24 : rowsJ2 141 142 77 360 ≤ 514167265081669 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4390 c22250R_141_25 (by norm_num)

theorem c22250R_141_23 : rowsJ2 141 142 76 360 ≤ 518635811883194 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4389 c22250R_141_24 (by norm_num)

theorem c22250R_141_22 : rowsJ2 141 142 75 360 ≤ 523704117390201 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4388 c22250R_141_23 (by norm_num)

theorem c22250R_141_21 : rowsJ2 141 142 74 360 ≤ 529424589020603 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4387 c22250R_141_22 (by norm_num)

theorem c22250R_141_20 : rowsJ2 141 142 73 360 ≤ 535832775692798 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4386 c22250R_141_21 (by norm_num)

theorem c22250R_141_19 : rowsJ2 141 142 72 360 ≤ 542983361769903 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4385 c22250R_141_20 (by norm_num)

theorem c22250R_141_18 : rowsJ2 141 142 71 360 ≤ 550914508161835 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4384 c22250R_141_19 (by norm_num)

theorem c22250R_141_17 : rowsJ2 141 142 70 360 ≤ 559683448110249 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4383 c22250R_141_18 (by norm_num)

theorem c22250R_141_16 : rowsJ2 141 142 69 360 ≤ 568692178149932 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4382 c22250R_141_17 (by norm_num)

theorem c22250R_141_15 : rowsJ2 141 142 68 360 ≤ 577287409594899 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4381 c22250R_141_16 (by norm_num)

theorem c22250R_141_14 : rowsJ2 141 142 67 360 ≤ 585413393432462 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4380 c22250R_141_15 (by norm_num)

theorem c22250R_141_13 : rowsJ2 141 142 66 360 ≤ 593032176810382 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4379 c22250R_141_14 (by norm_num)

theorem c22250R_141_12 : rowsJ2 141 142 65 360 ≤ 600088899231394 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4378 c22250R_141_13 (by norm_num)

theorem c22250R_141_11 : rowsJ2 141 142 64 360 ≤ 606546152572008 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4377 c22250R_141_12 (by norm_num)

theorem c22250R_141_10 : rowsJ2 141 142 63 360 ≤ 612349611026119 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4376 c22250R_141_11 (by norm_num)

theorem c22250R_141_9 : rowsJ2 141 142 62 360 ≤ 617496218358889 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4375 c22250R_141_10 (by norm_num)

theorem c22250R_141_8 : rowsJ2 141 142 61 360 ≤ 622017887640252 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4374 c22250R_141_9 (by norm_num)

theorem c22250R_141_7 : rowsJ2 141 142 60 360 ≤ 625947755869525 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4373 c22250R_141_8 (by norm_num)

theorem c22250R_141_6 : rowsJ2 141 142 59 360 ≤ 629320275039298 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4372 c22250R_141_7 (by norm_num)

theorem c22250R_141_5 : rowsJ2 141 142 58 360 ≤ 632171308194586 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4371 c22250R_141_6 (by norm_num)

theorem c22250R_141_4 : rowsJ2 141 142 56 360 ≤ 636460038504287 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4370 c22250R_141_5 (by norm_num)

theorem c22250R_141_3 : rowsJ2 141 142 51 360 ≤ 640885481125108 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4369 c22250R_141_4 (by norm_num)

theorem c22250R_141_2 : rowsJ2 141 142 29 360 ≤ 642571736682373 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4368 c22250R_141_3 (by norm_num)

theorem c22250R_141_1 : rowsJ2 141 142 24 360 ≤ 650633615074145 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4367 c22250R_141_2 (by norm_num)

theorem c22250R_141_0 : rowsJ2 141 142 0 360 ≤ 652600649700812 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22250R_4366 c22250R_141_1 (by norm_num)

theorem hr22250R_141 : rows2 141 142 ≤ 652600649700812 := rows2_le_of_rowsJ2 141 142 c22250R_141_0

theorem c22250R_142_30 : rowsJ2 142 143 86 360 ≤ 489844826273992 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4429 rows22250R_4430 (by norm_num)

theorem c22250R_142_29 : rowsJ2 142 143 83 360 ≤ 492918014538027 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4428 c22250R_142_30 (by norm_num)

theorem c22250R_142_28 : rowsJ2 142 143 81 360 ≤ 496553375200239 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4427 c22250R_142_29 (by norm_num)

theorem c22250R_142_27 : rowsJ2 142 143 80 360 ≤ 498959408583955 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4426 c22250R_142_28 (by norm_num)

theorem c22250R_142_26 : rowsJ2 142 143 79 360 ≤ 501802512784436 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4425 c22250R_142_27 (by norm_num)

theorem c22250R_142_25 : rowsJ2 142 143 78 360 ≤ 505131239546672 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4424 c22250R_142_26 (by norm_num)

theorem c22250R_142_24 : rowsJ2 142 143 77 360 ≤ 508976706036427 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4423 c22250R_142_25 (by norm_num)

theorem c22250R_142_23 : rowsJ2 142 143 76 360 ≤ 513389266537822 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4422 c22250R_142_24 (by norm_num)

theorem c22250R_142_22 : rowsJ2 142 143 75 360 ≤ 518402176182586 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4421 c22250R_142_23 (by norm_num)

theorem c22250R_142_21 : rowsJ2 142 143 74 360 ≤ 524067817803571 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4420 c22250R_142_22 (by norm_num)

theorem c22250R_142_20 : rowsJ2 142 143 73 360 ≤ 530421808907708 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4419 c22250R_142_21 (by norm_num)

theorem c22250R_142_19 : rowsJ2 142 143 72 360 ≤ 537518808323687 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4418 c22250R_142_20 (by norm_num)

theorem c22250R_142_18 : rowsJ2 142 143 71 360 ≤ 545397043605737 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4417 c22250R_142_19 (by norm_num)

theorem c22250R_142_17 : rowsJ2 142 143 70 360 ≤ 554113721628733 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4416 c22250R_142_18 (by norm_num)

theorem c22250R_142_16 : rowsJ2 142 143 69 360 ≤ 563709954298480 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4415 c22250R_142_17 (by norm_num)

theorem c22250R_142_15 : rowsJ2 142 143 68 360 ≤ 572866340919750 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4414 c22250R_142_16 (by norm_num)

theorem c22250R_142_14 : rowsJ2 142 143 67 360 ≤ 581527525345873 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4413 c22250R_142_15 (by norm_num)

theorem c22250R_142_13 : rowsJ2 142 143 66 360 ≤ 589655833766137 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4412 c22250R_142_14 (by norm_num)

theorem c22250R_142_12 : rowsJ2 142 143 65 360 ≤ 597196752203984 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4411 c22250R_142_13 (by norm_num)

theorem c22250R_142_11 : rowsJ2 142 143 64 360 ≤ 604113107701681 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4410 c22250R_142_12 (by norm_num)

theorem c22250R_142_10 : rowsJ2 142 143 63 360 ≤ 610350877724043 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4409 c22250R_142_11 (by norm_num)

theorem c22250R_142_9 : rowsJ2 142 143 62 360 ≤ 615907022110285 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4408 c22250R_142_10 (by norm_num)

theorem c22250R_142_8 : rowsJ2 142 143 61 360 ≤ 620813267959085 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4407 c22250R_142_9 (by norm_num)

theorem c22250R_142_7 : rowsJ2 142 143 60 360 ≤ 625102540314047 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4406 c22250R_142_8 (by norm_num)

theorem c22250R_142_6 : rowsJ2 142 143 59 360 ≤ 628809052827132 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4405 c22250R_142_7 (by norm_num)

theorem c22250R_142_5 : rowsJ2 142 143 58 360 ≤ 631968403347172 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4404 c22250R_142_6 (by norm_num)

theorem c22250R_142_4 : rowsJ2 142 143 56 360 ≤ 636795542061282 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4403 c22250R_142_5 (by norm_num)

theorem c22250R_142_3 : rowsJ2 142 143 53 360 ≤ 640913761529600 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4402 c22250R_142_4 (by norm_num)

theorem c22250R_142_2 : rowsJ2 142 143 30 360 ≤ 642854785273224 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4401 c22250R_142_3 (by norm_num)

theorem c22250R_142_1 : rowsJ2 142 143 24 360 ≤ 650190266277858 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4400 c22250R_142_2 (by norm_num)

theorem c22250R_142_0 : rowsJ2 142 143 0 360 ≤ 652374742508752 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22250R_4399 c22250R_142_1 (by norm_num)

theorem hr22250R_142 : rows2 142 143 ≤ 652374742508752 := rows2_le_of_rowsJ2 142 143 c22250R_142_0

theorem c22250R_143_30 : rowsJ2 143 144 87 360 ≤ 412168344732435 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4461 rows22250R_4462 (by norm_num)

theorem c22250R_143_29 : rowsJ2 143 144 84 360 ≤ 414169387359569 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4460 c22250R_143_30 (by norm_num)

theorem c22250R_143_28 : rowsJ2 143 144 82 360 ≤ 416908679937715 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4459 c22250R_143_29 (by norm_num)

theorem c22250R_143_27 : rowsJ2 143 144 80 360 ≤ 421112484012598 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4458 c22250R_143_28 (by norm_num)

theorem c22250R_143_26 : rowsJ2 143 144 79 360 ≤ 423855951806572 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4457 c22250R_143_27 (by norm_num)

theorem c22250R_143_25 : rowsJ2 143 144 78 360 ≤ 427085410039170 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4456 c22250R_143_26 (by norm_num)

theorem c22250R_143_24 : rowsJ2 143 144 77 360 ≤ 430832046273538 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4455 c22250R_143_25 (by norm_num)

theorem c22250R_143_23 : rowsJ2 143 144 76 360 ≤ 435146189603382 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4454 c22250R_143_24 (by norm_num)

theorem c22250R_143_22 : rowsJ2 143 144 75 360 ≤ 440061163180730 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4453 c22250R_143_23 (by norm_num)

theorem c22250R_143_21 : rowsJ2 143 144 74 360 ≤ 445629323512012 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4452 c22250R_143_22 (by norm_num)

theorem c22250R_143_20 : rowsJ2 143 144 73 360 ≤ 451886353953888 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4451 c22250R_143_21 (by norm_num)

theorem c22250R_143_19 : rowsJ2 143 144 72 360 ≤ 458886886008651 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4450 c22250R_143_20 (by norm_num)

theorem c22250R_143_18 : rowsJ2 143 144 71 360 ≤ 466669211098295 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4449 c22250R_143_19 (by norm_num)

theorem c22250R_143_17 : rowsJ2 143 144 70 360 ≤ 475290507891951 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4448 c22250R_143_18 (by norm_num)

theorem c22250R_143_16 : rowsJ2 143 144 69 360 ≤ 484791950353794 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4447 c22250R_143_17 (by norm_num)

theorem c22250R_143_15 : rowsJ2 143 144 68 360 ≤ 494517792586350 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4446 c22250R_143_16 (by norm_num)

theorem c22250R_143_14 : rowsJ2 143 144 67 360 ≤ 503721992317515 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4445 c22250R_143_15 (by norm_num)

theorem c22250R_143_13 : rowsJ2 143 144 66 360 ≤ 512367164986502 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4444 c22250R_143_14 (by norm_num)

theorem c22250R_143_12 : rowsJ2 143 144 65 360 ≤ 520399151735472 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4443 c22250R_143_13 (by norm_num)

theorem c22250R_143_11 : rowsJ2 143 144 64 360 ≤ 527781023657250 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4442 c22250R_143_12 (by norm_num)

theorem c22250R_143_10 : rowsJ2 143 144 63 360 ≤ 534459068835853 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4441 c22250R_143_11 (by norm_num)

theorem c22250R_143_9 : rowsJ2 143 144 62 360 ≤ 540430272717244 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4440 c22250R_143_10 (by norm_num)

theorem c22250R_143_8 : rowsJ2 143 144 61 360 ≤ 545726187294921 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4439 c22250R_143_9 (by norm_num)

theorem c22250R_143_7 : rowsJ2 143 144 60 360 ≤ 550379536059369 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4438 c22250R_143_8 (by norm_num)

theorem c22250R_143_6 : rowsJ2 143 144 59 360 ≤ 554424304292022 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4437 c22250R_143_7 (by norm_num)

theorem c22250R_143_5 : rowsJ2 143 144 58 360 ≤ 557895834212590 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4436 c22250R_143_6 (by norm_num)

theorem c22250R_143_4 : rowsJ2 143 144 56 360 ≤ 563267940799782 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4435 c22250R_143_5 (by norm_num)

theorem c22250R_143_3 : rowsJ2 143 144 53 360 ≤ 568000018309983 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4434 c22250R_143_4 (by norm_num)

theorem c22250R_143_2 : rowsJ2 143 144 31 360 ≤ 570048325407384 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4433 c22250R_143_3 (by norm_num)

theorem c22250R_143_1 : rowsJ2 143 144 24 360 ≤ 575548886906217 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4432 c22250R_143_2 (by norm_num)

theorem c22250R_143_0 : rowsJ2 143 144 0 360 ≤ 578065978860141 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22250R_4431 c22250R_143_1 (by norm_num)

theorem hr22250R_143 : rows2 143 144 ≤ 578065978860141 := rows2_le_of_rowsJ2 143 144 c22250R_143_0

theorem c22250R_144_29 : rowsJ2 144 145 85 360 ≤ 412437563014496 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4492 rows22250R_4493 (by norm_num)

theorem c22250R_144_28 : rowsJ2 144 145 82 360 ≤ 415732106116366 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4491 c22250R_144_29 (by norm_num)

theorem c22250R_144_27 : rowsJ2 144 145 80 360 ≤ 419698339257303 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4490 c22250R_144_28 (by norm_num)

theorem c22250R_144_26 : rowsJ2 144 145 79 360 ≤ 422323696765330 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4489 c22250R_144_27 (by norm_num)

theorem c22250R_144_25 : rowsJ2 144 145 78 360 ≤ 425435496508091 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4488 c22250R_144_26 (by norm_num)

theorem c22250R_144_24 : rowsJ2 144 145 77 360 ≤ 429064996693659 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4487 c22250R_144_25 (by norm_num)

theorem c22250R_144_23 : rowsJ2 144 145 76 360 ≤ 433262502494522 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4486 c22250R_144_24 (by norm_num)

theorem c22250R_144_22 : rowsJ2 144 145 75 360 ≤ 438061405429011 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4485 c22250R_144_23 (by norm_num)

theorem c22250R_144_21 : rowsJ2 144 145 74 360 ≤ 443514037039082 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4484 c22250R_144_22 (by norm_num)

theorem c22250R_144_20 : rowsJ2 144 145 73 360 ≤ 449656146987909 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4483 c22250R_144_21 (by norm_num)

theorem c22250R_144_19 : rowsJ2 144 145 72 360 ≤ 456542340919488 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4482 c22250R_144_20 (by norm_num)

theorem c22250R_144_18 : rowsJ2 144 145 71 360 ≤ 464210974704160 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4481 c22250R_144_19 (by norm_num)

theorem c22250R_144_17 : rowsJ2 144 145 70 360 ≤ 472719200393696 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4480 c22250R_144_18 (by norm_num)

theorem c22250R_144_16 : rowsJ2 144 145 69 360 ≤ 482108254729000 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4479 c22250R_144_17 (by norm_num)

theorem c22250R_144_15 : rowsJ2 144 145 68 360 ≤ 492438136703622 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4478 c22250R_144_16 (by norm_num)

theorem c22250R_144_14 : rowsJ2 144 145 67 360 ≤ 502219649091702 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4477 c22250R_144_15 (by norm_num)

theorem c22250R_144_13 : rowsJ2 144 145 66 360 ≤ 511415711420148 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4476 c22250R_144_14 (by norm_num)

theorem c22250R_144_12 : rowsJ2 144 145 65 360 ≤ 519972533240366 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4475 c22250R_144_13 (by norm_num)

theorem c22250R_144_11 : rowsJ2 144 145 64 360 ≤ 527853443314159 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4474 c22250R_144_12 (by norm_num)

theorem c22250R_144_10 : rowsJ2 144 145 63 360 ≤ 535005052503330 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4473 c22250R_144_11 (by norm_num)

theorem c22250R_144_9 : rowsJ2 144 145 62 360 ≤ 541424386229977 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4472 c22250R_144_10 (by norm_num)

theorem c22250R_144_8 : rowsJ2 144 145 61 360 ≤ 547142837131779 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4471 c22250R_144_9 (by norm_num)

theorem c22250R_144_7 : rowsJ2 144 145 60 360 ≤ 552192942513300 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4470 c22250R_144_8 (by norm_num)

theorem c22250R_144_6 : rowsJ2 144 145 59 360 ≤ 556608474308166 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4469 c22250R_144_7 (by norm_num)

theorem c22250R_144_5 : rowsJ2 144 145 58 360 ≤ 560424533820971 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4468 c22250R_144_6 (by norm_num)

theorem c22250R_144_4 : rowsJ2 144 145 56 360 ≤ 566405893229942 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4467 c22250R_144_5 (by norm_num)

theorem c22250R_144_3 : rowsJ2 144 145 54 360 ≤ 570448359762509 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4466 c22250R_144_4 (by norm_num)

theorem c22250R_144_2 : rowsJ2 144 145 33 360 ≤ 574537074530025 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4465 c22250R_144_3 (by norm_num)

theorem c22250R_144_1 : rowsJ2 144 145 24 360 ≤ 578343461240433 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4464 c22250R_144_2 (by norm_num)

theorem c22250R_144_0 : rowsJ2 144 145 0 360 ≤ 581306787052370 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22250R_4463 c22250R_144_1 (by norm_num)

theorem hr22250R_144 : rows2 144 145 ≤ 581306787052370 := rows2_le_of_rowsJ2 144 145 c22250R_144_0

theorem c22250R_145_29 : rowsJ2 145 146 87 360 ≤ 481866147331716 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4523 rows22250R_4524 (by norm_num)

theorem c22250R_145_28 : rowsJ2 145 146 83 360 ≤ 484191273415169 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4522 c22250R_145_29 (by norm_num)

theorem c22250R_145_27 : rowsJ2 145 146 81 360 ≤ 487065268886276 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4521 c22250R_145_28 (by norm_num)

theorem c22250R_145_26 : rowsJ2 145 146 79 360 ≤ 491557432576307 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4520 c22250R_145_27 (by norm_num)

theorem c22250R_145_25 : rowsJ2 145 146 78 360 ≤ 494509466893670 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4519 c22250R_145_26 (by norm_num)

theorem c22250R_145_24 : rowsJ2 145 146 77 360 ≤ 497979622617993 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4518 c22250R_145_25 (by norm_num)

theorem c22250R_145_23 : rowsJ2 145 146 76 360 ≤ 502018179264460 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4517 c22250R_145_24 (by norm_num)

theorem c22250R_145_22 : rowsJ2 145 146 75 360 ≤ 506658594002506 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4516 c22250R_145_23 (by norm_num)

theorem c22250R_145_21 : rowsJ2 145 146 74 360 ≤ 511953171622382 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4515 c22250R_145_22 (by norm_num)

theorem c22250R_145_20 : rowsJ2 145 146 73 360 ≤ 517937725340438 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4514 c22250R_145_21 (by norm_num)

theorem c22250R_145_19 : rowsJ2 145 146 72 360 ≤ 524666833107652 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4513 c22250R_145_20 (by norm_num)

theorem c22250R_145_18 : rowsJ2 145 146 71 360 ≤ 532178912454309 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4512 c22250R_145_19 (by norm_num)

theorem c22250R_145_17 : rowsJ2 145 146 70 360 ≤ 540531086936209 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4511 c22250R_145_18 (by norm_num)

theorem c22250R_145_16 : rowsJ2 145 146 69 360 ≤ 549764653250689 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4510 c22250R_145_17 (by norm_num)

theorem c22250R_145_15 : rowsJ2 145 146 68 360 ≤ 559939581218177 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4509 c22250R_145_16 (by norm_num)

theorem c22250R_145_14 : rowsJ2 145 146 67 360 ≤ 570307214935382 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4508 c22250R_145_15 (by norm_num)

theorem c22250R_145_13 : rowsJ2 145 146 66 360 ≤ 580062457160090 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4507 c22250R_145_14 (by norm_num)

theorem c22250R_145_12 : rowsJ2 145 146 65 360 ≤ 589151896068310 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4506 c22250R_145_13 (by norm_num)

theorem c22250R_145_11 : rowsJ2 145 146 64 360 ≤ 597539128465356 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4505 c22250R_145_12 (by norm_num)

theorem c22250R_145_10 : rowsJ2 145 146 63 360 ≤ 605171096764995 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4504 c22250R_145_11 (by norm_num)

theorem c22250R_145_9 : rowsJ2 145 146 62 360 ≤ 612044877153098 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4503 c22250R_145_10 (by norm_num)

theorem c22250R_145_8 : rowsJ2 145 146 61 360 ≤ 618191714894097 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4502 c22250R_145_9 (by norm_num)

theorem c22250R_145_7 : rowsJ2 145 146 60 360 ≤ 623643972548284 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4501 c22250R_145_8 (by norm_num)

theorem c22250R_145_6 : rowsJ2 145 146 59 360 ≤ 628435219637648 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4500 c22250R_145_7 (by norm_num)

theorem c22250R_145_5 : rowsJ2 145 146 58 360 ≤ 632600327015932 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4499 c22250R_145_6 (by norm_num)

theorem c22250R_145_4 : rowsJ2 145 146 56 360 ≤ 639198715101005 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4498 c22250R_145_5 (by norm_num)

theorem c22250R_145_3 : rowsJ2 145 146 54 360 ≤ 643748052435477 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4497 c22250R_145_4 (by norm_num)

theorem c22250R_145_2 : rowsJ2 145 146 36 360 ≤ 648696617700864 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4496 c22250R_145_3 (by norm_num)

theorem c22250R_145_1 : rowsJ2 145 146 24 360 ≤ 651203799585989 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4495 c22250R_145_2 (by norm_num)

theorem c22250R_145_0 : rowsJ2 145 146 0 360 ≤ 653982925548645 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22250R_4494 c22250R_145_1 (by norm_num)

theorem hr22250R_145 : rows2 145 146 ≤ 653982925548645 := rows2_le_of_rowsJ2 145 146 c22250R_145_0

theorem c22250R_146_29 : rowsJ2 146 147 84 360 ≤ 626813976264032 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4554 rows22250R_4555 (by norm_num)

theorem c22250R_146_28 : rowsJ2 146 147 81 360 ≤ 630202334804981 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4553 c22250R_146_29 (by norm_num)

theorem c22250R_146_27 : rowsJ2 146 147 79 360 ≤ 634337950830531 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4552 c22250R_146_28 (by norm_num)

theorem c22250R_146_26 : rowsJ2 146 147 78 360 ≤ 637112389386402 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4551 c22250R_146_27 (by norm_num)

theorem c22250R_146_25 : rowsJ2 146 147 77 360 ≤ 640405461914074 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4550 c22250R_146_26 (by norm_num)

theorem c22250R_146_24 : rowsJ2 146 147 76 360 ≤ 644267423547355 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4549 c22250R_146_25 (by norm_num)

theorem c22250R_146_23 : rowsJ2 146 147 75 360 ≤ 648731797492137 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4548 c22250R_146_24 (by norm_num)

theorem c22250R_146_22 : rowsJ2 146 147 74 360 ≤ 653850863161980 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4547 c22250R_146_23 (by norm_num)

theorem c22250R_146_21 : rowsJ2 146 147 73 360 ≤ 659660497828559 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4546 c22250R_146_22 (by norm_num)

theorem c22250R_146_20 : rowsJ2 146 147 72 360 ≤ 666215253237367 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4545 c22250R_146_21 (by norm_num)

theorem c22250R_146_19 : rowsJ2 146 147 71 360 ≤ 673553609210886 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4544 c22250R_146_20 (by norm_num)

theorem c22250R_146_18 : rowsJ2 146 147 70 360 ≤ 681732662423459 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4543 c22250R_146_19 (by norm_num)

theorem c22250R_146_17 : rowsJ2 146 147 69 360 ≤ 690793770305400 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4542 c22250R_146_18 (by norm_num)

theorem c22250R_146_16 : rowsJ2 146 147 68 360 ≤ 700796875260835 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4541 c22250R_146_17 (by norm_num)

theorem c22250R_146_15 : rowsJ2 146 147 67 360 ≤ 711786517865612 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4540 c22250R_146_16 (by norm_num)

theorem c22250R_146_14 : rowsJ2 146 147 66 360 ≤ 722136515228995 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4539 c22250R_146_15 (by norm_num)

theorem c22250R_146_13 : rowsJ2 146 147 65 360 ≤ 731793849256495 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4538 c22250R_146_14 (by norm_num)

theorem c22250R_146_12 : rowsJ2 146 147 64 360 ≤ 740722400096902 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4537 c22250R_146_13 (by norm_num)

theorem c22250R_146_11 : rowsJ2 146 147 63 360 ≤ 748869455486288 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4536 c22250R_146_12 (by norm_num)

theorem c22250R_146_10 : rowsJ2 146 147 62 360 ≤ 756232158181723 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4535 c22250R_146_11 (by norm_num)

theorem c22250R_146_9 : rowsJ2 146 147 61 360 ≤ 762841623120558 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4534 c22250R_146_10 (by norm_num)

theorem c22250R_146_8 : rowsJ2 146 147 60 360 ≤ 768730054702147 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4533 c22250R_146_9 (by norm_num)

theorem c22250R_146_7 : rowsJ2 146 147 59 360 ≤ 773930836199919 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4532 c22250R_146_8 (by norm_num)

theorem c22250R_146_6 : rowsJ2 146 147 58 360 ≤ 778478623800009 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4531 c22250R_146_7 (by norm_num)

theorem c22250R_146_5 : rowsJ2 146 147 57 360 ≤ 782409445667040 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4530 c22250R_146_6 (by norm_num)

theorem c22250R_146_4 : rowsJ2 146 147 56 360 ≤ 785760806465438 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4529 c22250R_146_5 (by norm_num)

theorem c22250R_146_3 : rowsJ2 146 147 54 360 ≤ 790883215038587 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4528 c22250R_146_4 (by norm_num)

theorem c22250R_146_2 : rowsJ2 146 147 48 360 ≤ 796792727299062 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4527 c22250R_146_3 (by norm_num)

theorem c22250R_146_1 : rowsJ2 146 147 24 360 ≤ 798461391050858 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4526 c22250R_146_2 (by norm_num)

theorem c22250R_146_0 : rowsJ2 146 147 0 360 ≤ 801389593765211 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22250R_4525 c22250R_146_1 (by norm_num)

theorem hr22250R_146 : rows2 146 147 ≤ 801389593765211 := rows2_le_of_rowsJ2 146 147 c22250R_146_0

theorem c22250R_147_28 : rowsJ2 147 148 82 360 ≤ 690313222763211 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4584 rows22250R_4585 (by norm_num)

theorem c22250R_147_27 : rowsJ2 147 148 80 360 ≤ 693269787008518 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4583 c22250R_147_28 (by norm_num)

theorem c22250R_147_26 : rowsJ2 147 148 78 360 ≤ 697909737825246 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4582 c22250R_147_27 (by norm_num)

theorem c22250R_147_25 : rowsJ2 147 148 77 360 ≤ 700983534448843 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4581 c22250R_147_26 (by norm_num)

theorem c22250R_147_24 : rowsJ2 147 148 76 360 ≤ 704626608644810 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4580 c22250R_147_25 (by norm_num)

theorem c22250R_147_23 : rowsJ2 147 148 75 360 ≤ 708872546908219 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4579 c22250R_147_24 (by norm_num)

theorem c22250R_147_22 : rowsJ2 147 148 74 360 ≤ 713773601429409 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4578 c22250R_147_23 (by norm_num)

theorem c22250R_147_21 : rowsJ2 147 148 73 360 ≤ 719365710753134 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4577 c22250R_147_22 (by norm_num)

theorem c22250R_147_20 : rowsJ2 147 148 72 360 ≤ 725703398528845 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4576 c22250R_147_21 (by norm_num)

theorem c22250R_147_19 : rowsJ2 147 148 71 360 ≤ 732825204056944 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4575 c22250R_147_20 (by norm_num)

theorem c22250R_147_18 : rowsJ2 147 148 70 360 ≤ 740788195199280 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4574 c22250R_147_19 (by norm_num)

theorem c22250R_147_17 : rowsJ2 147 148 69 360 ≤ 749633787276050 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4573 c22250R_147_18 (by norm_num)

theorem c22250R_147_16 : rowsJ2 147 148 68 360 ≤ 759421893307420 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4572 c22250R_147_17 (by norm_num)

theorem c22250R_147_15 : rowsJ2 147 148 67 360 ≤ 770197110366559 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4571 c22250R_147_16 (by norm_num)

theorem c22250R_147_14 : rowsJ2 147 148 66 360 ≤ 781151206178859 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4570 c22250R_147_15 (by norm_num)

theorem c22250R_147_13 : rowsJ2 147 148 65 360 ≤ 791385224890614 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4569 c22250R_147_14 (by norm_num)

theorem c22250R_147_12 : rowsJ2 147 148 64 360 ≤ 800863342083001 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4568 c22250R_147_13 (by norm_num)

theorem c22250R_147_11 : rowsJ2 147 148 63 360 ≤ 809533201222209 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4567 c22250R_147_12 (by norm_num)

theorem c22250R_147_10 : rowsJ2 147 148 62 360 ≤ 817392023875782 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4566 c22250R_147_11 (by norm_num)

theorem c22250R_147_9 : rowsJ2 147 148 61 360 ≤ 824470807938965 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4565 c22250R_147_10 (by norm_num)

theorem c22250R_147_8 : rowsJ2 147 148 60 360 ≤ 830801612304540 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4564 c22250R_147_9 (by norm_num)

theorem c22250R_147_7 : rowsJ2 147 148 59 360 ≤ 836417646062184 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4563 c22250R_147_8 (by norm_num)

theorem c22250R_147_6 : rowsJ2 147 148 58 360 ≤ 841353362244091 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4562 c22250R_147_7 (by norm_num)

theorem c22250R_147_5 : rowsJ2 147 148 57 360 ≤ 845644556517114 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4561 c22250R_147_6 (by norm_num)

theorem c22250R_147_4 : rowsJ2 147 148 55 360 ≤ 852443905405884 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4560 c22250R_147_5 (by norm_num)

theorem c22250R_147_3 : rowsJ2 147 148 53 360 ≤ 857133015036867 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4559 c22250R_147_4 (by norm_num)

theorem c22250R_147_2 : rowsJ2 147 148 49 360 ≤ 861598088944575 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4558 c22250R_147_3 (by norm_num)

theorem c22250R_147_1 : rowsJ2 147 148 24 360 ≤ 863063103008503 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4557 c22250R_147_2 (by norm_num)

theorem c22250R_147_0 : rowsJ2 147 148 0 360 ≤ 865583708064445 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22250R_4556 c22250R_147_1 (by norm_num)

theorem hr22250R_147 : rows2 147 148 ≤ 865583708064445 := rows2_le_of_rowsJ2 147 148 c22250R_147_0

theorem c22250R_148_29 : rowsJ2 148 149 83 360 ≤ 827278182163633 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4615 rows22250R_4616 (by norm_num)

theorem c22250R_148_28 : rowsJ2 148 149 80 360 ≤ 830764707326986 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4614 c22250R_148_29 (by norm_num)

theorem c22250R_148_27 : rowsJ2 148 149 78 360 ≤ 835020273134515 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4613 c22250R_148_28 (by norm_num)

theorem c22250R_148_26 : rowsJ2 148 149 77 360 ≤ 837875270512950 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4612 c22250R_148_27 (by norm_num)

theorem c22250R_148_25 : rowsJ2 148 149 76 360 ≤ 841282308160239 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4611 c22250R_148_26 (by norm_num)

theorem c22250R_148_24 : rowsJ2 148 149 75 360 ≤ 845292762625488 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4610 c22250R_148_25 (by norm_num)

theorem c22250R_148_23 : rowsJ2 148 149 74 360 ≤ 849958860252752 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4609 c22250R_148_24 (by norm_num)

theorem c22250R_148_22 : rowsJ2 148 149 73 360 ≤ 855316601395340 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4608 c22250R_148_23 (by norm_num)

theorem c22250R_148_21 : rowsJ2 148 149 72 360 ≤ 861420483103189 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4607 c22250R_148_22 (by norm_num)

theorem c22250R_148_20 : rowsJ2 148 149 71 360 ≤ 868309104827045 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4606 c22250R_148_21 (by norm_num)

theorem c22250R_148_19 : rowsJ2 148 149 70 360 ≤ 876039507246938 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4605 c22250R_148_20 (by norm_num)

theorem c22250R_148_18 : rowsJ2 148 149 69 360 ≤ 884653164396675 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4604 c22250R_148_19 (by norm_num)

theorem c22250R_148_17 : rowsJ2 148 149 68 360 ≤ 894209961692845 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4603 c22250R_148_18 (by norm_num)

theorem c22250R_148_16 : rowsJ2 148 149 67 360 ≤ 904754553696763 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4602 c22250R_148_17 (by norm_num)

theorem c22250R_148_15 : rowsJ2 148 149 66 360 ≤ 916350004094061 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4601 c22250R_148_16 (by norm_num)

theorem c22250R_148_14 : rowsJ2 148 149 65 360 ≤ 927197623538600 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4600 c22250R_148_15 (by norm_num)

theorem c22250R_148_13 : rowsJ2 148 149 64 360 ≤ 937261900273137 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4599 c22250R_148_14 (by norm_num)

theorem c22250R_148_12 : rowsJ2 148 149 63 360 ≤ 946490849105408 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4598 c22250R_148_13 (by norm_num)

theorem c22250R_148_11 : rowsJ2 148 149 62 360 ≤ 954881787875867 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4597 c22250R_148_12 (by norm_num)

theorem c22250R_148_10 : rowsJ2 148 149 61 360 ≤ 962465615985446 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4596 c22250R_148_11 (by norm_num)

theorem c22250R_148_9 : rowsJ2 148 149 60 360 ≤ 969274264811379 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4595 c22250R_148_10 (by norm_num)

theorem c22250R_148_8 : rowsJ2 148 149 59 360 ≤ 975340786742435 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4594 c22250R_148_9 (by norm_num)

theorem c22250R_148_7 : rowsJ2 148 149 58 360 ≤ 980699448677636 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4593 c22250R_148_8 (by norm_num)

theorem c22250R_148_6 : rowsJ2 148 149 57 360 ≤ 985385830388452 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4592 c22250R_148_7 (by norm_num)

theorem c22250R_148_5 : rowsJ2 148 149 56 360 ≤ 989436928171366 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4591 c22250R_148_6 (by norm_num)

theorem c22250R_148_4 : rowsJ2 148 149 55 360 ≤ 992891264247576 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4590 c22250R_148_5 (by norm_num)

theorem c22250R_148_3 : rowsJ2 148 149 53 360 ≤ 998172070372838 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4589 c22250R_148_4 (by norm_num)

theorem c22250R_148_2 : rowsJ2 148 149 50 360 ≤ 1002681770681703 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4588 c22250R_148_3 (by norm_num)

theorem c22250R_148_1 : rowsJ2 148 149 24 360 ≤ 1004793641719609 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4587 c22250R_148_2 (by norm_num)

theorem c22250R_148_0 : rowsJ2 148 149 0 360 ≤ 1007236654344140 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22250R_4586 c22250R_148_1 (by norm_num)

theorem hr22250R_148 : rows2 148 149 ≤ 1007236654344140 := rows2_le_of_rowsJ2 148 149 c22250R_148_0

theorem c22250R_149_28 : rowsJ2 149 150 82 360 ≤ 882216623693408 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4645 rows22250R_4646 (by norm_num)

theorem c22250R_149_27 : rowsJ2 149 150 79 360 ≤ 886255209898796 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4644 c22250R_149_28 (by norm_num)

theorem c22250R_149_26 : rowsJ2 149 150 77 360 ≤ 891030940241053 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4643 c22250R_149_27 (by norm_num)

theorem c22250R_149_25 : rowsJ2 149 150 76 360 ≤ 894194796154678 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4642 c22250R_149_26 (by norm_num)

theorem c22250R_149_24 : rowsJ2 149 150 75 360 ≤ 897944720479960 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4641 c22250R_149_25 (by norm_num)

theorem c22250R_149_23 : rowsJ2 149 150 74 360 ≤ 902333289838650 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4640 c22250R_149_24 (by norm_num)

theorem c22250R_149_22 : rowsJ2 149 150 73 360 ≤ 907413987783209 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4639 c22250R_149_23 (by norm_num)

theorem c22250R_149_21 : rowsJ2 149 150 72 360 ≤ 913241282803690 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4638 c22250R_149_22 (by norm_num)

theorem c22250R_149_20 : rowsJ2 149 150 71 360 ≤ 919853831646229 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4637 c22250R_149_21 (by norm_num)

theorem c22250R_149_19 : rowsJ2 149 150 70 360 ≤ 927308645812100 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4636 c22250R_149_20 (by norm_num)

theorem c22250R_149_18 : rowsJ2 149 150 69 360 ≤ 935647255168394 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4635 c22250R_149_19 (by norm_num)

theorem c22250R_149_17 : rowsJ2 149 150 68 360 ≤ 944929515498330 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4634 c22250R_149_18 (by norm_num)

theorem c22250R_149_16 : rowsJ2 149 150 67 360 ≤ 955200135949007 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4633 c22250R_149_17 (by norm_num)

theorem c22250R_149_15 : rowsJ2 149 150 66 360 ≤ 966522150274809 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4632 c22250R_149_16 (by norm_num)

theorem c22250R_149_14 : rowsJ2 149 150 65 360 ≤ 977993276688116 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4631 c22250R_149_15 (by norm_num)

theorem c22250R_149_13 : rowsJ2 149 150 64 360 ≤ 988653029154399 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4630 c22250R_149_14 (by norm_num)

theorem c22250R_149_12 : rowsJ2 149 150 63 360 ≤ 998449806109804 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4629 c22250R_149_13 (by norm_num)

theorem c22250R_149_11 : rowsJ2 149 150 62 360 ≤ 1007381035589904 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4628 c22250R_149_12 (by norm_num)

theorem c22250R_149_10 : rowsJ2 149 150 61 360 ≤ 1015477533306120 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4627 c22250R_149_11 (by norm_num)

theorem c22250R_149_9 : rowsJ2 149 150 60 360 ≤ 1022771117190140 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4626 c22250R_149_10 (by norm_num)

theorem c22250R_149_8 : rowsJ2 149 150 59 360 ≤ 1029294696312645 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4625 c22250R_149_9 (by norm_num)

theorem c22250R_149_7 : rowsJ2 149 150 58 360 ≤ 1035082364179583 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4624 c22250R_149_8 (by norm_num)

theorem c22250R_149_6 : rowsJ2 149 150 57 360 ≤ 1040169496806047 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4623 c22250R_149_7 (by norm_num)

theorem c22250R_149_5 : rowsJ2 149 150 56 360 ≤ 1044592855994265 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4622 c22250R_149_6 (by norm_num)

theorem c22250R_149_4 : rowsJ2 149 150 55 360 ≤ 1048390698271722 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4621 c22250R_149_5 (by norm_num)

theorem c22250R_149_3 : rowsJ2 149 150 53 360 ≤ 1054271029024120 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4620 c22250R_149_4 (by norm_num)

theorem c22250R_149_2 : rowsJ2 149 150 50 360 ≤ 1059455847424571 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4619 c22250R_149_3 (by norm_num)

theorem c22250R_149_1 : rowsJ2 149 150 24 360 ≤ 1061826065416978 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4618 c22250R_149_2 (by norm_num)

theorem c22250R_149_0 : rowsJ2 149 150 0 360 ≤ 1063721115081498 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22250R_4617 c22250R_149_1 (by norm_num)

theorem hr22250R_149 : rows2 149 150 ≤ 1063721115081498 := rows2_le_of_rowsJ2 149 150 c22250R_149_0

theorem c22250R_150_28 : rowsJ2 150 151 82 360 ≤ 1014785423726656 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4675 rows22250R_4676 (by norm_num)

theorem c22250R_150_27 : rowsJ2 150 151 79 360 ≤ 1018374708580719 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4674 c22250R_150_28 (by norm_num)

theorem c22250R_150_26 : rowsJ2 150 151 77 360 ≤ 1022755840506932 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4673 c22250R_150_27 (by norm_num)

theorem c22250R_150_25 : rowsJ2 150 151 76 360 ≤ 1025695171790490 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4672 c22250R_150_26 (by norm_num)

theorem c22250R_150_24 : rowsJ2 150 151 75 360 ≤ 1029202947454834 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4671 c22250R_150_25 (by norm_num)

theorem c22250R_150_23 : rowsJ2 150 151 74 360 ≤ 1033332114489964 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4670 c22250R_150_24 (by norm_num)

theorem c22250R_150_22 : rowsJ2 150 151 73 360 ≤ 1038136508351725 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4669 c22250R_150_23 (by norm_num)

theorem c22250R_150_21 : rowsJ2 150 151 72 360 ≤ 1043670931736311 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4668 c22250R_150_22 (by norm_num)

theorem c22250R_150_20 : rowsJ2 150 151 71 360 ≤ 1049991235901555 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4667 c22250R_150_21 (by norm_num)

theorem c22250R_150_19 : rowsJ2 150 151 70 360 ≤ 1057154404806017 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4666 c22250R_150_20 (by norm_num)

theorem c22250R_150_18 : rowsJ2 150 151 69 360 ≤ 1065202025009571 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4665 c22250R_150_19 (by norm_num)

theorem c22250R_150_17 : rowsJ2 150 151 68 360 ≤ 1074193924455895 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4664 c22250R_150_18 (by norm_num)

theorem c22250R_150_16 : rowsJ2 150 151 67 360 ≤ 1084174867912138 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4663 c22250R_150_17 (by norm_num)

theorem c22250R_150_15 : rowsJ2 150 151 66 360 ≤ 1095207861170136 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4662 c22250R_150_16 (by norm_num)

theorem c22250R_150_14 : rowsJ2 150 151 65 360 ≤ 1107341188587859 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4661 c22250R_150_15 (by norm_num)

theorem c22250R_150_13 : rowsJ2 150 151 64 360 ≤ 1118634742322766 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4660 c22250R_150_14 (by norm_num)

theorem c22250R_150_12 : rowsJ2 150 151 63 360 ≤ 1129037322162964 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4659 c22250R_150_13 (by norm_num)

theorem c22250R_150_11 : rowsJ2 150 151 62 360 ≤ 1138546485711556 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4658 c22250R_150_12 (by norm_num)

theorem c22250R_150_10 : rowsJ2 150 151 61 360 ≤ 1147192985279604 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4657 c22250R_150_11 (by norm_num)

theorem c22250R_150_9 : rowsJ2 150 151 60 360 ≤ 1155008544975673 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4656 c22250R_150_10 (by norm_num)

theorem c22250R_150_8 : rowsJ2 150 151 59 360 ≤ 1162025949564110 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4655 c22250R_150_9 (by norm_num)

theorem c22250R_150_7 : rowsJ2 150 151 58 360 ≤ 1168279137611671 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4654 c22250R_150_8 (by norm_num)

theorem c22250R_150_6 : rowsJ2 150 151 57 360 ≤ 1173803299323014 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4653 c22250R_150_7 (by norm_num)

theorem c22250R_150_5 : rowsJ2 150 151 56 360 ≤ 1178634979491374 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4652 c22250R_150_6 (by norm_num)

theorem c22250R_150_4 : rowsJ2 150 151 55 360 ≤ 1182812186019978 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4651 c22250R_150_5 (by norm_num)

theorem c22250R_150_3 : rowsJ2 150 151 53 360 ≤ 1189363219379229 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4650 c22250R_150_4 (by norm_num)

theorem c22250R_150_2 : rowsJ2 150 151 50 360 ≤ 1195328818853804 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4649 c22250R_150_3 (by norm_num)

theorem c22250R_150_1 : rowsJ2 150 151 24 360 ≤ 1198281973091663 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4648 c22250R_150_2 (by norm_num)

theorem c22250R_150_0 : rowsJ2 150 151 0 360 ≤ 1199963645641957 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22250R_4647 c22250R_150_1 (by norm_num)

theorem hr22250R_150 : rows2 150 151 ≤ 1199963645641957 := rows2_le_of_rowsJ2 150 151 c22250R_150_0

theorem c22250R_151_27 : rowsJ2 151 152 81 360 ≤ 1061528708236221 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4704 rows22250R_4705 (by norm_num)

theorem c22250R_151_26 : rowsJ2 151 152 78 360 ≤ 1065687358511704 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4703 c22250R_151_27 (by norm_num)

theorem c22250R_151_25 : rowsJ2 151 152 76 360 ≤ 1070605255976307 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4702 c22250R_151_26 (by norm_num)

theorem c22250R_151_24 : rowsJ2 151 152 75 360 ≤ 1073863411938713 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4701 c22250R_151_25 (by norm_num)

theorem c22250R_151_23 : rowsJ2 151 152 74 360 ≤ 1077725222030762 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4700 c22250R_151_24 (by norm_num)

theorem c22250R_151_22 : rowsJ2 151 152 73 360 ≤ 1082244890363390 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4699 c22250R_151_23 (by norm_num)

theorem c22250R_151_21 : rowsJ2 151 152 72 360 ≤ 1087477569812814 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4698 c22250R_151_22 (by norm_num)

theorem c22250R_151_20 : rowsJ2 151 152 71 360 ≤ 1093479444109289 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4697 c22250R_151_21 (by norm_num)

theorem c22250R_151_19 : rowsJ2 151 152 70 360 ≤ 1100307812697263 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4696 c22250R_151_20 (by norm_num)

theorem c22250R_151_18 : rowsJ2 151 152 69 360 ≤ 1108021178655586 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4695 c22250R_151_19 (by norm_num)

theorem c22250R_151_17 : rowsJ2 151 152 68 360 ≤ 1116679339982474 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4694 c22250R_151_18 (by norm_num)

theorem c22250R_151_16 : rowsJ2 151 152 67 360 ≤ 1126327114114257 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4693 c22250R_151_17 (by norm_num)

theorem c22250R_151_15 : rowsJ2 151 152 66 360 ≤ 1137027476749637 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4692 c22250R_151_16 (by norm_num)

theorem c22250R_151_14 : rowsJ2 151 152 65 360 ≤ 1148828764053252 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4691 c22250R_151_15 (by norm_num)

theorem c22250R_151_13 : rowsJ2 151 152 64 360 ≤ 1160766620323947 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4690 c22250R_151_14 (by norm_num)

theorem c22250R_151_12 : rowsJ2 151 152 63 360 ≤ 1171784875069174 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4689 c22250R_151_13 (by norm_num)

theorem c22250R_151_11 : rowsJ2 151 152 62 360 ≤ 1181881231337725 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4688 c22250R_151_12 (by norm_num)

theorem c22250R_151_10 : rowsJ2 151 152 61 360 ≤ 1191086394620538 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4687 c22250R_151_11 (by norm_num)

theorem c22250R_151_9 : rowsJ2 151 152 60 360 ≤ 1199432010926652 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4686 c22250R_151_10 (by norm_num)

theorem c22250R_151_8 : rowsJ2 151 152 59 360 ≤ 1206950755636670 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4685 c22250R_151_9 (by norm_num)

theorem c22250R_151_7 : rowsJ2 151 152 58 360 ≤ 1213676426551548 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4684 c22250R_151_8 (by norm_num)

theorem c22250R_151_6 : rowsJ2 151 152 57 360 ≤ 1219644041537966 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4683 c22250R_151_7 (by norm_num)

theorem c22250R_151_5 : rowsJ2 151 152 56 360 ≤ 1224889941196910 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4682 c22250R_151_6 (by norm_num)

theorem c22250R_151_4 : rowsJ2 151 152 55 360 ≤ 1229451897010673 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4681 c22250R_151_5 (by norm_num)

theorem c22250R_151_3 : rowsJ2 151 152 53 360 ≤ 1236682908596958 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4680 c22250R_151_4 (by norm_num)

theorem c22250R_151_2 : rowsJ2 151 152 50 360 ≤ 1243439625530276 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4679 c22250R_151_3 (by norm_num)

theorem c22250R_151_1 : rowsJ2 151 152 25 360 ≤ 1247107123030275 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4678 c22250R_151_2 (by norm_num)

theorem c22250R_151_0 : rowsJ2 151 152 0 360 ≤ 1248205985507416 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22250R_4677 c22250R_151_1 (by norm_num)

theorem hr22250R_151 : rows2 151 152 ≤ 1248205985507416 := rows2_le_of_rowsJ2 151 152 c22250R_151_0

theorem c22250R_152_26 : rowsJ2 152 153 79 360 ≤ 1191203446480759 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4732 rows22250R_4733 (by norm_num)

theorem c22250R_152_25 : rowsJ2 152 153 77 360 ≤ 1194810538329787 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4731 c22250R_152_26 (by norm_num)

theorem c22250R_152_24 : rowsJ2 152 153 75 360 ≤ 1200333961584285 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4730 c22250R_152_25 (by norm_num)

theorem c22250R_152_23 : rowsJ2 152 153 74 360 ≤ 1203947242704228 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4729 c22250R_152_24 (by norm_num)

theorem c22250R_152_22 : rowsJ2 152 153 73 360 ≤ 1208200745553206 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4728 c22250R_152_23 (by norm_num)

theorem c22250R_152_21 : rowsJ2 152 153 72 360 ≤ 1213149993503118 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4727 c22250R_152_22 (by norm_num)

theorem c22250R_152_20 : rowsJ2 152 153 71 360 ≤ 1218851522384021 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4726 c22250R_152_21 (by norm_num)

theorem c22250R_152_19 : rowsJ2 152 153 70 360 ≤ 1225362966114800 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4725 c22250R_152_20 (by norm_num)

theorem c22250R_152_18 : rowsJ2 152 153 69 360 ≤ 1232743145347750 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4724 c22250R_152_19 (by norm_num)

theorem c22250R_152_17 : rowsJ2 152 153 68 360 ≤ 1241052159434732 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4723 c22250R_152_18 (by norm_num)

theorem c22250R_152_16 : rowsJ2 152 153 67 360 ≤ 1250351482040876 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4722 c22250R_152_17 (by norm_num)

theorem c22250R_152_15 : rowsJ2 152 153 66 360 ≤ 1260704060751833 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4721 c22250R_152_16 (by norm_num)

theorem c22250R_152_14 : rowsJ2 152 153 65 360 ≤ 1272158284806081 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4720 c22250R_152_15 (by norm_num)

theorem c22250R_152_13 : rowsJ2 152 153 64 360 ≤ 1284780651113953 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4719 c22250R_152_14 (by norm_num)

theorem c22250R_152_12 : rowsJ2 152 153 63 360 ≤ 1296454388854248 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4718 c22250R_152_13 (by norm_num)

theorem c22250R_152_11 : rowsJ2 152 153 62 360 ≤ 1307177368104848 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4717 c22250R_152_12 (by norm_num)

theorem c22250R_152_10 : rowsJ2 152 153 61 360 ≤ 1316980269849028 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4716 c22250R_152_11 (by norm_num)

theorem c22250R_152_9 : rowsJ2 152 153 60 360 ≤ 1325894683512653 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4715 c22250R_152_10 (by norm_num)

theorem c22250R_152_8 : rowsJ2 152 153 59 360 ≤ 1333953195877996 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4714 c22250R_152_9 (by norm_num)

theorem c22250R_152_7 : rowsJ2 152 153 58 360 ≤ 1341189484095759 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4713 c22250R_152_8 (by norm_num)

theorem c22250R_152_6 : rowsJ2 152 153 57 360 ≤ 1347638413197693 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4712 c22250R_152_7 (by norm_num)

theorem c22250R_152_5 : rowsJ2 152 153 56 360 ≤ 1353336138537264 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4711 c22250R_152_6 (by norm_num)

theorem c22250R_152_4 : rowsJ2 152 153 55 360 ≤ 1358320213613408 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4710 c22250R_152_5 (by norm_num)

theorem c22250R_152_3 : rowsJ2 152 153 53 360 ≤ 1366305306246772 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4709 c22250R_152_4 (by norm_num)

theorem c22250R_152_2 : rowsJ2 152 153 50 360 ≤ 1373962960267727 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4708 c22250R_152_3 (by norm_num)

theorem c22250R_152_1 : rowsJ2 152 153 26 360 ≤ 1378597109296034 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4707 c22250R_152_2 (by norm_num)

theorem c22250R_152_0 : rowsJ2 152 153 0 360 ≤ 1379461956019902 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22250R_4706 c22250R_152_1 (by norm_num)

theorem hr22250R_152 : rows2 152 153 ≤ 1379461956019902 := rows2_le_of_rowsJ2 152 153 c22250R_152_0

theorem c22250R_153_27 : rowsJ2 153 154 80 360 ≤ 1228591789153036 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4761 rows22250R_4762 (by norm_num)

theorem c22250R_153_26 : rowsJ2 153 154 77 360 ≤ 1232876198620632 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4760 c22250R_153_27 (by norm_num)

theorem c22250R_153_25 : rowsJ2 153 154 75 360 ≤ 1237943013100588 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4759 c22250R_153_26 (by norm_num)

theorem c22250R_153_24 : rowsJ2 153 154 74 360 ≤ 1241299950695452 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4758 c22250R_153_25 (by norm_num)

theorem c22250R_153_23 : rowsJ2 153 154 73 360 ≤ 1245278968467364 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4757 c22250R_153_24 (by norm_num)

theorem c22250R_153_22 : rowsJ2 153 154 72 360 ≤ 1249935977844219 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4756 c22250R_153_23 (by norm_num)

theorem c22250R_153_21 : rowsJ2 153 154 71 360 ≤ 1255327883490766 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4755 c22250R_153_22 (by norm_num)

theorem c22250R_153_20 : rowsJ2 153 154 70 360 ≤ 1261512669759166 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4754 c22250R_153_21 (by norm_num)

theorem c22250R_153_19 : rowsJ2 153 154 69 360 ≤ 1268549490104434 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4753 c22250R_153_20 (by norm_num)

theorem c22250R_153_18 : rowsJ2 153 154 68 360 ≤ 1276498759775593 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4752 c22250R_153_19 (by norm_num)

theorem c22250R_153_17 : rowsJ2 153 154 67 360 ≤ 1285422252111163 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4751 c22250R_153_18 (by norm_num)

theorem c22250R_153_16 : rowsJ2 153 154 66 360 ≤ 1295383198787924 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4750 c22250R_153_17 (by norm_num)

theorem c22250R_153_15 : rowsJ2 153 154 65 360 ≤ 1306446394394280 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4749 c22250R_153_16 (by norm_num)

theorem c22250R_153_14 : rowsJ2 153 154 64 360 ≤ 1318678305724822 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4748 c22250R_153_15 (by norm_num)

theorem c22250R_153_13 : rowsJ2 153 154 63 360 ≤ 1331018657193770 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4747 c22250R_153_14 (by norm_num)

theorem c22250R_153_12 : rowsJ2 153 154 62 360 ≤ 1342378721851120 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4746 c22250R_153_13 (by norm_num)

theorem c22250R_153_11 : rowsJ2 153 154 61 360 ≤ 1352789174830119 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4745 c22250R_153_12 (by norm_num)

theorem c22250R_153_10 : rowsJ2 153 154 60 360 ≤ 1362281566631055 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4744 c22250R_153_11 (by norm_num)

theorem c22250R_153_9 : rowsJ2 153 154 59 360 ≤ 1370888412160943 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4743 c22250R_153_10 (by norm_num)

theorem c22250R_153_8 : rowsJ2 153 154 58 360 ≤ 1378643283769563 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4742 c22250R_153_9 (by norm_num)

theorem c22250R_153_7 : rowsJ2 153 154 57 360 ≤ 1385580908685880 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4741 c22250R_153_8 (by norm_num)

theorem c22250R_153_6 : rowsJ2 153 154 56 360 ≤ 1391737271283352 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4740 c22250R_153_7 (by norm_num)

theorem c22250R_153_5 : rowsJ2 153 154 55 360 ≤ 1397149720629514 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4739 c22250R_153_6 (by norm_num)

theorem c22250R_153_4 : rowsJ2 153 154 54 360 ≤ 1401857083805986 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4738 c22250R_153_5 (by norm_num)

theorem c22250R_153_3 : rowsJ2 153 154 52 360 ≤ 1409319974555402 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4737 c22250R_153_4 (by norm_num)

theorem c22250R_153_2 : rowsJ2 153 154 50 360 ≤ 1414470841685194 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4736 c22250R_153_3 (by norm_num)

theorem c22250R_153_1 : rowsJ2 153 154 28 360 ≤ 1420084069734600 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4735 c22250R_153_2 (by norm_num)

theorem c22250R_153_0 : rowsJ2 153 154 0 360 ≤ 1420586925112090 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22250R_4734 c22250R_153_1 (by norm_num)

theorem hr22250R_153 : rows2 153 154 ≤ 1420586925112090 := rows2_le_of_rowsJ2 153 154 c22250R_153_0

theorem c22250R_154_26 : rowsJ2 154 155 78 360 ≤ 1353620005638433 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4789 rows22250R_4790 (by norm_num)

theorem c22250R_154_25 : rowsJ2 154 155 76 360 ≤ 1357337156474567 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4788 c22250R_154_26 (by norm_num)

theorem c22250R_154_24 : rowsJ2 154 155 74 360 ≤ 1363029335821310 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4787 c22250R_154_25 (by norm_num)

theorem c22250R_154_23 : rowsJ2 154 155 73 360 ≤ 1366753162430129 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4786 c22250R_154_24 (by norm_num)

theorem c22250R_154_22 : rowsJ2 154 155 72 360 ≤ 1371136946246415 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4785 c22250R_154_23 (by norm_num)

theorem c22250R_154_21 : rowsJ2 154 155 71 360 ≤ 1376237982066322 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4784 c22250R_154_22 (by norm_num)

theorem c22250R_154_20 : rowsJ2 154 155 70 360 ≤ 1382114625241164 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4783 c22250R_154_21 (by norm_num)

theorem c22250R_154_19 : rowsJ2 154 155 69 360 ≤ 1388826381916467 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4782 c22250R_154_20 (by norm_num)

theorem c22250R_154_18 : rowsJ2 154 155 68 360 ≤ 1396434002497911 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4781 c22250R_154_19 (by norm_num)

theorem c22250R_154_17 : rowsJ2 154 155 67 360 ≤ 1404999578676051 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4780 c22250R_154_18 (by norm_num)

theorem c22250R_154_16 : rowsJ2 154 155 66 360 ≤ 1414586644361492 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4779 c22250R_154_17 (by norm_num)

theorem c22250R_154_15 : rowsJ2 154 155 65 360 ≤ 1425260280904533 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4778 c22250R_154_16 (by norm_num)

theorem c22250R_154_14 : rowsJ2 154 155 64 360 ≤ 1437087226998355 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4777 c22250R_154_15 (by norm_num)

theorem c22250R_154_13 : rowsJ2 154 155 63 360 ≤ 1450135993692590 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4776 c22250R_154_14 (by norm_num)

theorem c22250R_154_12 : rowsJ2 154 155 62 360 ≤ 1462174515440066 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4775 c22250R_154_13 (by norm_num)

theorem c22250R_154_11 : rowsJ2 154 155 61 360 ≤ 1473233486192760 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4774 c22250R_154_12 (by norm_num)

theorem c22250R_154_10 : rowsJ2 154 155 60 360 ≤ 1483344441245192 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4773 c22250R_154_11 (by norm_num)

theorem c22250R_154_9 : rowsJ2 154 155 59 360 ≤ 1492539846476143 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4772 c22250R_154_10 (by norm_num)

theorem c22250R_154_8 : rowsJ2 154 155 58 360 ≤ 1500853191479782 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4771 c22250R_154_9 (by norm_num)

theorem c22250R_154_7 : rowsJ2 154 155 57 360 ≤ 1508319086992586 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4770 c22250R_154_8 (by norm_num)

theorem c22250R_154_6 : rowsJ2 154 155 56 360 ≤ 1514973367045692 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4769 c22250R_154_7 (by norm_num)

theorem c22250R_154_5 : rowsJ2 154 155 55 360 ≤ 1520853196299227 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4768 c22250R_154_6 (by norm_num)

theorem c22250R_154_4 : rowsJ2 154 155 54 360 ≤ 1525997183044762 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4767 c22250R_154_5 (by norm_num)

theorem c22250R_154_3 : rowsJ2 154 155 52 360 ≤ 1534240002219790 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4766 c22250R_154_4 (by norm_num)

theorem c22250R_154_2 : rowsJ2 154 155 50 360 ≤ 1540044266182964 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4765 c22250R_154_3 (by norm_num)

theorem c22250R_154_1 : rowsJ2 154 155 43 360 ≤ 1546898324434086 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4764 c22250R_154_2 (by norm_num)

theorem c22250R_154_0 : rowsJ2 154 155 0 360 ≤ 1547316708262176 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22250R_4763 c22250R_154_1 (by norm_num)

theorem hr22250R_154 : rows2 154 155 ≤ 1547316708262176 := rows2_le_of_rowsJ2 154 155 c22250R_154_0

theorem c22250R_155_27 : rowsJ2 155 156 79 360 ≤ 1474294492528843 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4818 rows22250R_4819 (by norm_num)

theorem c22250R_155_26 : rowsJ2 155 156 76 360 ≤ 1478710683028330 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4817 c22250R_155_27 (by norm_num)

theorem c22250R_155_25 : rowsJ2 155 156 74 360 ≤ 1483933552103381 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4816 c22250R_155_26 (by norm_num)

theorem c22250R_155_24 : rowsJ2 155 156 73 360 ≤ 1487394010638230 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4815 c22250R_155_25 (by norm_num)

theorem c22250R_155_23 : rowsJ2 155 156 72 360 ≤ 1491495864389887 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4814 c22250R_155_24 (by norm_num)

theorem c22250R_155_22 : rowsJ2 155 156 71 360 ≤ 1496296816706921 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4813 c22250R_155_23 (by norm_num)

theorem c22250R_155_21 : rowsJ2 155 156 70 360 ≤ 1501855611484348 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4812 c22250R_155_22 (by norm_num)

theorem c22250R_155_20 : rowsJ2 155 156 69 360 ≤ 1508232124279068 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4811 c22250R_155_21 (by norm_num)

theorem c22250R_155_19 : rowsJ2 155 156 68 360 ≤ 1515487456600359 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4810 c22250R_155_20 (by norm_num)

theorem c22250R_155_18 : rowsJ2 155 156 67 360 ≤ 1523684033710401 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4809 c22250R_155_19 (by norm_num)

theorem c22250R_155_17 : rowsJ2 155 156 66 360 ≤ 1532885706290026 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4808 c22250R_155_18 (by norm_num)

theorem c22250R_155_16 : rowsJ2 155 156 65 360 ≤ 1543157856346146 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4807 c22250R_155_17 (by norm_num)

theorem c22250R_155_15 : rowsJ2 155 156 64 360 ≤ 1554567507762944 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4806 c22250R_155_16 (by norm_num)

theorem c22250R_155_14 : rowsJ2 155 156 63 360 ≤ 1567183441925893 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4805 c22250R_155_15 (by norm_num)

theorem c22250R_155_13 : rowsJ2 155 156 62 360 ≤ 1579912221133375 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4804 c22250R_155_14 (by norm_num)

theorem c22250R_155_12 : rowsJ2 155 156 61 360 ≤ 1591630801633992 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4803 c22250R_155_13 (by norm_num)

theorem c22250R_155_11 : rowsJ2 155 156 60 360 ≤ 1602370723440031 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4802 c22250R_155_12 (by norm_num)

theorem c22250R_155_10 : rowsJ2 155 156 59 360 ≤ 1612164422233537 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4801 c22250R_155_11 (by norm_num)

theorem c22250R_155_9 : rowsJ2 155 156 58 360 ≤ 1621045322664489 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4800 c22250R_155_10 (by norm_num)

theorem c22250R_155_8 : rowsJ2 155 156 57 360 ≤ 1629047935834614 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4799 c22250R_155_9 (by norm_num)

theorem c22250R_155_7 : rowsJ2 155 156 56 360 ≤ 1636207961398606 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4798 c22250R_155_8 (by norm_num)

theorem c22250R_155_6 : rowsJ2 155 156 55 360 ≤ 1642562394740511 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4797 c22250R_155_7 (by norm_num)

theorem c22250R_155_5 : rowsJ2 155 156 54 360 ≤ 1648149639712066 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4796 c22250R_155_6 (by norm_num)

theorem c22250R_155_4 : rowsJ2 155 156 53 360 ≤ 1653009627452475 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4795 c22250R_155_5 (by norm_num)

theorem c22250R_155_3 : rowsJ2 155 156 52 360 ≤ 1657183941845377 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4794 c22250R_155_4 (by norm_num)

theorem c22250R_155_2 : rowsJ2 155 156 50 360 ≤ 1663650953863057 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4793 c22250R_155_3 (by norm_num)

theorem c22250R_155_1 : rowsJ2 155 156 44 360 ≤ 1671542631117491 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4792 c22250R_155_2 (by norm_num)

theorem c22250R_155_0 : rowsJ2 155 156 0 360 ≤ 1671966694972261 :=
  rowsJ2_le_of_split 155 156 (by norm_num) (by norm_num) rows22250R_4791 c22250R_155_1 (by norm_num)

theorem hr22250R_155 : rows2 155 156 ≤ 1671966694972261 := rows2_le_of_rowsJ2 155 156 c22250R_155_0

theorem c22250R_156_26 : rowsJ2 156 157 78 360 ≤ 1582158669647424 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4846 rows22250R_4847 (by norm_num)

theorem c22250R_156_25 : rowsJ2 156 157 75 360 ≤ 1587282333041489 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4845 c22250R_156_26 (by norm_num)

theorem c22250R_156_24 : rowsJ2 156 157 73 360 ≤ 1593151398942626 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4844 c22250R_156_25 (by norm_num)

theorem c22250R_156_23 : rowsJ2 156 157 72 360 ≤ 1596991102905873 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4843 c22250R_156_24 (by norm_num)

theorem c22250R_156_22 : rowsJ2 156 157 71 360 ≤ 1601511457498549 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4842 c22250R_156_23 (by norm_num)

theorem c22250R_156_21 : rowsJ2 156 157 70 360 ≤ 1606771617500174 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4841 c22250R_156_22 (by norm_num)

theorem c22250R_156_20 : rowsJ2 156 157 69 360 ≤ 1612831849443391 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4840 c22250R_156_21 (by norm_num)

theorem c22250R_156_19 : rowsJ2 156 157 68 360 ≤ 1619753626785294 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4839 c22250R_156_20 (by norm_num)

theorem c22250R_156_18 : rowsJ2 156 157 67 360 ≤ 1627599728537240 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4838 c22250R_156_19 (by norm_num)

theorem c22250R_156_17 : rowsJ2 156 157 66 360 ≤ 1636434341711490 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4837 c22250R_156_18 (by norm_num)

theorem c22250R_156_16 : rowsJ2 156 157 65 360 ≤ 1646323167964605 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4836 c22250R_156_17 (by norm_num)

theorem c22250R_156_15 : rowsJ2 156 157 64 360 ≤ 1657333534842245 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4835 c22250R_156_16 (by norm_num)

theorem c22250R_156_14 : rowsJ2 156 157 63 360 ≤ 1669534512057460 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4834 c22250R_156_15 (by norm_num)

theorem c22250R_156_13 : rowsJ2 156 157 62 360 ≤ 1682997033265224 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4833 c22250R_156_14 (by norm_num)

theorem c22250R_156_12 : rowsJ2 156 157 61 360 ≤ 1695418247224183 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4832 c22250R_156_13 (by norm_num)

theorem c22250R_156_11 : rowsJ2 156 157 60 360 ≤ 1706829724954232 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4831 c22250R_156_12 (by norm_num)

theorem c22250R_156_10 : rowsJ2 156 157 59 360 ≤ 1717263897189579 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4830 c22250R_156_11 (by norm_num)

theorem c22250R_156_9 : rowsJ2 156 157 58 360 ≤ 1726754147927356 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4829 c22250R_156_10 (by norm_num)

theorem c22250R_156_8 : rowsJ2 156 157 57 360 ≤ 1735334912046203 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4828 c22250R_156_9 (by norm_num)

theorem c22250R_156_7 : rowsJ2 156 157 56 360 ≤ 1743041777429121 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4827 c22250R_156_8 (by norm_num)

theorem c22250R_156_6 : rowsJ2 156 157 55 360 ≤ 1749911592050053 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4826 c22250R_156_7 (by norm_num)

theorem c22250R_156_5 : rowsJ2 156 157 54 360 ≤ 1755982576512230 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4825 c22250R_156_6 (by norm_num)

theorem c22250R_156_4 : rowsJ2 156 157 53 360 ≤ 1761294442558004 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4824 c22250R_156_5 (by norm_num)

theorem c22250R_156_3 : rowsJ2 156 157 51 360 ≤ 1769807879409151 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4823 c22250R_156_4 (by norm_num)

theorem c22250R_156_2 : rowsJ2 156 157 49 360 ≤ 1775804353954147 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4822 c22250R_156_3 (by norm_num)

theorem c22250R_156_1 : rowsJ2 156 157 45 360 ≤ 1781824735360931 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4821 c22250R_156_2 (by norm_num)

theorem c22250R_156_0 : rowsJ2 156 157 0 360 ≤ 1783058224340954 :=
  rowsJ2_le_of_split 156 157 (by norm_num) (by norm_num) rows22250R_4820 c22250R_156_1 (by norm_num)

theorem hr22250R_156 : rows2 156 157 ≤ 1783058224340954 := rows2_le_of_rowsJ2 156 157 c22250R_156_0

theorem c22250R_157_26 : rowsJ2 157 158 76 360 ≤ 1697147919432742 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4874 rows22250R_4875 (by norm_num)

theorem c22250R_157_25 : rowsJ2 157 158 74 360 ≤ 1701500486404155 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4873 c22250R_157_26 (by norm_num)

theorem c22250R_157_24 : rowsJ2 157 158 72 360 ≤ 1708035411709524 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4872 c22250R_157_25 (by norm_num)

theorem c22250R_157_23 : rowsJ2 157 158 71 360 ≤ 1712266057874895 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4871 c22250R_157_24 (by norm_num)

theorem c22250R_157_22 : rowsJ2 157 158 70 360 ≤ 1717217940429100 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4870 c22250R_157_23 (by norm_num)

theorem c22250R_157_21 : rowsJ2 157 158 69 360 ≤ 1722951735287021 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4869 c22250R_157_22 (by norm_num)

theorem c22250R_157_20 : rowsJ2 157 158 68 360 ≤ 1729529305385431 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4868 c22250R_157_21 (by norm_num)

theorem c22250R_157_19 : rowsJ2 157 158 67 360 ≤ 1737013800195166 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4867 c22250R_157_20 (by norm_num)

theorem c22250R_157_18 : rowsJ2 157 158 66 360 ≤ 1745469758998661 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4866 c22250R_157_19 (by norm_num)

theorem c22250R_157_17 : rowsJ2 157 158 65 360 ≤ 1754963218316259 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4865 c22250R_157_18 (by norm_num)

theorem c22250R_157_16 : rowsJ2 157 158 64 360 ≤ 1765561823889092 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4864 c22250R_157_17 (by norm_num)

theorem c22250R_157_15 : rowsJ2 157 158 63 360 ≤ 1777334947653476 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4863 c22250R_157_16 (by norm_num)

theorem c22250R_157_14 : rowsJ2 157 158 62 360 ≤ 1790353810172355 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4862 c22250R_157_15 (by norm_num)

theorem c22250R_157_13 : rowsJ2 157 158 61 360 ≤ 1803490172783141 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4861 c22250R_157_14 (by norm_num)

theorem c22250R_157_12 : rowsJ2 157 158 60 360 ≤ 1815584970277457 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4860 c22250R_157_13 (by norm_num)

theorem c22250R_157_11 : rowsJ2 157 158 59 360 ≤ 1826670649747177 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4859 c22250R_157_12 (by norm_num)

theorem c22250R_157_10 : rowsJ2 157 158 58 360 ≤ 1836780574648726 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4858 c22250R_157_11 (by norm_num)

theorem c22250R_157_9 : rowsJ2 157 158 57 360 ≤ 1845949122635351 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4857 c22250R_157_10 (by norm_num)

theorem c22250R_157_8 : rowsJ2 157 158 56 360 ≤ 1854211787774494 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4856 c22250R_157_9 (by norm_num)

theorem c22250R_157_7 : rowsJ2 157 158 55 360 ≤ 1861605287612171 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4855 c22250R_157_8 (by norm_num)

theorem c22250R_157_6 : rowsJ2 157 158 54 360 ≤ 1868167675573928 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4854 c22250R_157_7 (by norm_num)

theorem c22250R_157_5 : rowsJ2 157 158 53 360 ≤ 1873938459222983 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4853 c22250R_157_6 (by norm_num)

theorem c22250R_157_4 : rowsJ2 157 158 52 360 ≤ 1878958724931315 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4852 c22250R_157_5 (by norm_num)

theorem c22250R_157_3 : rowsJ2 157 158 51 360 ≤ 1883271269558480 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4851 c22250R_157_4 (by norm_num)

theorem c22250R_157_2 : rowsJ2 157 158 49 360 ≤ 1889953779727474 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4850 c22250R_157_3 (by norm_num)

theorem c22250R_157_1 : rowsJ2 157 158 45 360 ≤ 1896933491547423 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4849 c22250R_157_2 (by norm_num)

theorem c22250R_157_0 : rowsJ2 157 158 0 360 ≤ 1898417049523820 :=
  rowsJ2_le_of_split 157 158 (by norm_num) (by norm_num) rows22250R_4848 c22250R_157_1 (by norm_num)

theorem hr22250R_157 : rows2 157 158 ≤ 1898417049523820 := rows2_le_of_rowsJ2 157 158 c22250R_157_0

theorem c22250R_158_26 : rowsJ2 158 159 77 360 ≤ 1806730221761656 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4902 rows22250R_4903 (by norm_num)

theorem c22250R_158_25 : rowsJ2 158 159 74 360 ≤ 1812015574083081 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4901 c22250R_158_26 (by norm_num)

theorem c22250R_158_24 : rowsJ2 158 159 72 360 ≤ 1818070133075551 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4900 c22250R_158_25 (by norm_num)

theorem c22250R_158_23 : rowsJ2 158 159 71 360 ≤ 1822031358901963 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4899 c22250R_158_24 (by norm_num)

theorem c22250R_158_22 : rowsJ2 158 159 70 360 ≤ 1826694943344986 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4898 c22250R_158_23 (by norm_num)

theorem c22250R_158_21 : rowsJ2 158 159 69 360 ≤ 1832121995154320 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4897 c22250R_158_22 (by norm_num)

theorem c22250R_158_20 : rowsJ2 158 159 68 360 ≤ 1838374789373720 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4896 c22250R_158_21 (by norm_num)

theorem c22250R_158_19 : rowsJ2 158 159 67 360 ≤ 1845516867795771 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4895 c22250R_158_20 (by norm_num)

theorem c22250R_158_18 : rowsJ2 158 159 66 360 ≤ 1853613143127331 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4894 c22250R_158_19 (by norm_num)

theorem c22250R_158_17 : rowsJ2 158 159 65 360 ≤ 1862730007252796 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4893 c22250R_158_18 (by norm_num)

theorem c22250R_158_16 : rowsJ2 158 159 64 360 ≤ 1872935444006356 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4892 c22250R_158_17 (by norm_num)

theorem c22250R_158_15 : rowsJ2 158 159 63 360 ≤ 1884299146891276 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4891 c22250R_158_16 (by norm_num)

theorem c22250R_158_14 : rowsJ2 158 159 62 360 ≤ 1896892642214878 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4890 c22250R_158_15 (by norm_num)

theorem c22250R_158_13 : rowsJ2 158 159 61 360 ≤ 1910789418141382 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4889 c22250R_158_14 (by norm_num)

theorem c22250R_158_12 : rowsJ2 158 159 60 360 ≤ 1923612305804956 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4888 c22250R_158_13 (by norm_num)

theorem c22250R_158_11 : rowsJ2 158 159 59 360 ≤ 1935393796709924 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4887 c22250R_158_12 (by norm_num)

theorem c22250R_158_10 : rowsJ2 158 159 58 360 ≤ 1946167260683999 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4886 c22250R_158_11 (by norm_num)

theorem c22250R_158_9 : rowsJ2 158 159 57 360 ≤ 1955967044015871 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4885 c22250R_158_10 (by norm_num)

theorem c22250R_158_8 : rowsJ2 158 159 56 360 ≤ 1964828571852380 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4884 c22250R_158_9 (by norm_num)

theorem c22250R_158_7 : rowsJ2 158 159 55 360 ≤ 1972788455320392 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4883 c22250R_158_8 (by norm_num)

theorem c22250R_158_6 : rowsJ2 158 159 54 360 ≤ 1979884603864776 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4882 c22250R_158_7 (by norm_num)

theorem c22250R_158_5 : rowsJ2 158 159 53 360 ≤ 1986156343324755 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4881 c22250R_158_6 (by norm_num)

theorem c22250R_158_4 : rowsJ2 158 159 52 360 ≤ 1991644540304933 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4880 c22250R_158_5 (by norm_num)

theorem c22250R_158_3 : rowsJ2 158 159 51 360 ≤ 1996391733435609 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4879 c22250R_158_4 (by norm_num)

theorem c22250R_158_2 : rowsJ2 158 159 49 360 ≤ 2003842463732912 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4878 c22250R_158_3 (by norm_num)

theorem c22250R_158_1 : rowsJ2 158 159 45 360 ≤ 2011943440081307 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4877 c22250R_158_2 (by norm_num)

theorem c22250R_158_0 : rowsJ2 158 159 0 360 ≤ 2014007391076656 :=
  rowsJ2_le_of_split 158 159 (by norm_num) (by norm_num) rows22250R_4876 c22250R_158_1 (by norm_num)

theorem hr22250R_158 : rows2 158 159 ≤ 2014007391076656 := rows2_le_of_rowsJ2 158 159 c22250R_158_0

theorem c22250R_159_25 : rowsJ2 159 160 75 360 ≤ 1912520351390343 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4929 rows22250R_4930 (by norm_num)

theorem c22250R_159_24 : rowsJ2 159 160 73 360 ≤ 1917011488981880 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4928 c22250R_159_25 (by norm_num)

theorem c22250R_159_23 : rowsJ2 159 160 71 360 ≤ 1923754784079524 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4927 c22250R_159_24 (by norm_num)

theorem c22250R_159_22 : rowsJ2 159 160 70 360 ≤ 1928120530764437 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4926 c22250R_159_23 (by norm_num)

theorem c22250R_159_21 : rowsJ2 159 160 69 360 ≤ 1933230743938320 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4925 c22250R_159_22 (by norm_num)

theorem c22250R_159_20 : rowsJ2 159 160 68 360 ≤ 1939148130076533 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4924 c22250R_159_21 (by norm_num)

theorem c22250R_159_19 : rowsJ2 159 160 67 360 ≤ 1945936641688769 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4923 c22250R_159_20 (by norm_num)

theorem c22250R_159_18 : rowsJ2 159 160 66 360 ≤ 1953661582429263 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4922 c22250R_159_19 (by norm_num)

theorem c22250R_159_17 : rowsJ2 159 160 65 360 ≤ 1962389716250424 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4921 c22250R_159_18 (by norm_num)

theorem c22250R_159_16 : rowsJ2 159 160 64 360 ≤ 1972189381014641 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4920 c22250R_159_17 (by norm_num)

theorem c22250R_159_15 : rowsJ2 159 160 63 360 ≤ 1983130607006010 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4919 c22250R_159_16 (by norm_num)

theorem c22250R_159_14 : rowsJ2 159 160 62 360 ≤ 1995285240813554 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4918 c22250R_159_15 (by norm_num)

theorem c22250R_159_13 : rowsJ2 159 160 61 360 ≤ 2008727075091252 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4917 c22250R_159_14 (by norm_num)

theorem c22250R_159_12 : rowsJ2 159 160 60 360 ≤ 2022291331847351 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4916 c22250R_159_13 (by norm_num)

theorem c22250R_159_11 : rowsJ2 159 160 59 360 ≤ 2034781115678908 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4915 c22250R_159_12 (by norm_num)

theorem c22250R_159_10 : rowsJ2 159 160 58 360 ≤ 2046229825600920 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4914 c22250R_159_11 (by norm_num)

theorem c22250R_159_9 : rowsJ2 159 160 57 360 ≤ 2056671798048200 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4913 c22250R_159_10 (by norm_num)

theorem c22250R_159_8 : rowsJ2 159 160 56 360 ≤ 2066142409539276 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4912 c22250R_159_9 (by norm_num)

theorem c22250R_159_7 : rowsJ2 159 160 55 360 ≤ 2074678183935669 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4911 c22250R_159_8 (by norm_num)

theorem c22250R_159_6 : rowsJ2 159 160 54 360 ≤ 2082316904791014 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4910 c22250R_159_7 (by norm_num)

theorem c22250R_159_5 : rowsJ2 159 160 53 360 ≤ 2089097733314246 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4909 c22250R_159_6 (by norm_num)

theorem c22250R_159_4 : rowsJ2 159 160 52 360 ≤ 2095061332504090 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4908 c22250R_159_5 (by norm_num)

theorem c22250R_159_3 : rowsJ2 159 160 51 360 ≤ 2100249998050033 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4907 c22250R_159_4 (by norm_num)

theorem c22250R_159_2 : rowsJ2 159 160 49 360 ≤ 2108480712336303 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4906 c22250R_159_3 (by norm_num)

theorem c22250R_159_1 : rowsJ2 159 160 45 360 ≤ 2117719304569996 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4905 c22250R_159_2 (by norm_num)

theorem c22250R_159_0 : rowsJ2 159 160 0 360 ≤ 2120371540269875 :=
  rowsJ2_le_of_split 159 160 (by norm_num) (by norm_num) rows22250R_4904 c22250R_159_1 (by norm_num)

theorem hr22250R_159 : rows2 159 160 ≤ 2120371540269875 := rows2_le_of_rowsJ2 159 160 c22250R_159_0

theorem c22250R_160_25 : rowsJ2 160 161 73 360 ≤ 2025113759465121 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4956 rows22250R_4957 (by norm_num)

theorem c22250R_160_24 : rowsJ2 160 161 71 360 ≤ 2031362928421493 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4955 c22250R_160_25 (by norm_num)

theorem c22250R_160_23 : rowsJ2 160 161 70 360 ≤ 2035451655796192 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4954 c22250R_160_24 (by norm_num)

theorem c22250R_160_22 : rowsJ2 160 161 69 360 ≤ 2040265525077434 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4953 c22250R_160_23 (by norm_num)

theorem c22250R_160_21 : rowsJ2 160 161 68 360 ≤ 2045867698809317 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4952 c22250R_160_22 (by norm_num)

theorem c22250R_160_20 : rowsJ2 160 161 67 360 ≤ 2052322563978135 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4951 c22250R_160_21 (by norm_num)

theorem c22250R_160_19 : rowsJ2 160 161 66 360 ≤ 2059695838131880 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4950 c22250R_160_20 (by norm_num)

theorem c22250R_160_18 : rowsJ2 160 161 65 360 ≤ 2068054679485191 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4949 c22250R_160_19 (by norm_num)

theorem c22250R_160_17 : rowsJ2 160 161 64 360 ≤ 2077467801428599 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4948 c22250R_160_18 (by norm_num)

theorem c22250R_160_16 : rowsJ2 160 161 63 360 ≤ 2088005591887448 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4947 c22250R_160_17 (by norm_num)

theorem c22250R_160_15 : rowsJ2 160 161 62 360 ≤ 2099740238005544 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4946 c22250R_160_16 (by norm_num)

theorem c22250R_160_14 : rowsJ2 160 161 61 360 ≤ 2112745856662128 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4945 c22250R_160_15 (by norm_num)

theorem c22250R_160_13 : rowsJ2 160 161 60 360 ≤ 2127098631368205 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4944 c22250R_160_14 (by norm_num)

theorem c22250R_160_12 : rowsJ2 160 161 59 360 ≤ 2140343326658677 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4943 c22250R_160_13 (by norm_num)

theorem c22250R_160_11 : rowsJ2 160 161 58 360 ≤ 2152513400714468 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4942 c22250R_160_12 (by norm_num)

theorem c22250R_160_10 : rowsJ2 160 161 57 360 ≤ 2163643208839564 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4941 c22250R_160_11 (by norm_num)

theorem c22250R_160_9 : rowsJ2 160 161 56 360 ≤ 2173768106492344 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4940 c22250R_160_10 (by norm_num)

theorem c22250R_160_8 : rowsJ2 160 161 55 360 ≤ 2182924556776039 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4939 c22250R_160_9 (by norm_num)

theorem c22250R_160_7 : rowsJ2 160 161 54 360 ≤ 2191150242886328 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4938 c22250R_160_8 (by norm_num)

theorem c22250R_160_6 : rowsJ2 160 161 53 360 ≤ 2198484186042692 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4937 c22250R_160_7 (by norm_num)

theorem c22250R_160_5 : rowsJ2 160 161 52 360 ≤ 2204966869462841 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4936 c22250R_160_6 (by norm_num)

theorem c22250R_160_4 : rowsJ2 160 161 51 360 ≤ 2210640368976008 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4935 c22250R_160_5 (by norm_num)

theorem c22250R_160_3 : rowsJ2 160 161 50 360 ≤ 2215548490912273 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4934 c22250R_160_4 (by norm_num)

theorem c22250R_160_2 : rowsJ2 160 161 48 360 ≤ 2223253363664428 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4933 c22250R_160_3 (by norm_num)

theorem c22250R_160_1 : rowsJ2 160 161 45 360 ≤ 2230281929859836 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4932 c22250R_160_2 (by norm_num)

theorem c22250R_160_0 : rowsJ2 160 161 0 360 ≤ 2233770792991213 :=
  rowsJ2_le_of_split 160 161 (by norm_num) (by norm_num) rows22250R_4931 c22250R_160_1 (by norm_num)

theorem hr22250R_160 : rows2 160 161 ≤ 2233770792991213 := rows2_le_of_rowsJ2 160 161 c22250R_160_0

theorem c22250R_161_24 : rowsJ2 161 162 72 360 ≤ 2134519784868074 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4982 rows22250R_4983 (by norm_num)

theorem c22250R_161_23 : rowsJ2 161 162 70 360 ≤ 2141481747250670 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4981 c22250R_161_24 (by norm_num)

theorem c22250R_161_22 : rowsJ2 161 162 69 360 ≤ 2145989279731582 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4980 c22250R_161_23 (by norm_num)

theorem c22250R_161_21 : rowsJ2 161 162 68 360 ≤ 2151265666988133 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4979 c22250R_161_22 (by norm_num)

theorem c22250R_161_20 : rowsJ2 161 162 67 360 ≤ 2157375750786395 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4978 c22250R_161_21 (by norm_num)

theorem c22250R_161_19 : rowsJ2 161 162 66 360 ≤ 2164385681883461 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4977 c22250R_161_20 (by norm_num)

theorem c22250R_161_18 : rowsJ2 161 162 65 360 ≤ 2172363031144641 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4976 c22250R_161_19 (by norm_num)

theorem c22250R_161_17 : rowsJ2 161 162 64 360 ≤ 2181376905007273 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4975 c22250R_161_18 (by norm_num)

theorem c22250R_161_16 : rowsJ2 161 162 63 360 ≤ 2191498065740633 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4974 c22250R_161_17 (by norm_num)

theorem c22250R_161_15 : rowsJ2 161 162 62 360 ≤ 2202799056980707 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4973 c22250R_161_16 (by norm_num)

theorem c22250R_161_14 : rowsJ2 161 162 61 360 ≤ 2215354335052013 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4972 c22250R_161_15 (by norm_num)

theorem c22250R_161_13 : rowsJ2 161 162 60 360 ≤ 2229240406625625 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4971 c22250R_161_14 (by norm_num)

theorem c22250R_161_12 : rowsJ2 161 162 59 360 ≤ 2243254109007799 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4970 c22250R_161_13 (by norm_num)

theorem c22250R_161_11 : rowsJ2 161 162 58 360 ≤ 2256158795922557 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4969 c22250R_161_12 (by norm_num)

theorem c22250R_161_10 : rowsJ2 161 162 57 360 ≤ 2267988866011929 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4968 c22250R_161_11 (by norm_num)

theorem c22250R_161_9 : rowsJ2 161 162 56 360 ≤ 2278779676714080 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4967 c22250R_161_10 (by norm_num)

theorem c22250R_161_8 : rowsJ2 161 162 55 360 ≤ 2288567652080481 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4966 c22250R_161_9 (by norm_num)

theorem c22250R_161_7 : rowsJ2 161 162 54 360 ≤ 2297390395410026 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4965 c22250R_161_8 (by norm_num)

theorem c22250R_161_6 : rowsJ2 161 162 53 360 ≤ 2305286807230058 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4964 c22250R_161_7 (by norm_num)

theorem c22250R_161_5 : rowsJ2 161 162 52 360 ≤ 2312297209185705 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4963 c22250R_161_6 (by norm_num)

theorem c22250R_161_4 : rowsJ2 161 162 51 360 ≤ 2318463474435215 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4962 c22250R_161_5 (by norm_num)

theorem c22250R_161_3 : rowsJ2 161 162 50 360 ≤ 2323829165188705 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4961 c22250R_161_4 (by norm_num)

theorem c22250R_161_2 : rowsJ2 161 162 48 360 ≤ 2332342398059607 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4960 c22250R_161_3 (by norm_num)

theorem c22250R_161_1 : rowsJ2 161 162 44 360 ≤ 2341902076968839 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4959 c22250R_161_2 (by norm_num)

theorem c22250R_161_0 : rowsJ2 161 162 0 360 ≤ 2344648279476915 :=
  rowsJ2_le_of_split 161 162 (by norm_num) (by norm_num) rows22250R_4958 c22250R_161_1 (by norm_num)

theorem hr22250R_161 : rows2 161 162 ≤ 2344648279476915 := rows2_le_of_rowsJ2 161 162 c22250R_161_0

theorem c22250R_162_25 : rowsJ2 162 163 73 360 ≤ 2231042291247217 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_5009 rows22250R_5010 (by norm_num)

theorem c22250R_162_24 : rowsJ2 162 163 71 360 ≤ 2236314133398954 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_5008 c22250R_162_25 (by norm_num)

theorem c22250R_162_23 : rowsJ2 162 163 69 360 ≤ 2244074348408632 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_5007 c22250R_162_24 (by norm_num)

theorem c22250R_162_22 : rowsJ2 162 163 68 360 ≤ 2249045982314408 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_5006 c22250R_162_23 (by norm_num)

theorem c22250R_162_21 : rowsJ2 162 163 67 360 ≤ 2254832004366948 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_5005 c22250R_162_22 (by norm_num)

theorem c22250R_162_20 : rowsJ2 162 163 66 360 ≤ 2261499023498713 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_5004 c22250R_162_21 (by norm_num)

theorem c22250R_162_19 : rowsJ2 162 163 65 360 ≤ 2269115047327237 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_5003 c22250R_162_20 (by norm_num)

theorem c22250R_162_18 : rowsJ2 162 163 64 360 ≤ 2277749598638884 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_5002 c22250R_162_19 (by norm_num)

theorem c22250R_162_17 : rowsJ2 162 163 63 360 ≤ 2287473836611576 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_5001 c22250R_162_18 (by norm_num)

theorem c22250R_162_16 : rowsJ2 162 163 62 360 ≤ 2298360683259401 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_5000 c22250R_162_17 (by norm_num)

theorem c22250R_162_15 : rowsJ2 162 163 61 360 ≤ 2310484955615070 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4999 c22250R_162_16 (by norm_num)

theorem c22250R_162_14 : rowsJ2 162 163 60 360 ≤ 2323923504202870 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4998 c22250R_162_15 (by norm_num)

theorem c22250R_162_13 : rowsJ2 162 163 59 360 ≤ 2338755358396458 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4997 c22250R_162_14 (by norm_num)

theorem c22250R_162_12 : rowsJ2 162 163 58 360 ≤ 2352443233612366 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4996 c22250R_162_13 (by norm_num)

theorem c22250R_162_11 : rowsJ2 162 163 57 360 ≤ 2365021603909009 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4995 c22250R_162_12 (by norm_num)

theorem c22250R_162_10 : rowsJ2 162 163 56 360 ≤ 2376525859401806 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4994 c22250R_162_11 (by norm_num)

theorem c22250R_162_9 : rowsJ2 162 163 55 360 ≤ 2386992414518271 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4993 c22250R_162_10 (by norm_num)

theorem c22250R_162_8 : rowsJ2 162 163 54 360 ≤ 2396458820921703 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4992 c22250R_162_9 (by norm_num)

theorem c22250R_162_7 : rowsJ2 162 163 53 360 ≤ 2404963885637570 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4991 c22250R_162_8 (by norm_num)

theorem c22250R_162_6 : rowsJ2 162 163 52 360 ≤ 2412547794947344 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4990 c22250R_162_7 (by norm_num)

theorem c22250R_162_5 : rowsJ2 162 163 51 360 ≤ 2419252244649173 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4989 c22250R_162_6 (by norm_num)

theorem c22250R_162_4 : rowsJ2 162 163 50 360 ≤ 2425120577324531 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4988 c22250R_162_5 (by norm_num)

theorem c22250R_162_3 : rowsJ2 162 163 49 360 ≤ 2430197927293859 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4987 c22250R_162_4 (by norm_num)

theorem c22250R_162_2 : rowsJ2 162 163 47 360 ≤ 2438170104568184 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4986 c22250R_162_3 (by norm_num)

theorem c22250R_162_1 : rowsJ2 162 163 44 360 ≤ 2445445190016848 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4985 c22250R_162_2 (by norm_num)

theorem c22250R_162_0 : rowsJ2 162 163 0 360 ≤ 2449015884844151 :=
  rowsJ2_le_of_split 162 163 (by norm_num) (by norm_num) rows22250R_4984 c22250R_162_1 (by norm_num)

theorem hr22250R_162 : rows2 162 163 ≤ 2449015884844151 := rows2_le_of_rowsJ2 162 163 c22250R_162_0

theorem c22250R_163_24 : rowsJ2 163 164 71 360 ≤ 2340540708974664 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5035 rows22250R_5036 (by norm_num)

theorem c22250R_163_23 : rowsJ2 163 164 69 360 ≤ 2347732258678387 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5034 c22250R_163_24 (by norm_num)

theorem c22250R_163_22 : rowsJ2 163 164 68 360 ≤ 2352388667051269 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5033 c22250R_163_23 (by norm_num)

theorem c22250R_163_21 : rowsJ2 163 164 67 360 ≤ 2357839547462331 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5032 c22250R_163_22 (by norm_num)

theorem c22250R_163_20 : rowsJ2 163 164 66 360 ≤ 2364151988366166 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5031 c22250R_163_21 (by norm_num)

theorem c22250R_163_19 : rowsJ2 163 164 65 360 ≤ 2371394454428662 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5030 c22250R_163_20 (by norm_num)

theorem c22250R_163_18 : rowsJ2 163 164 64 360 ≤ 2379636904095966 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5029 c22250R_163_19 (by norm_num)

theorem c22250R_163_17 : rowsJ2 163 164 63 360 ≤ 2388950911841304 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5028 c22250R_163_18 (by norm_num)

theorem c22250R_163_16 : rowsJ2 163 164 62 360 ≤ 2399409795576995 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5027 c22250R_163_17 (by norm_num)

theorem c22250R_163_15 : rowsJ2 163 164 61 360 ≤ 2411088749751791 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5026 c22250R_163_16 (by norm_num)

theorem c22250R_163_14 : rowsJ2 163 164 60 360 ≤ 2424064984689980 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5025 c22250R_163_15 (by norm_num)

theorem c22250R_163_13 : rowsJ2 163 164 59 360 ≤ 2438417872770203 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5024 c22250R_163_14 (by norm_num)

theorem c22250R_163_12 : rowsJ2 163 164 58 360 ≤ 2452903906076848 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5023 c22250R_163_13 (by norm_num)

theorem c22250R_163_11 : rowsJ2 163 164 57 360 ≤ 2466244646285602 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5022 c22250R_163_12 (by norm_num)

theorem c22250R_163_10 : rowsJ2 163 164 56 360 ≤ 2478475542469012 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5021 c22250R_163_11 (by norm_num)

theorem c22250R_163_9 : rowsJ2 163 164 55 360 ≤ 2489633024144536 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5020 c22250R_163_10 (by norm_num)

theorem c22250R_163_8 : rowsJ2 163 164 54 360 ≤ 2499754614593280 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5019 c22250R_163_9 (by norm_num)

theorem c22250R_163_7 : rowsJ2 163 164 53 360 ≤ 2508879049228963 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5018 c22250R_163_8 (by norm_num)

theorem c22250R_163_6 : rowsJ2 163 164 52 360 ≤ 2517046399585507 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5017 c22250R_163_7 (by norm_num)

theorem c22250R_163_5 : rowsJ2 163 164 51 360 ≤ 2524298203525804 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5016 c22250R_163_6 (by norm_num)

theorem c22250R_163_4 : rowsJ2 163 164 50 360 ≤ 2530677602312401 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5015 c22250R_163_5 (by norm_num)

theorem c22250R_163_3 : rowsJ2 163 164 49 360 ≤ 2536229485224210 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5014 c22250R_163_4 (by norm_num)

theorem c22250R_163_2 : rowsJ2 163 164 47 360 ≤ 2545039927061467 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5013 c22250R_163_3 (by norm_num)

theorem c22250R_163_1 : rowsJ2 163 164 44 360 ≤ 2553289705164050 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5012 c22250R_163_2 (by norm_num)

theorem c22250R_163_0 : rowsJ2 163 164 0 360 ≤ 2557739297287099 :=
  rowsJ2_le_of_split 163 164 (by norm_num) (by norm_num) rows22250R_5011 c22250R_163_1 (by norm_num)

theorem hr22250R_163 : rows2 163 164 ≤ 2557739297287099 := rows2_le_of_rowsJ2 163 164 c22250R_163_0

theorem c22250R_164_24 : rowsJ2 164 165 72 360 ≤ 2441312590883683 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5061 rows22250R_5062 (by norm_num)

theorem c22250R_164_23 : rowsJ2 164 165 70 360 ≤ 2446759544093482 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5060 c22250R_164_24 (by norm_num)

theorem c22250R_164_22 : rowsJ2 164 165 68 360 ≤ 2454777969914791 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5059 c22250R_164_23 (by norm_num)

theorem c22250R_164_21 : rowsJ2 164 165 67 360 ≤ 2459915304366683 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5058 c22250R_164_22 (by norm_num)

theorem c22250R_164_20 : rowsJ2 164 165 66 360 ≤ 2465894434090238 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5057 c22250R_164_21 (by norm_num)

theorem c22250R_164_19 : rowsJ2 164 165 65 360 ≤ 2472784307052963 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5056 c22250R_164_20 (by norm_num)

theorem c22250R_164_18 : rowsJ2 164 165 64 360 ≤ 2480655342694068 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5055 c22250R_164_19 (by norm_num)

theorem c22250R_164_17 : rowsJ2 164 165 63 360 ≤ 2489579555265396 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5054 c22250R_164_18 (by norm_num)

theorem c22250R_164_16 : rowsJ2 164 165 62 360 ≤ 2499630682277203 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5053 c22250R_164_17 (by norm_num)

theorem c22250R_164_15 : rowsJ2 164 165 61 360 ≤ 2510884318573144 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5052 c22250R_164_16 (by norm_num)

theorem c22250R_164_14 : rowsJ2 164 165 60 360 ≤ 2523418056595310 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5051 c22250R_164_15 (by norm_num)

theorem c22250R_164_13 : rowsJ2 164 165 59 360 ≤ 2537311633440988 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5050 c22250R_164_14 (by norm_num)

theorem c22250R_164_12 : rowsJ2 164 165 58 360 ≤ 2552647085358801 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5049 c22250R_164_13 (by norm_num)

theorem c22250R_164_11 : rowsJ2 164 165 57 360 ≤ 2566800844607745 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5048 c22250R_164_12 (by norm_num)

theorem c22250R_164_10 : rowsJ2 164 165 56 360 ≤ 2579808453590320 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5047 c22250R_164_11 (by norm_num)

theorem c22250R_164_9 : rowsJ2 164 165 55 360 ≤ 2591706389766812 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5046 c22250R_164_10 (by norm_num)

theorem c22250R_164_8 : rowsJ2 164 165 54 360 ≤ 2602532179491827 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5045 c22250R_164_9 (by norm_num)

theorem c22250R_164_7 : rowsJ2 164 165 53 360 ≤ 2612324516739269 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5044 c22250R_164_8 (by norm_num)

theorem c22250R_164_6 : rowsJ2 164 165 52 360 ≤ 2621123387289248 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5043 c22250R_164_7 (by norm_num)

theorem c22250R_164_5 : rowsJ2 164 165 51 360 ≤ 2628970198982963 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5042 c22250R_164_6 (by norm_num)

theorem c22250R_164_4 : rowsJ2 164 165 50 360 ≤ 2635907918689061 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5041 c22250R_164_5 (by norm_num)

theorem c22250R_164_3 : rowsJ2 164 165 49 360 ≤ 2641981216667074 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5040 c22250R_164_4 (by norm_num)

theorem c22250R_164_2 : rowsJ2 164 165 47 360 ≤ 2651722669313124 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5039 c22250R_164_3 (by norm_num)

theorem c22250R_164_1 : rowsJ2 164 165 44 360 ≤ 2661084071508662 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5038 c22250R_164_2 (by norm_num)

theorem c22250R_164_0 : rowsJ2 164 165 0 360 ≤ 2666637016561976 :=
  rowsJ2_le_of_split 164 165 (by norm_num) (by norm_num) rows22250R_5037 c22250R_164_1 (by norm_num)

theorem hr22250R_164 : rows2 164 165 ≤ 2666637016561976 := rows2_le_of_rowsJ2 164 165 c22250R_164_0

theorem c22250R_165_23 : rowsJ2 165 166 71 360 ≤ 2539625680537106 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5086 rows22250R_5087 (by norm_num)

theorem c22250R_165_22 : rowsJ2 165 166 69 360 ≤ 2545751509193837 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5085 c22250R_165_23 (by norm_num)

theorem c22250R_165_21 : rowsJ2 165 166 67 360 ≤ 2554623858851266 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5084 c22250R_165_22 (by norm_num)

theorem c22250R_165_20 : rowsJ2 165 166 66 360 ≤ 2560258062406913 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5083 c22250R_165_21 (by norm_num)

theorem c22250R_165_19 : rowsJ2 165 166 65 360 ≤ 2566783114059068 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5082 c22250R_165_20 (by norm_num)

theorem c22250R_165_18 : rowsJ2 165 166 64 360 ≤ 2574269915582336 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5081 c22250R_165_19 (by norm_num)

theorem c22250R_165_17 : rowsJ2 165 166 63 360 ≤ 2582790941301524 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5080 c22250R_165_18 (by norm_num)

theorem c22250R_165_16 : rowsJ2 165 166 62 360 ≤ 2592420367636702 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5079 c22250R_165_17 (by norm_num)

theorem c22250R_165_15 : rowsJ2 165 166 61 360 ≤ 2603234208217742 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5078 c22250R_165_16 (by norm_num)

theorem c22250R_165_14 : rowsJ2 165 166 60 360 ≤ 2615310455133276 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5077 c22250R_165_15 (by norm_num)

theorem c22250R_165_13 : rowsJ2 165 166 59 360 ≤ 2628729226920313 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5076 c22250R_165_14 (by norm_num)

theorem c22250R_165_12 : rowsJ2 165 166 58 360 ≤ 2643572923945829 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5075 c22250R_165_13 (by norm_num)

theorem c22250R_165_11 : rowsJ2 165 166 57 360 ≤ 2658555608534025 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5074 c22250R_165_12 (by norm_num)

theorem c22250R_165_10 : rowsJ2 165 166 56 360 ≤ 2672354879314849 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5073 c22250R_165_11 (by norm_num)

theorem c22250R_165_9 : rowsJ2 165 166 55 360 ≤ 2685007289958011 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5072 c22250R_165_10 (by norm_num)

theorem c22250R_165_8 : rowsJ2 165 166 54 360 ≤ 2696550396440317 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5071 c22250R_165_9 (by norm_num)

theorem c22250R_165_7 : rowsJ2 165 166 53 360 ≤ 2707022876243393 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5070 c22250R_165_8 (by norm_num)

theorem c22250R_165_6 : rowsJ2 165 166 52 360 ≤ 2716464652847029 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5069 c22250R_165_7 (by norm_num)

theorem c22250R_165_5 : rowsJ2 165 166 51 360 ≤ 2724917026128807 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5068 c22250R_165_6 (by norm_num)

theorem c22250R_165_4 : rowsJ2 165 166 50 360 ≤ 2732422809316930 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5067 c22250R_165_5 (by norm_num)

theorem c22250R_165_3 : rowsJ2 165 166 49 360 ≤ 2739026473184200 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5066 c22250R_165_4 (by norm_num)

theorem c22250R_165_2 : rowsJ2 165 166 47 360 ≤ 2749714535552680 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5065 c22250R_165_3 (by norm_num)

theorem c22250R_165_1 : rowsJ2 165 166 44 360 ≤ 2760205448438306 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5064 c22250R_165_2 (by norm_num)

theorem c22250R_165_0 : rowsJ2 165 166 0 360 ≤ 2766921897379530 :=
  rowsJ2_le_of_split 165 166 (by norm_num) (by norm_num) rows22250R_5063 c22250R_165_1 (by norm_num)

theorem hr22250R_165 : rows2 165 166 ≤ 2766921897379530 := rows2_le_of_rowsJ2 165 166 c22250R_165_0

theorem c22250R_166_23 : rowsJ2 166 167 69 360 ≤ 2542145253213581 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5111 rows22250R_5112 (by norm_num)

theorem c22250R_166_22 : rowsJ2 166 167 67 360 ≤ 2550435000498365 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5110 c22250R_166_23 (by norm_num)

theorem c22250R_166_21 : rowsJ2 166 167 66 360 ≤ 2555746461583027 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5109 c22250R_166_22 (by norm_num)

theorem c22250R_166_20 : rowsJ2 166 167 65 360 ≤ 2561928531106362 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5108 c22250R_166_21 (by norm_num)

theorem c22250R_166_19 : rowsJ2 166 167 64 360 ≤ 2569052620805174 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5107 c22250R_166_20 (by norm_num)

theorem c22250R_166_18 : rowsJ2 166 167 63 360 ≤ 2577191691724649 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5106 c22250R_166_19 (by norm_num)

theorem c22250R_166_17 : rowsJ2 166 167 62 360 ≤ 2586420384938002 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5105 c22250R_166_18 (by norm_num)

theorem c22250R_166_16 : rowsJ2 166 167 61 360 ≤ 2596815157771455 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5104 c22250R_166_17 (by norm_num)

theorem c22250R_166_15 : rowsJ2 166 167 60 360 ≤ 2608454426104685 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5103 c22250R_166_16 (by norm_num)

theorem c22250R_166_14 : rowsJ2 166 167 59 360 ≤ 2621418713357130 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5102 c22250R_166_15 (by norm_num)

theorem c22250R_166_13 : rowsJ2 166 167 58 360 ≤ 2635790806816117 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5101 c22250R_166_14 (by norm_num)

theorem c22250R_166_12 : rowsJ2 166 167 57 360 ≤ 2651655922013531 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5100 c22250R_166_13 (by norm_num)

theorem c22250R_166_11 : rowsJ2 166 167 56 360 ≤ 2666299702886063 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5099 c22250R_166_12 (by norm_num)

theorem c22250R_166_10 : rowsJ2 166 167 55 360 ≤ 2679758816196413 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5098 c22250R_166_11 (by norm_num)

theorem c22250R_166_9 : rowsJ2 166 167 54 360 ≤ 2692070882752374 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5097 c22250R_166_10 (by norm_num)

theorem c22250R_166_8 : rowsJ2 166 167 53 360 ≤ 2703274597213093 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5096 c22250R_166_9 (by norm_num)

theorem c22250R_166_7 : rowsJ2 166 167 52 360 ≤ 2713409853014168 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5095 c22250R_166_8 (by norm_num)

theorem c22250R_166_6 : rowsJ2 166 167 51 360 ≤ 2722517873028210 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5094 c22250R_166_7 (by norm_num)

theorem c22250R_166_5 : rowsJ2 166 167 50 360 ≤ 2730641346612102 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5093 c22250R_166_6 (by norm_num)

theorem c22250R_166_4 : rowsJ2 166 167 49 360 ≤ 2737824573732094 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5092 c22250R_166_5 (by norm_num)

theorem c22250R_166_3 : rowsJ2 166 167 48 360 ≤ 2744113616903393 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5091 c22250R_166_4 (by norm_num)

theorem c22250R_166_2 : rowsJ2 166 167 46 360 ≤ 2754203186907265 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5090 c22250R_166_3 (by norm_num)

theorem c22250R_166_1 : rowsJ2 166 167 43 360 ≤ 2763902695428524 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5089 c22250R_166_2 (by norm_num)

theorem c22250R_166_0 : rowsJ2 166 167 0 360 ≤ 2769478720541220 :=
  rowsJ2_le_of_split 166 167 (by norm_num) (by norm_num) rows22250R_5088 c22250R_166_1 (by norm_num)

theorem hr22250R_166 : rows2 166 167 ≤ 2769478720541220 := rows2_le_of_rowsJ2 166 167 c22250R_166_0

theorem c22250R_167_23 : rowsJ2 167 168 70 360 ≤ 2535992452892459 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5136 rows22250R_5137 (by norm_num)

theorem c22250R_167_22 : rowsJ2 167 168 68 360 ≤ 2542327010630779 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5135 c22250R_167_23 (by norm_num)

theorem c22250R_167_21 : rowsJ2 167 168 66 360 ≤ 2551502259273997 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5134 c22250R_167_22 (by norm_num)

theorem c22250R_167_20 : rowsJ2 167 168 65 360 ≤ 2557329165247502 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5133 c22250R_167_21 (by norm_num)

theorem c22250R_167_19 : rowsJ2 167 168 64 360 ≤ 2564077720186201 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5132 c22250R_167_20 (by norm_num)

theorem c22250R_167_18 : rowsJ2 167 168 63 360 ≤ 2571821394314757 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5131 c22250R_167_19 (by norm_num)

theorem c22250R_167_17 : rowsJ2 167 168 62 360 ≤ 2580635314703275 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5130 c22250R_167_18 (by norm_num)

theorem c22250R_167_16 : rowsJ2 167 168 61 360 ≤ 2590596402673298 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5129 c22250R_167_17 (by norm_num)

theorem c22250R_167_15 : rowsJ2 167 168 60 360 ≤ 2601783517215808 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5128 c22250R_167_16 (by norm_num)

theorem c22250R_167_14 : rowsJ2 167 168 59 360 ≤ 2614277605036680 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5127 c22250R_167_15 (by norm_num)

theorem c22250R_167_13 : rowsJ2 167 168 58 360 ≤ 2628161857889972 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5126 c22250R_167_14 (by norm_num)

theorem c22250R_167_12 : rowsJ2 167 168 57 360 ≤ 2643521877910403 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5125 c22250R_167_13 (by norm_num)

theorem c22250R_167_11 : rowsJ2 167 168 56 360 ≤ 2659027079428680 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5124 c22250R_167_12 (by norm_num)

theorem c22250R_167_10 : rowsJ2 167 168 55 360 ≤ 2673308787034371 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5123 c22250R_167_11 (by norm_num)

theorem c22250R_167_9 : rowsJ2 167 168 54 360 ≤ 2686404716815266 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5122 c22250R_167_10 (by norm_num)

theorem c22250R_167_8 : rowsJ2 167 168 53 360 ≤ 2698353609170432 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5121 c22250R_167_9 (by norm_num)

theorem c22250R_167_7 : rowsJ2 167 168 52 360 ≤ 2709195354296364 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5120 c22250R_167_8 (by norm_num)

theorem c22250R_167_6 : rowsJ2 167 168 51 360 ≤ 2718971123227022 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5119 c22250R_167_7 (by norm_num)

theorem c22250R_167_5 : rowsJ2 167 168 50 360 ≤ 2727723505084385 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5118 c22250R_167_6 (by norm_num)

theorem c22250R_167_4 : rowsJ2 167 168 49 360 ≤ 2735496651234691 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5117 c22250R_167_5 (by norm_num)

theorem c22250R_167_3 : rowsJ2 167 168 48 360 ≤ 2742336427090045 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5116 c22250R_167_4 (by norm_num)

theorem c22250R_167_2 : rowsJ2 167 168 46 360 ≤ 2753408870494655 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5115 c22250R_167_3 (by norm_num)

theorem c22250R_167_1 : rowsJ2 167 168 43 360 ≤ 2764281027435324 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5114 c22250R_167_2 (by norm_num)

theorem c22250R_167_0 : rowsJ2 167 168 0 360 ≤ 2771016238183371 :=
  rowsJ2_le_of_split 167 168 (by norm_num) (by norm_num) rows22250R_5113 c22250R_167_1 (by norm_num)

theorem hr22250R_167 : rows2 167 168 ≤ 2771016238183371 := rows2_le_of_rowsJ2 167 168 c22250R_167_0

theorem c22250R_168_22 : rowsJ2 168 169 68 360 ≤ 2532606075585442 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5160 rows22250R_5161 (by norm_num)

theorem c22250R_168_21 : rowsJ2 168 169 66 360 ≤ 2541181073702947 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5159 c22250R_168_22 (by norm_num)

theorem c22250R_168_20 : rowsJ2 168 169 65 360 ≤ 2546675614662151 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5158 c22250R_168_21 (by norm_num)

theorem c22250R_168_19 : rowsJ2 168 169 64 360 ≤ 2553071072189943 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5157 c22250R_168_20 (by norm_num)

theorem c22250R_168_18 : rowsJ2 168 169 63 360 ≤ 2560441454784133 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5156 c22250R_168_19 (by norm_num)

theorem c22250R_168_17 : rowsJ2 168 169 62 360 ≤ 2568862403562278 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5155 c22250R_168_18 (by norm_num)

theorem c22250R_168_16 : rowsJ2 168 169 61 360 ≤ 2578411330929433 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5154 c22250R_168_17 (by norm_num)

theorem c22250R_168_15 : rowsJ2 168 169 60 360 ≤ 2589167565190042 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5153 c22250R_168_16 (by norm_num)

theorem c22250R_168_14 : rowsJ2 168 169 59 360 ≤ 2601212501724726 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5152 c22250R_168_15 (by norm_num)

theorem c22250R_168_13 : rowsJ2 168 169 58 360 ≤ 2614629761397549 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5151 c22250R_168_14 (by norm_num)

theorem c22250R_168_12 : rowsJ2 168 169 57 360 ≤ 2629505356909512 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5150 c22250R_168_13 (by norm_num)

theorem c22250R_168_11 : rowsJ2 168 169 56 360 ≤ 2645927867870728 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5149 c22250R_168_12 (by norm_num)

theorem c22250R_168_10 : rowsJ2 168 169 55 360 ≤ 2661087352197512 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5148 c22250R_168_11 (by norm_num)

theorem c22250R_168_9 : rowsJ2 168 169 54 360 ≤ 2675021660892280 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5147 c22250R_168_10 (by norm_num)

theorem c22250R_168_8 : rowsJ2 168 169 53 360 ≤ 2687769617881332 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5146 c22250R_168_9 (by norm_num)

theorem c22250R_168_7 : rowsJ2 168 169 52 360 ≤ 2699371146212505 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5145 c22250R_168_8 (by norm_num)

theorem c22250R_168_6 : rowsJ2 168 169 51 360 ≤ 2709867399613353 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5144 c22250R_168_7 (by norm_num)

theorem c22250R_168_5 : rowsJ2 168 169 50 360 ≤ 2719300900073190 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5143 c22250R_168_6 (by norm_num)

theorem c22250R_168_4 : rowsJ2 168 169 49 360 ≤ 2727715682149543 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5142 c22250R_168_5 (by norm_num)

theorem c22250R_168_3 : rowsJ2 168 169 48 360 ≤ 2735157444742352 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5141 c22250R_168_4 (by norm_num)

theorem c22250R_168_2 : rowsJ2 168 169 46 360 ≤ 2747313998101482 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5140 c22250R_168_3 (by norm_num)

theorem c22250R_168_1 : rowsJ2 168 169 43 360 ≤ 2759507893657726 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5139 c22250R_168_2 (by norm_num)

theorem c22250R_168_0 : rowsJ2 168 169 0 360 ≤ 2767644581517619 :=
  rowsJ2_le_of_split 168 169 (by norm_num) (by norm_num) rows22250R_5138 c22250R_168_1 (by norm_num)

theorem hr22250R_168 : rows2 168 169 ≤ 2767644581517619 := rows2_le_of_rowsJ2 168 169 c22250R_168_0

theorem c22250R_169_22 : rowsJ2 169 170 67 360 ≤ 2533576273834581 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5184 rows22250R_5185 (by norm_num)

theorem c22250R_169_21 : rowsJ2 169 170 65 360 ≤ 2543070066726235 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5183 c22250R_169_22 (by norm_num)

theorem c22250R_169_20 : rowsJ2 169 170 64 360 ≤ 2549099645400212 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5182 c22250R_169_21 (by norm_num)

theorem c22250R_169_19 : rowsJ2 169 170 63 360 ≤ 2556083283681763 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5181 c22250R_169_20 (by norm_num)

theorem c22250R_169_18 : rowsJ2 169 170 62 360 ≤ 2564097160387853 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5180 c22250R_169_19 (by norm_num)

theorem c22250R_169_17 : rowsJ2 169 170 61 360 ≤ 2573219201471372 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5179 c22250R_169_18 (by norm_num)

theorem c22250R_169_16 : rowsJ2 169 170 60 360 ≤ 2583529225902682 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5178 c22250R_169_17 (by norm_num)

theorem c22250R_169_15 : rowsJ2 169 170 59 360 ≤ 2595109098048846 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5177 c22250R_169_16 (by norm_num)

theorem c22250R_169_14 : rowsJ2 169 170 58 360 ≤ 2608042887221658 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5176 c22250R_169_15 (by norm_num)

theorem c22250R_169_13 : rowsJ2 169 170 57 360 ≤ 2622417035115203 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5175 c22250R_169_14 (by norm_num)

theorem c22250R_169_12 : rowsJ2 169 170 56 360 ≤ 2638320531910315 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5174 c22250R_169_13 (by norm_num)

theorem c22250R_169_11 : rowsJ2 169 170 55 360 ≤ 2654375781448814 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5173 c22250R_169_12 (by norm_num)

theorem c22250R_169_10 : rowsJ2 169 170 54 360 ≤ 2669165372172562 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5172 c22250R_169_11 (by norm_num)

theorem c22250R_169_9 : rowsJ2 169 170 53 360 ≤ 2682728244384733 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5171 c22250R_169_10 (by norm_num)

theorem c22250R_169_8 : rowsJ2 169 170 52 360 ≤ 2695104384759877 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5170 c22250R_169_9 (by norm_num)

theorem c22250R_169_7 : rowsJ2 169 170 51 360 ≤ 2706334958563763 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5169 c22250R_169_8 (by norm_num)

theorem c22250R_169_6 : rowsJ2 169 170 50 360 ≤ 2716462447698261 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5168 c22250R_169_7 (by norm_num)

theorem c22250R_169_5 : rowsJ2 169 170 49 360 ≤ 2725530795278398 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5167 c22250R_169_6 (by norm_num)

theorem c22250R_169_4 : rowsJ2 169 170 48 360 ≤ 2733585557489682 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5166 c22250R_169_5 (by norm_num)

theorem c22250R_169_3 : rowsJ2 169 170 47 360 ≤ 2740674063521458 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5165 c22250R_169_4 (by norm_num)

theorem c22250R_169_2 : rowsJ2 169 170 45 360 ≤ 2752151511813579 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5164 c22250R_169_3 (by norm_num)

theorem c22250R_169_1 : rowsJ2 169 170 42 360 ≤ 2763425521370804 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5163 c22250R_169_2 (by norm_num)

theorem c22250R_169_0 : rowsJ2 169 170 0 360 ≤ 2770035622612666 :=
  rowsJ2_le_of_split 169 170 (by norm_num) (by norm_num) rows22250R_5162 c22250R_169_1 (by norm_num)

theorem hr22250R_169 : rows2 169 170 ≤ 2770035622612666 := rows2_le_of_rowsJ2 169 170 c22250R_169_0

theorem c22250R_170_21 : rowsJ2 170 171 66 360 ≤ 2536276490369898 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5207 rows22250R_5208 (by norm_num)

theorem c22250R_170_20 : rowsJ2 170 171 64 360 ≤ 2546793124623790 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5206 c22250R_170_21 (by norm_num)

theorem c22250R_170_19 : rowsJ2 170 171 63 360 ≤ 2553413081554973 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5205 c22250R_170_20 (by norm_num)

theorem c22250R_170_18 : rowsJ2 170 171 62 360 ≤ 2561042601116570 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5204 c22250R_170_19 (by norm_num)

theorem c22250R_170_17 : rowsJ2 170 171 61 360 ≤ 2569760152358977 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5203 c22250R_170_18 (by norm_num)

theorem c22250R_170_16 : rowsJ2 170 171 60 360 ≤ 2579646073443294 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5202 c22250R_170_17 (by norm_num)

theorem c22250R_170_15 : rowsJ2 170 171 59 360 ≤ 2590782725305022 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5201 c22250R_170_16 (by norm_num)

theorem c22250R_170_14 : rowsJ2 170 171 58 360 ≤ 2603254652420455 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5200 c22250R_170_15 (by norm_num)

theorem c22250R_170_13 : rowsJ2 170 171 57 360 ≤ 2617148751401976 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5199 c22250R_170_14 (by norm_num)

theorem c22250R_170_12 : rowsJ2 170 171 56 360 ≤ 2632554448205067 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5198 c22250R_170_13 (by norm_num)

theorem c22250R_170_11 : rowsJ2 170 171 55 360 ≤ 2649563884792278 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5197 c22250R_170_12 (by norm_num)

theorem c22250R_170_10 : rowsJ2 170 171 54 360 ≤ 2665266419424359 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5196 c22250R_170_11 (by norm_num)

theorem c22250R_170_9 : rowsJ2 170 171 53 360 ≤ 2679701151434595 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5195 c22250R_170_10 (by norm_num)

theorem c22250R_170_8 : rowsJ2 170 171 52 360 ≤ 2692908171737653 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5194 c22250R_170_9 (by norm_num)

theorem c22250R_170_7 : rowsJ2 170 171 51 360 ≤ 2704928695877905 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5193 c22250R_170_8 (by norm_num)

theorem c22250R_170_6 : rowsJ2 170 171 50 360 ≤ 2715805202691004 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5192 c22250R_170_7 (by norm_num)

theorem c22250R_170_5 : rowsJ2 170 171 49 360 ≤ 2725581579293303 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5191 c22250R_170_6 (by norm_num)

theorem c22250R_170_4 : rowsJ2 170 171 48 360 ≤ 2734303273153687 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5190 c22250R_170_5 (by norm_num)

theorem c22250R_170_3 : rowsJ2 170 171 47 360 ≤ 2742017452048008 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5189 c22250R_170_4 (by norm_num)

theorem c22250R_170_2 : rowsJ2 170 171 45 360 ≤ 2754621559363845 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5188 c22250R_170_3 (by norm_num)

theorem c22250R_170_1 : rowsJ2 170 171 42 360 ≤ 2767269017005537 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5187 c22250R_170_2 (by norm_num)

theorem c22250R_170_0 : rowsJ2 170 171 0 360 ≤ 2775233802163741 :=
  rowsJ2_le_of_split 170 171 (by norm_num) (by norm_num) rows22250R_5186 c22250R_170_1 (by norm_num)

theorem hr22250R_170 : rows2 170 171 ≤ 2775233802163741 := rows2_le_of_rowsJ2 170 171 c22250R_170_0

theorem c22250R_171_22 : rowsJ2 171 172 66 360 ≤ 2529458059652946 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5231 rows22250R_5232 (by norm_num)

theorem c22250R_171_21 : rowsJ2 171 172 64 360 ≤ 2539287038676096 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5230 c22250R_171_22 (by norm_num)

theorem c22250R_171_20 : rowsJ2 171 172 63 360 ≤ 2545529896769849 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5229 c22250R_171_21 (by norm_num)

theorem c22250R_171_19 : rowsJ2 171 172 62 360 ≤ 2552760938913602 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5228 c22250R_171_20 (by norm_num)

theorem c22250R_171_18 : rowsJ2 171 172 61 360 ≤ 2561059202182208 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5227 c22250R_171_19 (by norm_num)

theorem c22250R_171_17 : rowsJ2 171 172 60 360 ≤ 2570505567589139 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5226 c22250R_171_18 (by norm_num)

theorem c22250R_171_16 : rowsJ2 171 172 59 360 ≤ 2581182915116126 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5225 c22250R_171_17 (by norm_num)

theorem c22250R_171_15 : rowsJ2 171 172 58 360 ≤ 2593176285774221 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5224 c22250R_171_16 (by norm_num)

theorem c22250R_171_14 : rowsJ2 171 172 57 360 ≤ 2606573051428792 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5223 c22250R_171_15 (by norm_num)

theorem c22250R_171_13 : rowsJ2 171 172 56 360 ≤ 2621463093176518 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5222 c22250R_171_14 (by norm_num)

theorem c22250R_171_12 : rowsJ2 171 172 55 360 ≤ 2637938989125224 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5221 c22250R_171_13 (by norm_num)

theorem c22250R_171_11 : rowsJ2 171 172 54 360 ≤ 2654573614316954 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5220 c22250R_171_12 (by norm_num)

theorem c22250R_171_10 : rowsJ2 171 172 53 360 ≤ 2669898195669146 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5219 c22250R_171_11 (by norm_num)

theorem c22250R_171_9 : rowsJ2 171 172 52 360 ≤ 2683952963830584 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5218 c22250R_171_10 (by norm_num)

theorem c22250R_171_8 : rowsJ2 171 172 51 360 ≤ 2696779217834993 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5217 c22250R_171_9 (by norm_num)

theorem c22250R_171_7 : rowsJ2 171 172 50 360 ≤ 2708419464538733 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5216 c22250R_171_8 (by norm_num)

theorem c22250R_171_6 : rowsJ2 171 172 49 360 ≤ 2718917564168470 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5215 c22250R_171_7 (by norm_num)

theorem c22250R_171_5 : rowsJ2 171 172 48 360 ≤ 2728318882741019 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5214 c22250R_171_6 (by norm_num)

theorem c22250R_171_4 : rowsJ2 171 172 47 360 ≤ 2736670452161079 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5213 c22250R_171_5 (by norm_num)

theorem c22250R_171_3 : rowsJ2 171 172 46 360 ≤ 2744021138854271 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5212 c22250R_171_4 (by norm_num)

theorem c22250R_171_2 : rowsJ2 171 172 44 360 ≤ 2755925581298617 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5211 c22250R_171_3 (by norm_num)

theorem c22250R_171_1 : rowsJ2 171 172 42 360 ≤ 2764466868388301 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5210 c22250R_171_2 (by norm_num)

theorem c22250R_171_0 : rowsJ2 171 172 0 360 ≤ 2773902085686288 :=
  rowsJ2_le_of_split 171 172 (by norm_num) (by norm_num) rows22250R_5209 c22250R_171_1 (by norm_num)

theorem hr22250R_171 : rows2 171 172 ≤ 2773902085686288 := rows2_le_of_rowsJ2 171 172 c22250R_171_0

theorem c22250R_172_21 : rowsJ2 172 173 65 360 ≤ 2535150418977414 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5254 rows22250R_5255 (by norm_num)

theorem c22250R_172_20 : rowsJ2 172 173 63 360 ≤ 2546041728446245 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5253 c22250R_172_21 (by norm_num)

theorem c22250R_172_19 : rowsJ2 172 173 62 360 ≤ 2552898010702525 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5252 c22250R_172_20 (by norm_num)

theorem c22250R_172_18 : rowsJ2 172 173 61 360 ≤ 2560800338770350 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5251 c22250R_172_19 (by norm_num)

theorem c22250R_172_17 : rowsJ2 172 173 60 360 ≤ 2569830167668056 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5250 c22250R_172_18 (by norm_num)

theorem c22250R_172_16 : rowsJ2 172 173 59 360 ≤ 2580070926484114 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5249 c22250R_172_17 (by norm_num)

theorem c22250R_172_15 : rowsJ2 172 173 58 360 ≤ 2591608181821158 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5248 c22250R_172_16 (by norm_num)

theorem c22250R_172_14 : rowsJ2 172 173 57 360 ≤ 2604529808933970 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5247 c22250R_172_15 (by norm_num)

theorem c22250R_172_13 : rowsJ2 172 173 56 360 ≤ 2618926171355781 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5246 c22250R_172_14 (by norm_num)

theorem c22250R_172_12 : rowsJ2 172 173 55 360 ≤ 2634890309869242 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5245 c22250R_172_13 (by norm_num)

theorem c22250R_172_11 : rowsJ2 172 173 54 360 ≤ 2652518141749188 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5244 c22250R_172_12 (by norm_num)

theorem c22250R_172_10 : rowsJ2 172 173 53 360 ≤ 2668792870411990 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5243 c22250R_172_11 (by norm_num)

theorem c22250R_172_9 : rowsJ2 172 173 52 360 ≤ 2683754912210906 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5242 c22250R_172_10 (by norm_num)

theorem c22250R_172_8 : rowsJ2 172 173 51 360 ≤ 2697445693384140 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5241 c22250R_172_9 (by norm_num)

theorem c22250R_172_7 : rowsJ2 172 173 50 360 ≤ 2709907790454294 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5240 c22250R_172_8 (by norm_num)

theorem c22250R_172_6 : rowsJ2 172 173 49 360 ≤ 2721185076505038 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5239 c22250R_172_7 (by norm_num)

theorem c22250R_172_5 : rowsJ2 172 173 48 360 ≤ 2731322874106026 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5238 c22250R_172_6 (by norm_num)

theorem c22250R_172_4 : rowsJ2 172 173 47 360 ≤ 2740368115699399 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5237 c22250R_172_5 (by norm_num)

theorem c22250R_172_3 : rowsJ2 172 173 46 360 ≤ 2748369512310482 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5236 c22250R_172_4 (by norm_num)

theorem c22250R_172_2 : rowsJ2 172 173 44 360 ≤ 2761445585552716 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5235 c22250R_172_3 (by norm_num)

theorem c22250R_172_1 : rowsJ2 172 173 41 360 ≤ 2774571527367149 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5234 c22250R_172_2 (by norm_num)

theorem c22250R_172_0 : rowsJ2 172 173 0 360 ≤ 2782150227624241 :=
  rowsJ2_le_of_split 172 173 (by norm_num) (by norm_num) rows22250R_5233 c22250R_172_1 (by norm_num)

theorem hr22250R_172 : rows2 172 173 ≤ 2782150227624241 := rows2_le_of_rowsJ2 172 173 c22250R_172_0

theorem c22250R_173_21 : rowsJ2 173 174 65 360 ≤ 2537760524844378 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5277 rows22250R_5278 (by norm_num)

theorem c22250R_173_20 : rowsJ2 173 174 63 360 ≤ 2547942405847671 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5276 c22250R_173_21 (by norm_num)

theorem c22250R_173_19 : rowsJ2 173 174 62 360 ≤ 2554409836024744 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5275 c22250R_173_20 (by norm_num)

theorem c22250R_173_18 : rowsJ2 173 174 61 360 ≤ 2561901400724071 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5274 c22250R_173_19 (by norm_num)

theorem c22250R_173_17 : rowsJ2 173 174 60 360 ≤ 2570499155259570 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5273 c22250R_173_18 (by norm_num)

theorem c22250R_173_16 : rowsJ2 173 174 59 360 ≤ 2580287102768318 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5272 c22250R_173_17 (by norm_num)

theorem c22250R_173_15 : rowsJ2 173 174 58 360 ≤ 2591351359125116 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5271 c22250R_173_16 (by norm_num)

theorem c22250R_173_14 : rowsJ2 173 174 57 360 ≤ 2603780325475758 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5270 c22250R_173_15 (by norm_num)

theorem c22250R_173_13 : rowsJ2 173 174 56 360 ≤ 2617664869189688 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5269 c22250R_173_14 (by norm_num)

theorem c22250R_173_12 : rowsJ2 173 174 55 360 ≤ 2633098514094896 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5268 c22250R_173_13 (by norm_num)

theorem c22250R_173_11 : rowsJ2 173 174 54 360 ≤ 2650177640927828 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5267 c22250R_173_12 (by norm_num)

theorem c22250R_173_10 : rowsJ2 173 174 53 360 ≤ 2667422909157911 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5266 c22250R_173_11 (by norm_num)

theorem c22250R_173_9 : rowsJ2 173 174 52 360 ≤ 2683311382219395 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5265 c22250R_173_10 (by norm_num)

theorem c22250R_173_8 : rowsJ2 173 174 51 360 ≤ 2697884651966126 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5264 c22250R_173_9 (by norm_num)

theorem c22250R_173_7 : rowsJ2 173 174 50 360 ≤ 2711185400481526 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5263 c22250R_173_8 (by norm_num)

theorem c22250R_173_6 : rowsJ2 173 174 49 360 ≤ 2723257547261899 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5262 c22250R_173_7 (by norm_num)

theorem c22250R_173_5 : rowsJ2 173 174 48 360 ≤ 2734146402808795 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5261 c22250R_173_6 (by norm_num)

theorem c22250R_173_4 : rowsJ2 173 174 47 360 ≤ 2743898829452387 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5260 c22250R_173_5 (by norm_num)

theorem c22250R_173_3 : rowsJ2 173 174 46 360 ≤ 2752563410275350 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5259 c22250R_173_4 (by norm_num)

theorem c22250R_173_2 : rowsJ2 173 174 44 360 ≤ 2766833048255972 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5258 c22250R_173_3 (by norm_num)

theorem c22250R_173_1 : rowsJ2 173 174 41 360 ≤ 2781412788989918 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5257 c22250R_173_2 (by norm_num)

theorem c22250R_173_0 : rowsJ2 173 174 0 360 ≤ 2790409342951772 :=
  rowsJ2_le_of_split 173 174 (by norm_num) (by norm_num) rows22250R_5256 c22250R_173_1 (by norm_num)

theorem hr22250R_173 : rows2 173 174 ≤ 2790409342951772 := rows2_le_of_rowsJ2 173 174 c22250R_173_0

theorem c22250R_174_21 : rowsJ2 174 175 64 360 ≤ 2539680479487975 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5300 rows22250R_5301 (by norm_num)

theorem c22250R_174_20 : rowsJ2 174 175 62 360 ≤ 2550966396232496 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5299 c22250R_174_21 (by norm_num)

theorem c22250R_174_19 : rowsJ2 174 175 61 360 ≤ 2558071600231447 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5298 c22250R_174_20 (by norm_num)

theorem c22250R_174_18 : rowsJ2 174 175 60 360 ≤ 2566261300767000 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5297 c22250R_174_19 (by norm_num)

theorem c22250R_174_17 : rowsJ2 174 175 59 360 ≤ 2575620107892258 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5296 c22250R_174_18 (by norm_num)

theorem c22250R_174_16 : rowsJ2 174 175 58 360 ≤ 2586234718457570 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5295 c22250R_174_17 (by norm_num)

theorem c22250R_174_15 : rowsJ2 174 175 57 360 ≤ 2598194090133949 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5294 c22250R_174_16 (by norm_num)

theorem c22250R_174_14 : rowsJ2 174 175 56 360 ≤ 2611589623781952 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5293 c22250R_174_15 (by norm_num)

theorem c22250R_174_13 : rowsJ2 174 175 55 360 ≤ 2626515355035589 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5292 c22250R_174_14 (by norm_num)

theorem c22250R_174_12 : rowsJ2 174 175 54 360 ≤ 2643068156040351 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5291 c22250R_174_13 (by norm_num)

theorem c22250R_174_11 : rowsJ2 174 175 53 360 ≤ 2661347948363317 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5290 c22250R_174_12 (by norm_num)

theorem c22250R_174_10 : rowsJ2 174 175 52 360 ≤ 2678225955760049 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5289 c22250R_174_11 (by norm_num)

theorem c22250R_174_9 : rowsJ2 174 175 51 360 ≤ 2693743985320899 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5288 c22250R_174_10 (by norm_num)

theorem c22250R_174_8 : rowsJ2 174 175 50 360 ≤ 2707944871814527 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5287 c22250R_174_9 (by norm_num)

theorem c22250R_174_7 : rowsJ2 174 175 49 360 ≤ 2720872625984817 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5286 c22250R_174_8 (by norm_num)

theorem c22250R_174_6 : rowsJ2 174 175 48 360 ≤ 2732572589000425 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5285 c22250R_174_7 (by norm_num)

theorem c22250R_174_5 : rowsJ2 174 175 47 360 ≤ 2743091593889607 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5284 c22250R_174_6 (by norm_num)

theorem c22250R_174_4 : rowsJ2 174 175 46 360 ≤ 2752478134838454 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5283 c22250R_174_5 (by norm_num)

theorem c22250R_174_3 : rowsJ2 174 175 45 360 ≤ 2760782545283099 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5282 c22250R_174_4 (by norm_num)

theorem c22250R_174_2 : rowsJ2 174 175 43 360 ≤ 2774356642768883 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5281 c22250R_174_3 (by norm_num)

theorem c22250R_174_1 : rowsJ2 174 175 41 360 ≤ 2784260758581210 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5280 c22250R_174_2 (by norm_num)

theorem c22250R_174_0 : rowsJ2 174 175 0 360 ≤ 2794894234073660 :=
  rowsJ2_le_of_split 174 175 (by norm_num) (by norm_num) rows22250R_5279 c22250R_174_1 (by norm_num)

theorem hr22250R_174 : rows2 174 175 ≤ 2794894234073660 := rows2_le_of_rowsJ2 174 175 c22250R_174_0

theorem c22250R_175_20 : rowsJ2 175 176 63 360 ≤ 2549914825493050 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_5322 rows22250R_5323 (by norm_num)

theorem c22250R_175_19 : rowsJ2 175 176 61 360 ≤ 2562344216494924 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_5321 c22250R_175_20 (by norm_num)

theorem c22250R_175_18 : rowsJ2 175 176 60 360 ≤ 2570110283589715 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_5320 c22250R_175_19 (by norm_num)

theorem c22250R_175_17 : rowsJ2 175 176 59 360 ≤ 2579023627619976 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_5319 c22250R_175_18 (by norm_num)

theorem c22250R_175_16 : rowsJ2 175 176 58 360 ≤ 2589171552723339 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_5318 c22250R_175_17 (by norm_num)

theorem c22250R_175_15 : rowsJ2 175 176 57 360 ≤ 2600643598063322 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_5317 c22250R_175_16 (by norm_num)

theorem c22250R_175_14 : rowsJ2 175 176 56 360 ≤ 2613531721702903 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_5316 c22250R_175_15 (by norm_num)

theorem c22250R_175_13 : rowsJ2 175 176 55 360 ≤ 2627930493620517 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_5315 c22250R_175_14 (by norm_num)

theorem c22250R_175_12 : rowsJ2 175 176 54 360 ≤ 2643937298814532 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_5314 c22250R_175_13 (by norm_num)

theorem c22250R_175_11 : rowsJ2 175 176 53 360 ≤ 2661652551520274 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_5313 c22250R_175_12 (by norm_num)

theorem c22250R_175_10 : rowsJ2 175 176 52 360 ≤ 2679541826538418 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_5312 c22250R_175_11 (by norm_num)

theorem c22250R_175_9 : rowsJ2 175 176 51 360 ≤ 2696025030683654 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_5311 c22250R_175_10 (by norm_num)

theorem c22250R_175_8 : rowsJ2 175 176 50 360 ≤ 2711145193043922 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_5310 c22250R_175_9 (by norm_num)

theorem c22250R_175_7 : rowsJ2 175 176 49 360 ≤ 2724946454467271 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_5309 c22250R_175_8 (by norm_num)

theorem c22250R_175_6 : rowsJ2 175 176 48 360 ≤ 2737474223067065 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_5308 c22250R_175_7 (by norm_num)

theorem c22250R_175_5 : rowsJ2 175 176 47 360 ≤ 2748775336449087 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_5307 c22250R_175_6 (by norm_num)

theorem c22250R_175_4 : rowsJ2 175 176 46 360 ≤ 2758898231548901 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_5306 c22250R_175_5 (by norm_num)

theorem c22250R_175_3 : rowsJ2 175 176 45 360 ≤ 2767893123018281 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_5305 c22250R_175_4 (by norm_num)

theorem c22250R_175_2 : rowsJ2 175 176 43 360 ≤ 2782709780465696 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_5304 c22250R_175_3 (by norm_num)

theorem c22250R_175_1 : rowsJ2 175 176 40 360 ≤ 2797854091805607 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_5303 c22250R_175_2 (by norm_num)

theorem c22250R_175_0 : rowsJ2 175 176 0 360 ≤ 2806115889531461 :=
  rowsJ2_le_of_split 175 176 (by norm_num) (by norm_num) rows22250R_5302 c22250R_175_1 (by norm_num)

theorem hr22250R_175 : rows2 175 176 ≤ 2806115889531461 := rows2_le_of_rowsJ2 175 176 c22250R_175_0

theorem c22250R_176_20 : rowsJ2 176 177 61 360 ≤ 2568192227353944 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_5344 rows22250R_5345 (by norm_num)

theorem c22250R_176_19 : rowsJ2 176 177 60 360 ≤ 2575559781111852 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_5343 c22250R_176_20 (by norm_num)

theorem c22250R_176_18 : rowsJ2 176 177 59 360 ≤ 2584052381422855 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_5342 c22250R_176_19 (by norm_num)

theorem c22250R_176_17 : rowsJ2 176 177 58 360 ≤ 2593757974415596 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_5341 c22250R_176_18 (by norm_num)

theorem c22250R_176_16 : rowsJ2 176 177 57 360 ≤ 2604766714208223 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_5340 c22250R_176_17 (by norm_num)

theorem c22250R_176_15 : rowsJ2 176 177 56 360 ≤ 2617171148388923 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_5339 c22250R_176_16 (by norm_num)

theorem c22250R_176_14 : rowsJ2 176 177 55 360 ≤ 2631066412560704 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_5338 c22250R_176_15 (by norm_num)

theorem c22250R_176_13 : rowsJ2 176 177 54 360 ≤ 2646550434903810 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_5337 c22250R_176_14 (by norm_num)

theorem c22250R_176_12 : rowsJ2 176 177 53 360 ≤ 2663724151787130 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_5336 c22250R_176_13 (by norm_num)

theorem c22250R_176_11 : rowsJ2 176 177 52 360 ≤ 2682691735547991 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_5335 c22250R_176_12 (by norm_num)

theorem c22250R_176_10 : rowsJ2 176 177 51 360 ≤ 2700206205030488 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_5334 c22250R_176_11 (by norm_num)

theorem c22250R_176_9 : rowsJ2 176 177 50 360 ≤ 2716310837286495 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_5333 c22250R_176_10 (by norm_num)

theorem c22250R_176_8 : rowsJ2 176 177 49 360 ≤ 2731049954145717 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_5332 c22250R_176_9 (by norm_num)

theorem c22250R_176_7 : rowsJ2 176 177 48 360 ≤ 2744469079007707 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_5331 c22250R_176_8 (by norm_num)

theorem c22250R_176_6 : rowsJ2 176 177 47 360 ≤ 2756615100072780 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_5330 c22250R_176_7 (by norm_num)

theorem c22250R_176_5 : rowsJ2 176 177 46 360 ≤ 2767536440912808 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_5329 c22250R_176_6 (by norm_num)

theorem c22250R_176_4 : rowsJ2 176 177 45 360 ≤ 2777283239330687 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_5328 c22250R_176_5 (by norm_num)

theorem c22250R_176_3 : rowsJ2 176 177 44 360 ≤ 2785907535514003 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_5327 c22250R_176_4 (by norm_num)

theorem c22250R_176_2 : rowsJ2 176 177 42 360 ≤ 2800007496475592 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_5326 c22250R_176_3 (by norm_num)

theorem c22250R_176_1 : rowsJ2 176 177 40 360 ≤ 2810298534451218 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_5325 c22250R_176_2 (by norm_num)

theorem c22250R_176_0 : rowsJ2 176 177 0 360 ≤ 2820089201745463 :=
  rowsJ2_le_of_split 176 177 (by norm_num) (by norm_num) rows22250R_5324 c22250R_176_1 (by norm_num)

theorem hr22250R_176 : rows2 176 177 ≤ 2820089201745463 := rows2_le_of_rowsJ2 176 177 c22250R_176_0

theorem c22250R_177_19 : rowsJ2 177 178 60 360 ≤ 2575837328252233 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_5365 rows22250R_5366 (by norm_num)

theorem c22250R_177_18 : rowsJ2 177 178 59 360 ≤ 2583892807516674 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_5364 c22250R_177_19 (by norm_num)

theorem c22250R_177_17 : rowsJ2 177 178 58 360 ≤ 2593138912338261 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_5363 c22250R_177_18 (by norm_num)

theorem c22250R_177_16 : rowsJ2 177 178 57 360 ≤ 2603666439568364 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_5362 c22250R_177_17 (by norm_num)

theorem c22250R_177_15 : rowsJ2 177 178 56 360 ≤ 2615568552665009 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_5361 c22250R_177_16 (by norm_num)

theorem c22250R_177_14 : rowsJ2 177 178 55 360 ≤ 2628940977861803 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_5360 c22250R_177_15 (by norm_num)

theorem c22250R_177_13 : rowsJ2 177 178 54 360 ≤ 2643882210277839 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_5359 c22250R_177_14 (by norm_num)

theorem c22250R_177_12 : rowsJ2 177 178 53 360 ≤ 2660493731007539 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_5358 c22250R_177_13 (by norm_num)

theorem c22250R_177_11 : rowsJ2 177 178 52 360 ≤ 2678880236317015 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_5357 c22250R_177_12 (by norm_num)

theorem c22250R_177_10 : rowsJ2 177 178 51 360 ≤ 2697449149707296 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_5356 c22250R_177_11 (by norm_num)

theorem c22250R_177_9 : rowsJ2 177 178 50 360 ≤ 2714560021035533 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_5355 c22250R_177_10 (by norm_num)

theorem c22250R_177_8 : rowsJ2 177 178 49 360 ≤ 2730257398313349 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_5354 c22250R_177_9 (by norm_num)

theorem c22250R_177_7 : rowsJ2 177 178 48 360 ≤ 2744586962357125 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_5353 c22250R_177_8 (by norm_num)

theorem c22250R_177_6 : rowsJ2 177 178 47 360 ≤ 2757595691244871 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_5352 c22250R_177_7 (by norm_num)

theorem c22250R_177_5 : rowsJ2 177 178 46 360 ≤ 2769332031822289 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_5351 c22250R_177_6 (by norm_num)

theorem c22250R_177_4 : rowsJ2 177 178 45 360 ≤ 2779846079219106 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_5350 c22250R_177_5 (by norm_num)

theorem c22250R_177_3 : rowsJ2 177 178 44 360 ≤ 2789189765390622 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_5349 c22250R_177_4 (by norm_num)

theorem c22250R_177_2 : rowsJ2 177 178 42 360 ≤ 2804584169134019 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_5348 c22250R_177_3 (by norm_num)

theorem c22250R_177_1 : rowsJ2 177 178 40 360 ≤ 2815975275081233 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_5347 c22250R_177_2 (by norm_num)

theorem c22250R_177_0 : rowsJ2 177 178 0 360 ≤ 2827472987940171 :=
  rowsJ2_le_of_split 177 178 (by norm_num) (by norm_num) rows22250R_5346 c22250R_177_1 (by norm_num)

theorem hr22250R_177 : rows2 177 178 ≤ 2827472987940171 := rows2_le_of_rowsJ2 177 178 c22250R_177_0

theorem c22250R_178_18 : rowsJ2 178 179 59 360 ≤ 2592002927672409 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_5385 rows22250R_5386 (by norm_num)

theorem c22250R_178_17 : rowsJ2 178 179 58 360 ≤ 2600814995937129 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_5384 c22250R_178_18 (by norm_num)

theorem c22250R_178_16 : rowsJ2 178 179 57 360 ≤ 2610886378815722 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_5383 c22250R_178_17 (by norm_num)

theorem c22250R_178_15 : rowsJ2 178 179 56 360 ≤ 2622310890982551 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_5382 c22250R_178_16 (by norm_num)

theorem c22250R_178_14 : rowsJ2 178 179 55 360 ≤ 2635184883433476 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_5381 c22250R_178_15 (by norm_num)

theorem c22250R_178_13 : rowsJ2 178 179 54 360 ≤ 2649607451247492 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_5380 c22250R_178_14 (by norm_num)

theorem c22250R_178_12 : rowsJ2 178 179 53 360 ≤ 2665680652253793 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_5379 c22250R_178_13 (by norm_num)

theorem c22250R_178_11 : rowsJ2 178 179 52 360 ≤ 2683509737738687 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_5378 c22250R_178_12 (by norm_num)

theorem c22250R_178_10 : rowsJ2 178 179 51 360 ≤ 2703203396425384 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_5377 c22250R_178_11 (by norm_num)

theorem c22250R_178_9 : rowsJ2 178 179 50 360 ≤ 2721389782711842 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_5376 c22250R_178_10 (by norm_num)

theorem c22250R_178_8 : rowsJ2 178 179 49 360 ≤ 2738113728878392 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_5375 c22250R_178_9 (by norm_num)

theorem c22250R_178_7 : rowsJ2 178 179 48 360 ≤ 2753421128173711 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_5374 c22250R_178_8 (by norm_num)

theorem c22250R_178_6 : rowsJ2 178 179 47 360 ≤ 2767359100756189 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_5373 c22250R_178_7 (by norm_num)

theorem c22250R_178_5 : rowsJ2 178 179 46 360 ≤ 2779976166371630 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_5372 c22250R_178_6 (by norm_num)

theorem c22250R_178_4 : rowsJ2 178 179 45 360 ≤ 2791322424742912 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_5371 c22250R_178_5 (by norm_num)

theorem c22250R_178_3 : rowsJ2 178 179 44 360 ≤ 2801449744698587 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_5370 c22250R_178_4 (by norm_num)

theorem c22250R_178_2 : rowsJ2 178 179 42 360 ≤ 2818265094920325 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_5369 c22250R_178_3 (by norm_num)

theorem c22250R_178_1 : rowsJ2 178 179 39 360 ≤ 2835767551157324 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_5368 c22250R_178_2 (by norm_num)

theorem c22250R_178_0 : rowsJ2 178 179 0 360 ≤ 2844320294470237 :=
  rowsJ2_le_of_split 178 179 (by norm_num) (by norm_num) rows22250R_5367 c22250R_178_1 (by norm_num)

theorem hr22250R_178 : rows2 178 179 ≤ 2844320294470237 := rows2_le_of_rowsJ2 178 179 c22250R_178_0

theorem c22250R_179_19 : rowsJ2 179 180 59 360 ≤ 2601474606672686 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_5406 rows22250R_5407 (by norm_num)

theorem c22250R_179_18 : rowsJ2 179 180 58 360 ≤ 2609835413038383 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_5405 c22250R_179_19 (by norm_num)

theorem c22250R_179_17 : rowsJ2 179 180 57 360 ≤ 2619432610023796 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_5404 c22250R_179_18 (by norm_num)

theorem c22250R_179_16 : rowsJ2 179 180 56 360 ≤ 2630360692870206 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_5403 c22250R_179_17 (by norm_num)

theorem c22250R_179_15 : rowsJ2 179 180 55 360 ≤ 2642716665155991 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_5402 c22250R_179_16 (by norm_num)

theorem c22250R_179_14 : rowsJ2 179 180 54 360 ≤ 2656600248312810 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_5401 c22250R_179_15 (by norm_num)

theorem c22250R_179_13 : rowsJ2 179 180 53 360 ≤ 2672114101966425 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_5400 c22250R_179_14 (by norm_num)

theorem c22250R_179_12 : rowsJ2 179 180 52 360 ≤ 2689364056244777 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_5399 c22250R_179_13 (by norm_num)

theorem c22250R_179_11 : rowsJ2 179 180 51 360 ≤ 2708459357294549 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_5398 c22250R_179_12 (by norm_num)

theorem c22250R_179_10 : rowsJ2 179 180 50 360 ≤ 2727745996435585 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_5397 c22250R_179_11 (by norm_num)

theorem c22250R_179_9 : rowsJ2 179 180 49 360 ≤ 2745519741413280 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_5396 c22250R_179_10 (by norm_num)

theorem c22250R_179_8 : rowsJ2 179 180 48 360 ≤ 2761826747061159 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_5395 c22250R_179_9 (by norm_num)

theorem c22250R_179_7 : rowsJ2 179 180 47 360 ≤ 2776714321373299 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_5394 c22250R_179_8 (by norm_num)

theorem c22250R_179_6 : rowsJ2 179 180 46 360 ≤ 2790231099602524 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_5393 c22250R_179_7 (by norm_num)

theorem c22250R_179_5 : rowsJ2 179 180 45 360 ≤ 2802427225749445 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_5392 c22250R_179_6 (by norm_num)

theorem c22250R_179_4 : rowsJ2 179 180 44 360 ≤ 2813354542483256 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_5391 c22250R_179_5 (by norm_num)

theorem c22250R_179_3 : rowsJ2 179 180 43 360 ≤ 2823066790593261 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_5390 c22250R_179_4 (by norm_num)

theorem c22250R_179_2 : rowsJ2 179 180 41 360 ≤ 2839071807539047 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_5389 c22250R_179_3 (by norm_num)

theorem c22250R_179_1 : rowsJ2 179 180 39 360 ≤ 2850918460358805 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_5388 c22250R_179_2 (by norm_num)

theorem c22250R_179_0 : rowsJ2 179 180 0 360 ≤ 2861056462690849 :=
  rowsJ2_le_of_split 179 180 (by norm_num) (by norm_num) rows22250R_5387 c22250R_179_1 (by norm_num)

theorem hr22250R_179 : rows2 179 180 ≤ 2861056462690849 := rows2_le_of_rowsJ2 179 180 c22250R_179_0

theorem c22250R_180_18 : rowsJ2 180 181 58 360 ≤ 2613860750371254 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_5426 rows22250R_5427 (by norm_num)

theorem c22250R_180_17 : rowsJ2 180 181 57 360 ≤ 2623009980473024 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_5425 c22250R_180_18 (by norm_num)

theorem c22250R_180_16 : rowsJ2 180 181 56 360 ≤ 2633467451391169 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_5424 c22250R_180_17 (by norm_num)

theorem c22250R_180_15 : rowsJ2 180 181 55 360 ≤ 2645330856653591 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_5423 c22250R_180_16 (by norm_num)

theorem c22250R_180_14 : rowsJ2 180 181 54 360 ≤ 2658700580115675 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_5422 c22250R_180_15 (by norm_num)

theorem c22250R_180_13 : rowsJ2 180 181 53 360 ≤ 2673679918087296 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_5421 c22250R_180_14 (by norm_num)

theorem c22250R_180_12 : rowsJ2 180 181 52 360 ≤ 2690375313348610 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_5420 c22250R_180_13 (by norm_num)

theorem c22250R_180_11 : rowsJ2 180 181 51 360 ≤ 2708896602304745 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_5419 c22250R_180_12 (by norm_num)

theorem c22250R_180_10 : rowsJ2 180 181 50 360 ≤ 2729357276640089 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_5418 c22250R_180_11 (by norm_num)

theorem c22250R_180_9 : rowsJ2 180 181 49 360 ≤ 2748253495242925 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_5417 c22250R_180_10 (by norm_num)

theorem c22250R_180_8 : rowsJ2 180 181 48 360 ≤ 2765631737530769 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_5416 c22250R_180_9 (by norm_num)

theorem c22250R_180_7 : rowsJ2 180 181 47 360 ≤ 2781539558918443 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_5415 c22250R_180_8 (by norm_num)

theorem c22250R_180_6 : rowsJ2 180 181 46 360 ≤ 2796025766626956 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_5414 c22250R_180_7 (by norm_num)

theorem c22250R_180_5 : rowsJ2 180 181 45 360 ≤ 2809140602536262 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_5413 c22250R_180_6 (by norm_num)

theorem c22250R_180_4 : rowsJ2 180 181 44 360 ≤ 2820935934140293 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_5412 c22250R_180_5 (by norm_num)

theorem c22250R_180_3 : rowsJ2 180 181 43 360 ≤ 2831465454716909 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_5411 c22250R_180_4 (by norm_num)

theorem c22250R_180_2 : rowsJ2 180 181 41 360 ≤ 2848952239842841 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_5410 c22250R_180_3 (by norm_num)

theorem c22250R_180_1 : rowsJ2 180 181 39 360 ≤ 2862075323212034 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_5409 c22250R_180_2 (by norm_num)

theorem c22250R_180_0 : rowsJ2 180 181 0 360 ≤ 2873983942525787 :=
  rowsJ2_le_of_split 180 181 (by norm_num) (by norm_num) rows22250R_5408 c22250R_180_1 (by norm_num)

theorem hr22250R_180 : rows2 180 181 ≤ 2873983942525787 := rows2_le_of_rowsJ2 180 181 c22250R_180_0

theorem c22250R_181_17 : rowsJ2 181 182 57 360 ≤ 2634605266205657 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_5445 rows22250R_5446 (by norm_num)

theorem c22250R_181_16 : rowsJ2 181 182 56 360 ≤ 2644573142081095 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_5444 c22250R_181_17 (by norm_num)

theorem c22250R_181_15 : rowsJ2 181 182 55 360 ≤ 2655924172436655 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_5443 c22250R_181_16 (by norm_num)

theorem c22250R_181_14 : rowsJ2 181 182 54 360 ≤ 2668759432953824 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_5442 c22250R_181_15 (by norm_num)

theorem c22250R_181_13 : rowsJ2 181 182 53 360 ≤ 2683182884505796 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_5441 c22250R_181_14 (by norm_num)

theorem c22250R_181_12 : rowsJ2 181 182 52 360 ≤ 2699301608985247 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_5440 c22250R_181_13 (by norm_num)

theorem c22250R_181_11 : rowsJ2 181 182 51 360 ≤ 2717226058194831 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_5439 c22250R_181_12 (by norm_num)

theorem c22250R_181_10 : rowsJ2 181 182 50 360 ≤ 2737070317170287 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_5438 c22250R_181_11 (by norm_num)

theorem c22250R_181_9 : rowsJ2 181 182 49 360 ≤ 2757115431524224 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_5437 c22250R_181_10 (by norm_num)

theorem c22250R_181_8 : rowsJ2 181 182 48 360 ≤ 2775589717529536 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_5436 c22250R_181_9 (by norm_num)

theorem c22250R_181_7 : rowsJ2 181 182 47 360 ≤ 2792541031561995 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_5435 c22250R_181_8 (by norm_num)

theorem c22250R_181_6 : rowsJ2 181 182 46 360 ≤ 2808018402585229 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_5434 c22250R_181_7 (by norm_num)

theorem c22250R_181_5 : rowsJ2 181 182 45 360 ≤ 2822072216647095 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_5433 c22250R_181_6 (by norm_num)

theorem c22250R_181_4 : rowsJ2 181 182 44 360 ≤ 2834754409122181 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_5432 c22250R_181_5 (by norm_num)

theorem c22250R_181_3 : rowsJ2 181 182 43 360 ≤ 2846118665829977 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_5431 c22250R_181_4 (by norm_num)

theorem c22250R_181_2 : rowsJ2 181 182 41 360 ≤ 2865118145888452 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_5430 c22250R_181_3 (by norm_num)

theorem c22250R_181_1 : rowsJ2 181 182 39 360 ≤ 2879543471490932 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_5429 c22250R_181_2 (by norm_num)

theorem c22250R_181_0 : rowsJ2 181 182 0 360 ≤ 2893467258951609 :=
  rowsJ2_le_of_split 181 182 (by norm_num) (by norm_num) rows22250R_5428 c22250R_181_1 (by norm_num)

theorem hr22250R_181 : rows2 181 182 ≤ 2893467258951609 := rows2_le_of_rowsJ2 181 182 c22250R_181_0

theorem c22250R_182_18 : rowsJ2 182 183 57 360 ≤ 2647674162166055 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_5465 rows22250R_5466 (by norm_num)

theorem c22250R_182_17 : rowsJ2 182 183 56 360 ≤ 2657179466633908 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_5464 c22250R_182_18 (by norm_num)

theorem c22250R_182_16 : rowsJ2 182 183 55 360 ≤ 2668044725006621 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_5463 c22250R_182_17 (by norm_num)

theorem c22250R_182_15 : rowsJ2 182 183 54 360 ≤ 2680371744327266 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_5462 c22250R_182_16 (by norm_num)

theorem c22250R_182_14 : rowsJ2 182 183 53 360 ≤ 2694265188184476 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_5461 c22250R_182_15 (by norm_num)

theorem c22250R_182_13 : rowsJ2 182 183 52 360 ≤ 2709832814473729 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_5460 c22250R_182_14 (by norm_num)

theorem c22250R_182_12 : rowsJ2 182 183 51 360 ≤ 2727185726138770 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_5459 c22250R_182_13 (by norm_num)

theorem c22250R_182_11 : rowsJ2 182 183 50 360 ≤ 2746438636272793 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_5458 c22250R_182_12 (by norm_num)

theorem c22250R_182_10 : rowsJ2 182 183 49 360 ≤ 2767710149083988 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_5457 c22250R_182_11 (by norm_num)

theorem c22250R_182_9 : rowsJ2 182 183 48 360 ≤ 2787356784320992 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_5456 c22250R_182_10 (by norm_num)

theorem c22250R_182_8 : rowsJ2 182 183 47 360 ≤ 2805426767761021 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_5455 c22250R_182_9 (by norm_num)

theorem c22250R_182_7 : rowsJ2 182 183 46 360 ≤ 2821969414750324 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_5454 c22250R_182_8 (by norm_num)

theorem c22250R_182_6 : rowsJ2 182 183 45 360 ≤ 2837035316669884 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_5453 c22250R_182_7 (by norm_num)

theorem c22250R_182_5 : rowsJ2 182 183 44 360 ≤ 2850676534762273 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_5452 c22250R_182_6 (by norm_num)

theorem c22250R_182_4 : rowsJ2 182 183 43 360 ≤ 2862946802468815 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_5451 c22250R_182_5 (by norm_num)

theorem c22250R_182_3 : rowsJ2 182 183 42 360 ≤ 2873901737484952 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_5450 c22250R_182_4 (by norm_num)

theorem c22250R_182_2 : rowsJ2 182 183 40 360 ≤ 2892098852157936 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_5449 c22250R_182_3 (by norm_num)

theorem c22250R_182_1 : rowsJ2 182 183 38 360 ≤ 2905095942992254 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_5448 c22250R_182_2 (by norm_num)

theorem c22250R_182_0 : rowsJ2 182 183 0 360 ≤ 2915601569512720 :=
  rowsJ2_le_of_split 182 183 (by norm_num) (by norm_num) rows22250R_5447 c22250R_182_1 (by norm_num)

theorem hr22250R_182 : rows2 182 183 ≤ 2915601569512720 := rows2_le_of_rowsJ2 182 183 c22250R_182_0

theorem c22250R_183_17 : rowsJ2 183 184 56 360 ≤ 2664612472581964 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_5484 rows22250R_5485 (by norm_num)

theorem c22250R_183_16 : rowsJ2 183 184 55 360 ≤ 2674971973883773 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_5483 c22250R_183_17 (by norm_num)

theorem c22250R_183_15 : rowsJ2 183 184 54 360 ≤ 2686769902067853 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_5482 c22250R_183_16 (by norm_num)

theorem c22250R_183_14 : rowsJ2 183 184 53 360 ≤ 2700111654538466 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_5481 c22250R_183_15 (by norm_num)

theorem c22250R_183_13 : rowsJ2 183 184 52 360 ≤ 2715105694667856 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_5480 c22250R_183_14 (by norm_num)

theorem c22250R_183_12 : rowsJ2 183 184 51 360 ≤ 2731863804501265 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_5479 c22250R_183_13 (by norm_num)

theorem c22250R_183_11 : rowsJ2 183 184 50 360 ≤ 2750501351741845 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_5478 c22250R_183_12 (by norm_num)

theorem c22250R_183_10 : rowsJ2 183 184 49 360 ≤ 2771137572530147 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_5477 c22250R_183_11 (by norm_num)

theorem c22250R_183_9 : rowsJ2 183 184 48 360 ≤ 2791984800332410 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_5476 c22250R_183_10 (by norm_num)

theorem c22250R_183_8 : rowsJ2 183 184 47 360 ≤ 2811199965007146 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_5475 c22250R_183_9 (by norm_num)

theorem c22250R_183_7 : rowsJ2 183 184 46 360 ≤ 2828832726702368 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_5474 c22250R_183_8 (by norm_num)

theorem c22250R_183_6 : rowsJ2 183 184 45 360 ≤ 2844933936370896 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_5473 c22250R_183_7 (by norm_num)

theorem c22250R_183_5 : rowsJ2 183 184 44 360 ≤ 2859555831496284 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_5472 c22250R_183_6 (by norm_num)

theorem c22250R_183_4 : rowsJ2 183 184 43 360 ≤ 2872752239933878 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_5471 c22250R_183_5 (by norm_num)

theorem c22250R_183_3 : rowsJ2 183 184 42 360 ≤ 2884578793094075 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_5470 c22250R_183_4 (by norm_num)

theorem c22250R_183_2 : rowsJ2 183 184 40 360 ≤ 2904355231919242 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_5469 c22250R_183_3 (by norm_num)

theorem c22250R_183_1 : rowsJ2 183 184 38 360 ≤ 2918695974006218 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_5468 c22250R_183_2 (by norm_num)

theorem c22250R_183_0 : rowsJ2 183 184 0 360 ≤ 2931039590131509 :=
  rowsJ2_le_of_split 183 184 (by norm_num) (by norm_num) rows22250R_5467 c22250R_183_1 (by norm_num)

theorem hr22250R_183 : rows2 183 184 ≤ 2931039590131509 := rows2_le_of_rowsJ2 183 184 c22250R_183_0

theorem c22250R_184_16 : rowsJ2 184 185 55 360 ≤ 2690006941902895 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_5502 rows22250R_5503 (by norm_num)

theorem c22250R_184_15 : rowsJ2 184 185 54 360 ≤ 2701303205939000 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_5501 c22250R_184_16 (by norm_num)

theorem c22250R_184_14 : rowsJ2 184 185 53 360 ≤ 2714120295145719 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_5500 c22250R_184_15 (by norm_num)

theorem c22250R_184_13 : rowsJ2 184 185 52 360 ≤ 2728567418759226 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_5499 c22250R_184_14 (by norm_num)

theorem c22250R_184_12 : rowsJ2 184 185 51 360 ≤ 2744757076967402 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_5498 c22250R_184_13 (by norm_num)

theorem c22250R_184_11 : rowsJ2 184 185 50 360 ≤ 2762805329902953 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_5497 c22250R_184_12 (by norm_num)

theorem c22250R_184_10 : rowsJ2 184 185 49 360 ≤ 2782832082355083 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_5496 c22250R_184_11 (by norm_num)

theorem c22250R_184_9 : rowsJ2 184 185 48 360 ≤ 2804961385866430 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_5495 c22250R_184_10 (by norm_num)

theorem c22250R_184_8 : rowsJ2 184 185 47 360 ≤ 2825401919567629 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_5494 c22250R_184_9 (by norm_num)

theorem c22250R_184_7 : rowsJ2 184 185 46 360 ≤ 2844203762887259 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_5493 c22250R_184_8 (by norm_num)

theorem c22250R_184_6 : rowsJ2 184 185 45 360 ≤ 2861418096591031 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_5492 c22250R_184_7 (by norm_num)

theorem c22250R_184_5 : rowsJ2 184 185 44 360 ≤ 2877097400774023 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_5491 c22250R_184_6 (by norm_num)

theorem c22250R_184_4 : rowsJ2 184 185 43 360 ≤ 2891295660539086 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_5490 c22250R_184_5 (by norm_num)

theorem c22250R_184_3 : rowsJ2 184 185 42 360 ≤ 2904068580612005 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_5489 c22250R_184_4 (by norm_num)

theorem c22250R_184_2 : rowsJ2 184 185 40 360 ≤ 2925571179521355 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_5488 c22250R_184_3 (by norm_num)

theorem c22250R_184_1 : rowsJ2 184 185 38 360 ≤ 2941340846564882 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_5487 c22250R_184_2 (by norm_num)

theorem c22250R_184_0 : rowsJ2 184 185 0 360 ≤ 2955776997599017 :=
  rowsJ2_le_of_split 184 185 (by norm_num) (by norm_num) rows22250R_5486 c22250R_184_1 (by norm_num)

theorem hr22250R_184 : rows2 184 185 ≤ 2955776997599017 := rows2_le_of_rowsJ2 184 185 c22250R_184_0

theorem c22250R_185_16 : rowsJ2 185 186 54 360 ≤ 2716584707771699 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_5520 rows22250R_5521 (by norm_num)

theorem c22250R_185_15 : rowsJ2 185 186 53 360 ≤ 2728855174312546 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_5519 c22250R_185_16 (by norm_num)

theorem c22250R_185_14 : rowsJ2 185 186 52 360 ≤ 2742732547687011 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_5518 c22250R_185_15 (by norm_num)

theorem c22250R_185_13 : rowsJ2 185 186 51 360 ≤ 2758330077412021 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_5517 c22250R_185_14 (by norm_num)

theorem c22250R_185_12 : rowsJ2 185 186 50 360 ≤ 2775764545620796 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_5516 c22250R_185_13 (by norm_num)

theorem c22250R_185_11 : rowsJ2 185 186 49 360 ≤ 2795156553821001 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_5515 c22250R_185_12 (by norm_num)

theorem c22250R_185_10 : rowsJ2 185 186 48 360 ≤ 2816630826965779 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_5514 c22250R_185_11 (by norm_num)

theorem c22250R_185_9 : rowsJ2 185 186 47 360 ≤ 2838326944655406 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_5513 c22250R_185_10 (by norm_num)

theorem c22250R_185_8 : rowsJ2 185 186 46 360 ≤ 2858326226214421 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_5512 c22250R_185_9 (by norm_num)

theorem c22250R_185_7 : rowsJ2 185 186 45 360 ≤ 2876680246075783 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_5511 c22250R_185_8 (by norm_num)

theorem c22250R_185_6 : rowsJ2 185 186 44 360 ≤ 2893441786151685 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_5510 c22250R_185_7 (by norm_num)

theorem c22250R_185_5 : rowsJ2 185 186 43 360 ≤ 2908665043704742 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_5509 c22250R_185_6 (by norm_num)

theorem c22250R_185_4 : rowsJ2 185 186 42 360 ≤ 2922405847715692 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_5508 c22250R_185_5 (by norm_num)

theorem c22250R_185_3 : rowsJ2 185 186 41 360 ≤ 2934721885083056 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_5507 c22250R_185_4 (by norm_num)

theorem c22250R_185_2 : rowsJ2 185 186 39 360 ≤ 2955321134423103 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_5506 c22250R_185_3 (by norm_num)

theorem c22250R_185_1 : rowsJ2 185 186 37 360 ≤ 2968800662043073 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_5505 c22250R_185_2 (by norm_num)

theorem c22250R_185_0 : rowsJ2 185 186 0 360 ≤ 2979695616221645 :=
  rowsJ2_le_of_split 185 186 (by norm_num) (by norm_num) rows22250R_5504 c22250R_185_1 (by norm_num)

theorem hr22250R_185 : rows2 185 186 ≤ 2979695616221645 := rows2_le_of_rowsJ2 185 186 c22250R_185_0

theorem c22250R_186_15 : rowsJ2 186 187 53 360 ≤ 2738524893157979 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_5537 rows22250R_5538 (by norm_num)

theorem c22250R_186_14 : rowsJ2 186 187 52 360 ≤ 2751860390872653 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_5536 c22250R_186_15 (by norm_num)

theorem c22250R_186_13 : rowsJ2 186 187 51 360 ≤ 2766893292128447 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_5535 c22250R_186_14 (by norm_num)

theorem c22250R_186_12 : rowsJ2 186 187 50 360 ≤ 2783741142412303 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_5534 c22250R_186_13 (by norm_num)

theorem c22250R_186_11 : rowsJ2 186 187 49 360 ≤ 2802525280001798 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_5533 c22250R_186_12 (by norm_num)

theorem c22250R_186_10 : rowsJ2 186 187 48 360 ≤ 2823371142138070 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_5532 c22250R_186_11 (by norm_num)

theorem c22250R_186_9 : rowsJ2 186 187 47 360 ≤ 2846408590282077 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_5531 c22250R_186_10 (by norm_num)

theorem c22250R_186_8 : rowsJ2 186 187 46 360 ≤ 2867689653579091 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_5530 c22250R_186_9 (by norm_num)

theorem c22250R_186_7 : rowsJ2 186 187 45 360 ≤ 2887266381320727 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_5529 c22250R_186_8 (by norm_num)

theorem c22250R_186_6 : rowsJ2 186 187 44 360 ≤ 2905191933694939 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_5528 c22250R_186_7 (by norm_num)

theorem c22250R_186_5 : rowsJ2 186 187 43 360 ≤ 2921520792264359 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_5527 c22250R_186_6 (by norm_num)

theorem c22250R_186_4 : rowsJ2 186 187 42 360 ≤ 2936308978462390 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_5526 c22250R_186_5 (by norm_num)

theorem c22250R_186_3 : rowsJ2 186 187 41 360 ≤ 2949614281469931 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_5525 c22250R_186_4 (by norm_num)

theorem c22250R_186_2 : rowsJ2 186 187 39 360 ≤ 2972017677806758 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_5524 c22250R_186_3 (by norm_num)

theorem c22250R_186_1 : rowsJ2 186 187 37 360 ≤ 2986894875373780 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_5523 c22250R_186_2 (by norm_num)

theorem c22250R_186_0 : rowsJ2 186 187 0 360 ≤ 2999699267322428 :=
  rowsJ2_le_of_split 186 187 (by norm_num) (by norm_num) rows22250R_5522 c22250R_186_1 (by norm_num)

theorem hr22250R_186 : rows2 186 187 ≤ 2999699267322428 := rows2_le_of_rowsJ2 186 187 c22250R_186_0

theorem c22250R_187_14 : rowsJ2 187 188 52 360 ≤ 2761539703803615 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_5553 rows22250R_5554 (by norm_num)

theorem c22250R_187_13 : rowsJ2 187 188 51 360 ≤ 2775983917820856 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_5552 c22250R_187_14 (by norm_num)

theorem c22250R_187_12 : rowsJ2 187 188 50 360 ≤ 2792220207215109 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_5551 c22250R_187_13 (by norm_num)

theorem c22250R_187_11 : rowsJ2 187 188 49 360 ≤ 2810370678335608 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_5550 c22250R_187_12 (by norm_num)

theorem c22250R_187_10 : rowsJ2 187 188 48 360 ≤ 2830561510411922 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_5549 c22250R_187_11 (by norm_num)

theorem c22250R_187_9 : rowsJ2 187 188 47 360 ≤ 2852923282961002 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_5548 c22250R_187_10 (by norm_num)

theorem c22250R_187_8 : rowsJ2 187 188 46 360 ≤ 2875518479997563 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_5547 c22250R_187_9 (by norm_num)

theorem c22250R_187_7 : rowsJ2 187 188 45 360 ≤ 2896348270926432 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_5546 c22250R_187_8 (by norm_num)

theorem c22250R_187_6 : rowsJ2 187 188 44 360 ≤ 2915466264131249 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_5545 c22250R_187_7 (by norm_num)

theorem c22250R_187_5 : rowsJ2 187 188 43 360 ≤ 2932927290216393 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_5544 c22250R_187_6 (by norm_num)

theorem c22250R_187_4 : rowsJ2 187 188 42 360 ≤ 2948787623033451 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_5543 c22250R_187_5 (by norm_num)

theorem c22250R_187_3 : rowsJ2 187 188 41 360 ≤ 2963105209597012 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_5542 c22250R_187_4 (by norm_num)

theorem c22250R_187_2 : rowsJ2 187 188 39 360 ≤ 2987353751275987 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_5541 c22250R_187_3 (by norm_num)

theorem c22250R_187_1 : rowsJ2 187 188 37 360 ≤ 3003717958604050 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_5540 c22250R_187_2 (by norm_num)

theorem c22250R_187_0 : rowsJ2 187 188 0 360 ≤ 3018696956423132 :=
  rowsJ2_le_of_split 187 188 (by norm_num) (by norm_num) rows22250R_5539 c22250R_187_1 (by norm_num)

theorem hr22250R_187 : rows2 187 188 ≤ 3018696956423132 := rows2_le_of_rowsJ2 187 188 c22250R_187_0

theorem c22250R_188_14 : rowsJ2 188 189 51 360 ≤ 2785751297705590 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22250R_5569 rows22250R_5570 (by norm_num)

theorem c22250R_188_13 : rowsJ2 188 189 50 360 ≤ 2801404398521837 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22250R_5568 c22250R_188_14 (by norm_num)

theorem c22250R_188_12 : rowsJ2 188 189 49 360 ≤ 2818949228023382 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22250R_5567 c22250R_188_13 (by norm_num)

theorem c22250R_188_11 : rowsJ2 188 189 48 360 ≤ 2838512749881213 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22250R_5566 c22250R_188_12 (by norm_num)

theorem c22250R_188_10 : rowsJ2 188 189 47 360 ≤ 2860226302871998 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22250R_5565 c22250R_188_11 (by norm_num)

theorem c22250R_188_9 : rowsJ2 188 189 46 360 ≤ 2884225951557270 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22250R_5564 c22250R_188_10 (by norm_num)

theorem c22250R_188_8 : rowsJ2 188 189 45 360 ≤ 2906397602456111 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22250R_5563 c22250R_188_9 (by norm_num)

theorem c22250R_188_7 : rowsJ2 188 189 44 360 ≤ 2926795400815911 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22250R_5562 c22250R_188_8 (by norm_num)

theorem c22250R_188_6 : rowsJ2 188 189 43 360 ≤ 2945474609655903 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22250R_5561 c22250R_188_7 (by norm_num)

theorem c22250R_188_5 : rowsJ2 188 189 42 360 ≤ 2962491833792998 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22250R_5560 c22250R_188_6 (by norm_num)

theorem c22250R_188_4 : rowsJ2 188 189 41 360 ≤ 2977905252221096 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22250R_5559 c22250R_188_5 (by norm_num)

theorem c22250R_188_3 : rowsJ2 188 189 40 360 ≤ 2991774860331597 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22250R_5558 c22250R_188_4 (by norm_num)

theorem c22250R_188_2 : rowsJ2 188 189 38 360 ≤ 3014177867926682 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22250R_5557 c22250R_188_3 (by norm_num)

theorem c22250R_188_1 : rowsJ2 188 189 36 360 ≤ 3028168716041120 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22250R_5556 c22250R_188_2 (by norm_num)

theorem c22250R_188_0 : rowsJ2 188 189 0 360 ≤ 3039476238395610 :=
  rowsJ2_le_of_split 188 189 (by norm_num) (by norm_num) rows22250R_5555 c22250R_188_1 (by norm_num)

theorem hr22250R_188 : rows2 188 189 ≤ 3039476238395610 := rows2_le_of_rowsJ2 188 189 c22250R_188_0

theorem c22250R_189_13 : rowsJ2 189 190 50 360 ≤ 2811611928517281 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22250R_5584 rows22250R_5585 (by norm_num)

theorem c22250R_189_12 : rowsJ2 189 190 49 360 ≤ 2828524824045858 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22250R_5583 c22250R_189_13 (by norm_num)

theorem c22250R_189_11 : rowsJ2 189 190 48 360 ≤ 2847433848888228 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22250R_5582 c22250R_189_12 (by norm_num)

theorem c22250R_189_10 : rowsJ2 189 190 47 360 ≤ 2868471132535170 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22250R_5581 c22250R_189_11 (by norm_num)

theorem c22250R_189_9 : rowsJ2 189 190 46 360 ≤ 2891773505717783 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22250R_5580 c22250R_189_10 (by norm_num)

theorem c22250R_189_8 : rowsJ2 189 190 45 360 ≤ 2915321687783264 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22250R_5579 c22250R_189_9 (by norm_num)

theorem c22250R_189_7 : rowsJ2 189 190 44 360 ≤ 2937031814676679 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22250R_5578 c22250R_189_8 (by norm_num)

theorem c22250R_189_6 : rowsJ2 189 190 43 360 ≤ 2956959658533963 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22250R_5577 c22250R_189_7 (by norm_num)

theorem c22250R_189_5 : rowsJ2 189 190 42 360 ≤ 2975162226061005 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22250R_5576 c22250R_189_6 (by norm_num)

theorem c22250R_189_4 : rowsJ2 189 190 41 360 ≤ 2991697993832179 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22250R_5575 c22250R_189_5 (by norm_num)

theorem c22250R_189_3 : rowsJ2 189 190 40 360 ≤ 3006627152880410 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22250R_5574 c22250R_189_4 (by norm_num)

theorem c22250R_189_2 : rowsJ2 189 190 38 360 ≤ 3030936444098285 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22250R_5573 c22250R_189_3 (by norm_num)

theorem c22250R_189_1 : rowsJ2 189 190 36 360 ≤ 3046382359697895 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22250R_5572 c22250R_189_2 (by norm_num)

theorem c22250R_189_0 : rowsJ2 189 190 0 360 ≤ 3059675142313481 :=
  rowsJ2_le_of_split 189 190 (by norm_num) (by norm_num) rows22250R_5571 c22250R_189_1 (by norm_num)

theorem hr22250R_189 : rows2 189 190 ≤ 3059675142313481 := rows2_le_of_rowsJ2 189 190 c22250R_189_0

theorem c22250R_190_12 : rowsJ2 190 191 49 360 ≤ 2936481977126216 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22250R_5598 rows22250R_5599 (by norm_num)

theorem c22250R_190_11 : rowsJ2 190 191 48 360 ≤ 2954765431979387 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22250R_5597 c22250R_190_12 (by norm_num)

theorem c22250R_190_10 : rowsJ2 190 191 47 360 ≤ 2975155056160882 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22250R_5596 c22250R_190_11 (by norm_num)

theorem c22250R_190_9 : rowsJ2 190 191 46 360 ≤ 2997788490281138 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22250R_5595 c22250R_190_10 (by norm_num)

theorem c22250R_190_8 : rowsJ2 190 191 45 360 ≤ 3022808428950329 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22250R_5594 c22250R_190_9 (by norm_num)

theorem c22250R_190_7 : rowsJ2 190 191 44 360 ≤ 3045924458750004 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22250R_5593 c22250R_190_8 (by norm_num)

theorem c22250R_190_6 : rowsJ2 190 191 43 360 ≤ 3067192957944723 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22250R_5592 c22250R_190_7 (by norm_num)

theorem c22250R_190_5 : rowsJ2 190 191 42 360 ≤ 3086671426206609 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22250R_5591 c22250R_190_6 (by norm_num)

theorem c22250R_190_4 : rowsJ2 190 191 41 360 ≤ 3104418723365245 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22250R_5590 c22250R_190_5 (by norm_num)

theorem c22250R_190_3 : rowsJ2 190 191 40 360 ≤ 3120495316847755 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22250R_5589 c22250R_190_4 (by norm_num)

theorem c22250R_190_2 : rowsJ2 190 191 38 360 ≤ 3146818557482964 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22250R_5588 c22250R_190_3 (by norm_num)

theorem c22250R_190_1 : rowsJ2 190 191 36 360 ≤ 3163813226813697 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22250R_5587 c22250R_190_2 (by norm_num)

theorem c22250R_190_0 : rowsJ2 190 191 0 360 ≤ 3179367737691388 :=
  rowsJ2_le_of_split 190 191 (by norm_num) (by norm_num) rows22250R_5586 c22250R_190_1 (by norm_num)

theorem hr22250R_190 : rows2 190 191 ≤ 3179367737691388 := rows2_le_of_rowsJ2 190 191 c22250R_190_0

theorem c22250R_191_12 : rowsJ2 191 192 48 360 ≤ 3060531564056425 :=
  rowsJ2_le_of_split 191 192 (by norm_num) (by norm_num) rows22250R_5612 rows22250R_5613 (by norm_num)

theorem c22250R_191_11 : rowsJ2 191 192 47 360 ≤ 3080244858770983 :=
  rowsJ2_le_of_split 191 192 (by norm_num) (by norm_num) rows22250R_5611 c22250R_191_12 (by norm_num)

theorem c22250R_191_10 : rowsJ2 191 192 46 360 ≤ 3102179778812991 :=
  rowsJ2_le_of_split 191 192 (by norm_num) (by norm_num) rows22250R_5610 c22250R_191_11 (by norm_num)

theorem c22250R_191_9 : rowsJ2 191 192 45 360 ≤ 3126479836878331 :=
  rowsJ2_le_of_split 191 192 (by norm_num) (by norm_num) rows22250R_5609 c22250R_191_10 (by norm_num)

theorem c22250R_191_8 : rowsJ2 191 192 44 360 ≤ 3151038960867332 :=
  rowsJ2_le_of_split 191 192 (by norm_num) (by norm_num) rows22250R_5608 c22250R_191_9 (by norm_num)

theorem c22250R_191_7 : rowsJ2 191 192 43 360 ≤ 3173682993530934 :=
  rowsJ2_le_of_split 191 192 (by norm_num) (by norm_num) rows22250R_5607 c22250R_191_8 (by norm_num)

theorem c22250R_191_6 : rowsJ2 191 192 42 360 ≤ 3194470011806980 :=
  rowsJ2_le_of_split 191 192 (by norm_num) (by norm_num) rows22250R_5606 c22250R_191_7 (by norm_num)

theorem c22250R_191_5 : rowsJ2 191 192 41 360 ≤ 3213459336620065 :=
  rowsJ2_le_of_split 191 192 (by norm_num) (by norm_num) rows22250R_5605 c22250R_191_6 (by norm_num)

theorem c22250R_191_4 : rowsJ2 191 192 40 360 ≤ 3230711783689517 :=
  rowsJ2_le_of_split 191 192 (by norm_num) (by norm_num) rows22250R_5604 c22250R_191_5 (by norm_num)

theorem c22250R_191_3 : rowsJ2 191 192 39 360 ≤ 3246289924037875 :=
  rowsJ2_le_of_split 191 192 (by norm_num) (by norm_num) rows22250R_5603 c22250R_191_4 (by norm_num)

theorem c22250R_191_2 : rowsJ2 191 192 38 360 ≤ 3259160570939358 :=
  rowsJ2_le_of_split 191 192 (by norm_num) (by norm_num) rows22250R_5602 c22250R_191_3 (by norm_num)

theorem c22250R_191_1 : rowsJ2 191 192 35 360 ≤ 3284098104138240 :=
  rowsJ2_le_of_split 191 192 (by norm_num) (by norm_num) rows22250R_5601 c22250R_191_2 (by norm_num)

theorem c22250R_191_0 : rowsJ2 191 192 0 360 ≤ 3295843107236462 :=
  rowsJ2_le_of_split 191 192 (by norm_num) (by norm_num) rows22250R_5600 c22250R_191_1 (by norm_num)

theorem hr22250R_191 : rows2 191 192 ≤ 3295843107236462 := rows2_le_of_rowsJ2 191 192 c22250R_191_0

theorem c22250R_192_11 : rowsJ2 192 193 47 360 ≤ 3183902286245024 :=
  rowsJ2_le_of_split 192 193 (by norm_num) (by norm_num) rows22250R_5625 rows22250R_5626 (by norm_num)

theorem c22250R_192_10 : rowsJ2 192 193 46 360 ≤ 3205168238879307 :=
  rowsJ2_le_of_split 192 193 (by norm_num) (by norm_num) rows22250R_5624 c22250R_192_11 (by norm_num)

theorem c22250R_192_9 : rowsJ2 192 193 45 360 ≤ 3228777679864574 :=
  rowsJ2_le_of_split 192 193 (by norm_num) (by norm_num) rows22250R_5623 c22250R_192_10 (by norm_num)

theorem c22250R_192_8 : rowsJ2 192 193 44 360 ≤ 3254880398131223 :=
  rowsJ2_le_of_split 192 193 (by norm_num) (by norm_num) rows22250R_5622 c22250R_192_9 (by norm_num)

theorem c22250R_192_7 : rowsJ2 192 193 43 360 ≤ 3278998670166378 :=
  rowsJ2_le_of_split 192 193 (by norm_num) (by norm_num) rows22250R_5621 c22250R_192_8 (by norm_num)

theorem c22250R_192_6 : rowsJ2 192 193 42 360 ≤ 3301191256515899 :=
  rowsJ2_le_of_split 192 193 (by norm_num) (by norm_num) rows22250R_5620 c22250R_192_7 (by norm_num)

theorem c22250R_192_5 : rowsJ2 192 193 41 360 ≤ 3321518038877524 :=
  rowsJ2_le_of_split 192 193 (by norm_num) (by norm_num) rows22250R_5619 c22250R_192_6 (by norm_num)

theorem c22250R_192_4 : rowsJ2 192 193 40 360 ≤ 3340040274882059 :=
  rowsJ2_le_of_split 192 193 (by norm_num) (by norm_num) rows22250R_5618 c22250R_192_5 (by norm_num)

theorem c22250R_192_3 : rowsJ2 192 193 39 360 ≤ 3356820861898369 :=
  rowsJ2_le_of_split 192 193 (by norm_num) (by norm_num) rows22250R_5617 c22250R_192_4 (by norm_num)

theorem c22250R_192_2 : rowsJ2 192 193 37 360 ≤ 3382084143653716 :=
  rowsJ2_le_of_split 192 193 (by norm_num) (by norm_num) rows22250R_5616 c22250R_192_3 (by norm_num)

theorem c22250R_192_1 : rowsJ2 192 193 35 360 ≤ 3398133386234120 :=
  rowsJ2_le_of_split 192 193 (by norm_num) (by norm_num) rows22250R_5615 c22250R_192_2 (by norm_num)

theorem c22250R_192_0 : rowsJ2 192 193 0 360 ≤ 3411944172165728 :=
  rowsJ2_le_of_split 192 193 (by norm_num) (by norm_num) rows22250R_5614 c22250R_192_1 (by norm_num)

theorem hr22250R_192 : rows2 192 193 ≤ 3411944172165728 := rows2_le_of_rowsJ2 192 193 c22250R_192_0

theorem c22250R_193_10 : rowsJ2 193 194 46 360 ≤ 3306504472317426 :=
  rowsJ2_le_of_split 193 194 (by norm_num) (by norm_num) rows22250R_5637 rows22250R_5638 (by norm_num)

theorem c22250R_193_9 : rowsJ2 193 194 45 360 ≤ 3329392093951230 :=
  rowsJ2_le_of_split 193 194 (by norm_num) (by norm_num) rows22250R_5636 c22250R_193_10 (by norm_num)

theorem c22250R_193_8 : rowsJ2 193 194 44 360 ≤ 3354751267957710 :=
  rowsJ2_le_of_split 193 194 (by norm_num) (by norm_num) rows22250R_5635 c22250R_193_9 (by norm_num)

theorem c22250R_193_7 : rowsJ2 193 194 43 360 ≤ 3380383712626162 :=
  rowsJ2_le_of_split 193 194 (by norm_num) (by norm_num) rows22250R_5634 c22250R_193_8 (by norm_num)

theorem c22250R_193_6 : rowsJ2 193 194 42 360 ≤ 3404019305990828 :=
  rowsJ2_le_of_split 193 194 (by norm_num) (by norm_num) rows22250R_5633 c22250R_193_7 (by norm_num)

theorem c22250R_193_5 : rowsJ2 193 194 41 360 ≤ 3425718583350653 :=
  rowsJ2_le_of_split 193 194 (by norm_num) (by norm_num) rows22250R_5632 c22250R_193_6 (by norm_num)

theorem c22250R_193_4 : rowsJ2 193 194 40 360 ≤ 3445543329840422 :=
  rowsJ2_le_of_split 193 194 (by norm_num) (by norm_num) rows22250R_5631 c22250R_193_5 (by norm_num)

theorem c22250R_193_3 : rowsJ2 193 194 39 360 ≤ 3463556848122363 :=
  rowsJ2_le_of_split 193 194 (by norm_num) (by norm_num) rows22250R_5630 c22250R_193_4 (by norm_num)

theorem c22250R_193_2 : rowsJ2 193 194 37 360 ≤ 3490921671815984 :=
  rowsJ2_le_of_split 193 194 (by norm_num) (by norm_num) rows22250R_5629 c22250R_193_3 (by norm_num)

theorem c22250R_193_1 : rowsJ2 193 194 35 360 ≤ 3508585354109525 :=
  rowsJ2_le_of_split 193 194 (by norm_num) (by norm_num) rows22250R_5628 c22250R_193_2 (by norm_num)

theorem c22250R_193_0 : rowsJ2 193 194 0 360 ≤ 3524750420885265 :=
  rowsJ2_le_of_split 193 194 (by norm_num) (by norm_num) rows22250R_5627 c22250R_193_1 (by norm_num)

theorem hr22250R_193 : rows2 193 194 ≤ 3524750420885265 := rows2_le_of_rowsJ2 193 194 c22250R_193_0

theorem c22250R_194_9 : rowsJ2 194 195 45 360 ≤ 3428487314599352 :=
  rowsJ2_le_of_split 194 195 (by norm_num) (by norm_num) rows22250R_5648 rows22250R_5649 (by norm_num)

theorem c22250R_194_8 : rowsJ2 194 195 44 360 ≤ 3453133184849634 :=
  rowsJ2_le_of_split 194 195 (by norm_num) (by norm_num) rows22250R_5647 c22250R_194_9 (by norm_num)

theorem c22250R_194_7 : rowsJ2 194 195 43 360 ≤ 3480385978527661 :=
  rowsJ2_le_of_split 194 195 (by norm_num) (by norm_num) rows22250R_5646 c22250R_194_8 (by norm_num)

theorem c22250R_194_6 : rowsJ2 194 195 42 360 ≤ 3505568803193021 :=
  rowsJ2_le_of_split 194 195 (by norm_num) (by norm_num) rows22250R_5645 c22250R_194_7 (by norm_num)

theorem c22250R_194_5 : rowsJ2 194 195 41 360 ≤ 3528742964543565 :=
  rowsJ2_le_of_split 194 195 (by norm_num) (by norm_num) rows22250R_5644 c22250R_194_6 (by norm_num)

theorem c22250R_194_4 : rowsJ2 194 195 40 360 ≤ 3549970884517858 :=
  rowsJ2_le_of_split 194 195 (by norm_num) (by norm_num) rows22250R_5643 c22250R_194_5 (by norm_num)

theorem c22250R_194_3 : rowsJ2 194 195 39 360 ≤ 3569316373563473 :=
  rowsJ2_le_of_split 194 195 (by norm_num) (by norm_num) rows22250R_5642 c22250R_194_4 (by norm_num)

theorem c22250R_194_2 : rowsJ2 194 195 37 360 ≤ 3598900265539462 :=
  rowsJ2_le_of_split 194 195 (by norm_num) (by norm_num) rows22250R_5641 c22250R_194_3 (by norm_num)

theorem c22250R_194_1 : rowsJ2 194 195 34 360 ≤ 3624826531357486 :=
  rowsJ2_le_of_split 194 195 (by norm_num) (by norm_num) rows22250R_5640 c22250R_194_2 (by norm_num)

theorem c22250R_194_0 : rowsJ2 194 195 0 360 ≤ 3637035748518176 :=
  rowsJ2_le_of_split 194 195 (by norm_num) (by norm_num) rows22250R_5639 c22250R_194_1 (by norm_num)

theorem hr22250R_194 : rows2 194 195 ≤ 3637035748518176 := rows2_le_of_rowsJ2 194 195 c22250R_194_0

theorem c22250R_195_9 : rowsJ2 195 196 44 360 ≤ 3549756120272598 :=
  rowsJ2_le_of_split 195 196 (by norm_num) (by norm_num) rows22250R_5659 rows22250R_5660 (by norm_num)

theorem c22250R_195_8 : rowsJ2 195 196 43 360 ≤ 3576240591144441 :=
  rowsJ2_le_of_split 195 196 (by norm_num) (by norm_num) rows22250R_5658 c22250R_195_9 (by norm_num)

theorem c22250R_195_7 : rowsJ2 195 196 42 360 ≤ 3603013567827240 :=
  rowsJ2_le_of_split 195 196 (by norm_num) (by norm_num) rows22250R_5657 c22250R_195_8 (by norm_num)

theorem c22250R_195_6 : rowsJ2 195 196 41 360 ≤ 3627702840716930 :=
  rowsJ2_le_of_split 195 196 (by norm_num) (by norm_num) rows22250R_5656 c22250R_195_7 (by norm_num)

theorem c22250R_195_5 : rowsJ2 195 196 40 360 ≤ 3650371570977357 :=
  rowsJ2_le_of_split 195 196 (by norm_num) (by norm_num) rows22250R_5655 c22250R_195_6 (by norm_num)

theorem c22250R_195_4 : rowsJ2 195 196 39 360 ≤ 3671084171142045 :=
  rowsJ2_le_of_split 195 196 (by norm_num) (by norm_num) rows22250R_5654 c22250R_195_5 (by norm_num)

theorem c22250R_195_3 : rowsJ2 195 196 38 360 ≤ 3688541105957802 :=
  rowsJ2_le_of_split 195 196 (by norm_num) (by norm_num) rows22250R_5653 c22250R_195_4 (by norm_num)

theorem c22250R_195_2 : rowsJ2 195 196 36 360 ≤ 3714817487331323 :=
  rowsJ2_le_of_split 195 196 (by norm_num) (by norm_num) rows22250R_5652 c22250R_195_3 (by norm_num)

theorem c22250R_195_1 : rowsJ2 195 196 34 360 ≤ 3731507223301147 :=
  rowsJ2_le_of_split 195 196 (by norm_num) (by norm_num) rows22250R_5651 c22250R_195_2 (by norm_num)

theorem c22250R_195_0 : rowsJ2 195 196 0 360 ≤ 3745867801502199 :=
  rowsJ2_le_of_split 195 196 (by norm_num) (by norm_num) rows22250R_5650 c22250R_195_1 (by norm_num)

theorem hr22250R_195 : rows2 195 196 ≤ 3745867801502199 := rows2_le_of_rowsJ2 195 196 c22250R_195_0

theorem c22250R_196_8 : rowsJ2 196 197 43 360 ≤ 3670468476789418 :=
  rowsJ2_le_of_split 196 197 (by norm_num) (by norm_num) rows22250R_5669 rows22250R_5670 (by norm_num)

theorem c22250R_196_7 : rowsJ2 196 197 42 360 ≤ 3698943898238335 :=
  rowsJ2_le_of_split 196 197 (by norm_num) (by norm_num) rows22250R_5668 c22250R_196_8 (by norm_num)

theorem c22250R_196_6 : rowsJ2 196 197 41 360 ≤ 3725258448807933 :=
  rowsJ2_le_of_split 196 197 (by norm_num) (by norm_num) rows22250R_5667 c22250R_196_7 (by norm_num)

theorem c22250R_196_5 : rowsJ2 196 197 40 360 ≤ 3749476157426721 :=
  rowsJ2_le_of_split 196 197 (by norm_num) (by norm_num) rows22250R_5666 c22250R_196_6 (by norm_num)

theorem c22250R_196_4 : rowsJ2 196 197 39 360 ≤ 3771662158800135 :=
  rowsJ2_le_of_split 196 197 (by norm_num) (by norm_num) rows22250R_5665 c22250R_196_5 (by norm_num)

theorem c22250R_196_3 : rowsJ2 196 197 38 360 ≤ 3790408002325860 :=
  rowsJ2_le_of_split 196 197 (by norm_num) (by norm_num) rows22250R_5664 c22250R_196_4 (by norm_num)

theorem c22250R_196_2 : rowsJ2 196 197 36 360 ≤ 3818879299610972 :=
  rowsJ2_le_of_split 196 197 (by norm_num) (by norm_num) rows22250R_5663 c22250R_196_3 (by norm_num)

theorem c22250R_196_1 : rowsJ2 196 197 34 360 ≤ 3837253412920875 :=
  rowsJ2_le_of_split 196 197 (by norm_num) (by norm_num) rows22250R_5662 c22250R_196_2 (by norm_num)

theorem c22250R_196_0 : rowsJ2 196 197 0 360 ≤ 3854066668354238 :=
  rowsJ2_le_of_split 196 197 (by norm_num) (by norm_num) rows22250R_5661 c22250R_196_1 (by norm_num)

theorem hr22250R_196 : rows2 196 197 ≤ 3854066668354238 := rows2_le_of_rowsJ2 196 197 c22250R_196_0

theorem c22250R_197_7 : rowsJ2 197 198 42 360 ≤ 3790524516486046 :=
  rowsJ2_le_of_split 197 198 (by norm_num) (by norm_num) rows22250R_5678 rows22250R_5679 (by norm_num)

theorem c22250R_197_6 : rowsJ2 197 198 41 360 ≤ 3818510524918575 :=
  rowsJ2_le_of_split 197 198 (by norm_num) (by norm_num) rows22250R_5677 c22250R_197_7 (by norm_num)

theorem c22250R_197_5 : rowsJ2 197 198 40 360 ≤ 3844320480282665 :=
  rowsJ2_le_of_split 197 198 (by norm_num) (by norm_num) rows22250R_5676 c22250R_197_6 (by norm_num)

theorem c22250R_197_4 : rowsJ2 197 198 39 360 ≤ 3868020352691839 :=
  rowsJ2_le_of_split 197 198 (by norm_num) (by norm_num) rows22250R_5675 c22250R_197_5 (by norm_num)

theorem c22250R_197_3 : rowsJ2 197 198 38 360 ≤ 3888159246232287 :=
  rowsJ2_le_of_split 197 198 (by norm_num) (by norm_num) rows22250R_5674 c22250R_197_4 (by norm_num)

theorem c22250R_197_2 : rowsJ2 197 198 36 360 ≤ 3918949358785610 :=
  rowsJ2_le_of_split 197 198 (by norm_num) (by norm_num) rows22250R_5673 c22250R_197_3 (by norm_num)

theorem c22250R_197_1 : rowsJ2 197 198 33 360 ≤ 3945925825059081 :=
  rowsJ2_le_of_split 197 198 (by norm_num) (by norm_num) rows22250R_5672 c22250R_197_2 (by norm_num)

theorem c22250R_197_0 : rowsJ2 197 198 0 360 ≤ 3958627974364254 :=
  rowsJ2_le_of_split 197 198 (by norm_num) (by norm_num) rows22250R_5671 c22250R_197_1 (by norm_num)

theorem hr22250R_197 : rows2 197 198 ≤ 3958627974364254 := rows2_le_of_rowsJ2 197 198 c22250R_197_0

theorem c22250R_198_6 : rowsJ2 198 199 41 360 ≤ 3909980848205171 :=
  rowsJ2_le_of_split 198 199 (by norm_num) (by norm_num) rows22250R_5686 rows22250R_5687 (by norm_num)

theorem c22250R_198_5 : rowsJ2 198 199 40 360 ≤ 3937499622602298 :=
  rowsJ2_le_of_split 198 199 (by norm_num) (by norm_num) rows22250R_5685 c22250R_198_6 (by norm_num)

theorem c22250R_198_4 : rowsJ2 198 199 39 360 ≤ 3962827760259540 :=
  rowsJ2_le_of_split 198 199 (by norm_num) (by norm_num) rows22250R_5684 c22250R_198_5 (by norm_num)

theorem c22250R_198_3 : rowsJ2 198 199 38 360 ≤ 3984397369968326 :=
  rowsJ2_le_of_split 198 199 (by norm_num) (by norm_num) rows22250R_5683 c22250R_198_4 (by norm_num)

theorem c22250R_198_2 : rowsJ2 198 199 36 360 ≤ 4017636316932658 :=
  rowsJ2_le_of_split 198 199 (by norm_num) (by norm_num) rows22250R_5682 c22250R_198_3 (by norm_num)

theorem c22250R_198_1 : rowsJ2 198 199 33 360 ≤ 4047296608221547 :=
  rowsJ2_le_of_split 198 199 (by norm_num) (by norm_num) rows22250R_5681 c22250R_198_2 (by norm_num)

theorem c22250R_198_0 : rowsJ2 198 199 0 360 ≤ 4062241140928526 :=
  rowsJ2_le_of_split 198 199 (by norm_num) (by norm_num) rows22250R_5680 c22250R_198_1 (by norm_num)

theorem hr22250R_198 : rows2 198 199 ≤ 4062241140928526 := rows2_le_of_rowsJ2 198 199 c22250R_198_0

theorem c22250R_199_6 : rowsJ2 199 200 40 360 ≤ 4026145255124701 :=
  rowsJ2_le_of_split 199 200 (by norm_num) (by norm_num) rows22250R_5694 rows22250R_5695 (by norm_num)

theorem c22250R_199_5 : rowsJ2 199 200 39 360 ≤ 4053148247006056 :=
  rowsJ2_le_of_split 199 200 (by norm_num) (by norm_num) rows22250R_5693 c22250R_199_6 (by norm_num)

theorem c22250R_199_4 : rowsJ2 199 200 38 360 ≤ 4076260513593037 :=
  rowsJ2_le_of_split 199 200 (by norm_num) (by norm_num) rows22250R_5692 c22250R_199_5 (by norm_num)

theorem c22250R_199_3 : rowsJ2 199 200 37 360 ≤ 4095785203910657 :=
  rowsJ2_le_of_split 199 200 (by norm_num) (by norm_num) rows22250R_5691 c22250R_199_4 (by norm_num)

theorem c22250R_199_2 : rowsJ2 199 200 35 360 ≤ 4125432812522671 :=
  rowsJ2_le_of_split 199 200 (by norm_num) (by norm_num) rows22250R_5690 c22250R_199_3 (by norm_num)

theorem c22250R_199_1 : rowsJ2 199 200 33 360 ≤ 4144561904854511 :=
  rowsJ2_le_of_split 199 200 (by norm_num) (by norm_num) rows22250R_5689 c22250R_199_2 (by norm_num)

theorem c22250R_199_0 : rowsJ2 199 200 0 360 ≤ 4162063807190939 :=
  rowsJ2_le_of_split 199 200 (by norm_num) (by norm_num) rows22250R_5688 c22250R_199_1 (by norm_num)

theorem hr22250R_199 : rows2 199 200 ≤ 4162063807190939 := rows2_le_of_rowsJ2 199 200 c22250R_199_0

theorem c22250R_200_5 : rowsJ2 200 201 39 360 ≤ 4141614750503706 :=
  rowsJ2_le_of_split 200 201 (by norm_num) (by norm_num) rows22250R_5701 rows22250R_5702 (by norm_num)

theorem c22250R_200_4 : rowsJ2 200 201 38 360 ≤ 4166313108433100 :=
  rowsJ2_le_of_split 200 201 (by norm_num) (by norm_num) rows22250R_5700 c22250R_200_5 (by norm_num)

theorem c22250R_200_3 : rowsJ2 200 201 37 360 ≤ 4187296126261656 :=
  rowsJ2_le_of_split 200 201 (by norm_num) (by norm_num) rows22250R_5699 c22250R_200_4 (by norm_num)

theorem c22250R_200_2 : rowsJ2 200 201 35 360 ≤ 4219369036632190 :=
  rowsJ2_le_of_split 200 201 (by norm_num) (by norm_num) rows22250R_5698 c22250R_200_3 (by norm_num)

theorem c22250R_200_1 : rowsJ2 200 201 33 360 ≤ 4240369644069925 :=
  rowsJ2_le_of_split 200 201 (by norm_num) (by norm_num) rows22250R_5697 c22250R_200_2 (by norm_num)

theorem c22250R_200_0 : rowsJ2 200 201 0 360 ≤ 4260687806320796 :=
  rowsJ2_le_of_split 200 201 (by norm_num) (by norm_num) rows22250R_5696 c22250R_200_1 (by norm_num)

theorem hr22250R_200 : rows2 200 201 ≤ 4260687806320796 := rows2_le_of_rowsJ2 200 201 c22250R_200_0

theorem c22250R_201_4 : rowsJ2 201 202 38 360 ≤ 4252036280659276 :=
  rowsJ2_le_of_split 201 202 (by norm_num) (by norm_num) rows22250R_5707 rows22250R_5708 (by norm_num)

theorem c22250R_201_3 : rowsJ2 201 202 37 360 ≤ 4274518040453526 :=
  rowsJ2_le_of_split 201 202 (by norm_num) (by norm_num) rows22250R_5706 c22250R_201_4 (by norm_num)

theorem c22250R_201_2 : rowsJ2 201 202 35 360 ≤ 4309153586462728 :=
  rowsJ2_le_of_split 201 202 (by norm_num) (by norm_num) rows22250R_5705 c22250R_201_3 (by norm_num)

theorem c22250R_201_1 : rowsJ2 201 202 32 360 ≤ 4340050963473716 :=
  rowsJ2_le_of_split 201 202 (by norm_num) (by norm_num) rows22250R_5704 c22250R_201_2 (by norm_num)

theorem c22250R_201_0 : rowsJ2 201 202 0 360 ≤ 4355616203880897 :=
  rowsJ2_le_of_split 201 202 (by norm_num) (by norm_num) rows22250R_5703 c22250R_201_1 (by norm_num)

theorem hr22250R_201 : rows2 201 202 ≤ 4355616203880897 := rows2_le_of_rowsJ2 201 202 c22250R_201_0

theorem c22250R_202_3 : rowsJ2 202 203 37 360 ≤ 4359952928843208 :=
  rowsJ2_le_of_split 202 203 (by norm_num) (by norm_num) rows22250R_5712 rows22250R_5713 (by norm_num)

theorem c22250R_202_2 : rowsJ2 202 203 35 360 ≤ 4397293996816827 :=
  rowsJ2_le_of_split 202 203 (by norm_num) (by norm_num) rows22250R_5711 c22250R_202_3 (by norm_num)

theorem c22250R_202_1 : rowsJ2 202 203 32 360 ≤ 4431137834731166 :=
  rowsJ2_le_of_split 202 203 (by norm_num) (by norm_num) rows22250R_5710 c22250R_202_2 (by norm_num)

theorem c22250R_202_0 : rowsJ2 202 203 0 360 ≤ 4449371928156557 :=
  rowsJ2_le_of_split 202 203 (by norm_num) (by norm_num) rows22250R_5709 c22250R_202_1 (by norm_num)

theorem hr22250R_202 : rows2 202 203 ≤ 4449371928156557 := rows2_le_of_rowsJ2 202 203 c22250R_202_0

theorem c22250R_203_3 : rowsJ2 203 204 36 360 ≤ 4467216810834231 :=
  rowsJ2_le_of_split 203 204 (by norm_num) (by norm_num) rows22250R_5717 rows22250R_5718 (by norm_num)

theorem c22250R_203_2 : rowsJ2 203 204 34 360 ≤ 4500655074342757 :=
  rowsJ2_le_of_split 203 204 (by norm_num) (by norm_num) rows22250R_5716 c22250R_203_3 (by norm_num)

theorem c22250R_203_1 : rowsJ2 203 204 32 360 ≤ 4522544154084452 :=
  rowsJ2_le_of_split 203 204 (by norm_num) (by norm_num) rows22250R_5715 c22250R_203_2 (by norm_num)

theorem c22250R_203_0 : rowsJ2 203 204 0 360 ≤ 4543718491615149 :=
  rowsJ2_le_of_split 203 204 (by norm_num) (by norm_num) rows22250R_5714 c22250R_203_1 (by norm_num)

theorem hr22250R_203 : rows2 203 204 ≤ 4543718491615149 := rows2_le_of_rowsJ2 203 204 c22250R_203_0

theorem c22250R_204_2 : rowsJ2 204 205 34 360 ≤ 4590212506374901 :=
  rowsJ2_le_of_split 204 205 (by norm_num) (by norm_num) rows22250R_5721 rows22250R_5722 (by norm_num)

theorem c22250R_204_1 : rowsJ2 204 205 31 360 ≤ 4622426351270700 :=
  rowsJ2_le_of_split 204 205 (by norm_num) (by norm_num) rows22250R_5720 c22250R_204_2 (by norm_num)

theorem c22250R_204_0 : rowsJ2 204 205 0 360 ≤ 4638651884416225 :=
  rowsJ2_le_of_split 204 205 (by norm_num) (by norm_num) rows22250R_5719 c22250R_204_1 (by norm_num)

theorem hr22250R_204 : rows2 204 205 ≤ 4638651884416225 := rows2_le_of_rowsJ2 204 205 c22250R_204_0

theorem c22250R_205_2 : rowsJ2 205 206 34 360 ≤ 4679974566438844 :=
  rowsJ2_le_of_split 205 206 (by norm_num) (by norm_num) rows22250R_5725 rows22250R_5726 (by norm_num)

theorem c22250R_205_1 : rowsJ2 205 206 31 360 ≤ 4715271902685376 :=
  rowsJ2_le_of_split 205 206 (by norm_num) (by norm_num) rows22250R_5724 c22250R_205_2 (by norm_num)

theorem c22250R_205_0 : rowsJ2 205 206 0 360 ≤ 4734285105711407 :=
  rowsJ2_le_of_split 205 206 (by norm_num) (by norm_num) rows22250R_5723 c22250R_205_1 (by norm_num)

theorem hr22250R_205 : rows2 205 206 ≤ 4734285105711407 := rows2_le_of_rowsJ2 205 206 c22250R_205_0

theorem c22250R_206_1 : rowsJ2 206 207 31 360 ≤ 4808458212019341 :=
  rowsJ2_le_of_split 206 207 (by norm_num) (by norm_num) rows22250R_5728 rows22250R_5729 (by norm_num)

theorem c22250R_206_0 : rowsJ2 206 207 0 360 ≤ 4830543854865998 :=
  rowsJ2_le_of_split 206 207 (by norm_num) (by norm_num) rows22250R_5727 c22250R_206_1 (by norm_num)

theorem hr22250R_206 : rows2 206 207 ≤ 4830543854865998 := rows2_le_of_rowsJ2 206 207 c22250R_206_0

theorem c22250R_207_1 : rowsJ2 207 208 30 360 ≤ 4910495158117386 :=
  rowsJ2_le_of_split 207 208 (by norm_num) (by norm_num) rows22250R_5731 rows22250R_5732 (by norm_num)

theorem c22250R_207_0 : rowsJ2 207 208 0 360 ≤ 4927423667842282 :=
  rowsJ2_le_of_split 207 208 (by norm_num) (by norm_num) rows22250R_5730 c22250R_207_1 (by norm_num)

theorem hr22250R_207 : rows2 207 208 ≤ 4927423667842282 := rows2_le_of_rowsJ2 207 208 c22250R_207_0

theorem c22250R_208_1 : rowsJ2 208 209 30 360 ≤ 5005077169296423 :=
  rowsJ2_le_of_split 208 209 (by norm_num) (by norm_num) rows22250R_5734 rows22250R_5735 (by norm_num)

theorem c22250R_208_0 : rowsJ2 208 209 0 360 ≤ 5024920094538724 :=
  rowsJ2_le_of_split 208 209 (by norm_num) (by norm_num) rows22250R_5733 c22250R_208_1 (by norm_num)

theorem hr22250R_208 : rows2 208 209 ≤ 5024920094538724 := rows2_le_of_rowsJ2 208 209 c22250R_208_0

theorem c22250R_209_0 : rowsJ2 209 210 0 360 ≤ 5122953678801313 :=
  rowsJ2_le_of_split 209 210 (by norm_num) (by norm_num) rows22250R_5736 rows22250R_5737 (by norm_num)

theorem hr22250R_209 : rows2 209 210 ≤ 5122953678801313 := rows2_le_of_rowsJ2 209 210 c22250R_209_0

theorem c22250R_210_0 : rowsJ2 210 211 0 360 ≤ 5221517161795626 :=
  rowsJ2_le_of_split 210 211 (by norm_num) (by norm_num) rows22250R_5738 rows22250R_5739 (by norm_num)

theorem hr22250R_210 : rows2 210 211 ≤ 5221517161795626 := rows2_le_of_rowsJ2 210 211 c22250R_210_0

theorem c22250R_211_0 : rowsJ2 211 212 0 360 ≤ 5321167615156817 :=
  rowsJ2_le_of_split 211 212 (by norm_num) (by norm_num) rows22250R_5740 rows22250R_5741 (by norm_num)

theorem hr22250R_211 : rows2 211 212 ≤ 5321167615156817 := rows2_le_of_rowsJ2 211 212 c22250R_211_0

theorem c22250R_212_0 : rowsJ2 212 213 0 360 ≤ 5422386962253370 :=
  rowsJ2_le_of_split 212 213 (by norm_num) (by norm_num) rows22250R_5742 rows22250R_5743 (by norm_num)

theorem hr22250R_212 : rows2 212 213 ≤ 5422386962253370 := rows2_le_of_rowsJ2 212 213 c22250R_212_0

theorem c22250R_213_0 : rowsJ2 213 214 0 360 ≤ 5525168599878264 :=
  rowsJ2_le_of_split 213 214 (by norm_num) (by norm_num) rows22250R_5744 rows22250R_5745 (by norm_num)

theorem hr22250R_213 : rows2 213 214 ≤ 5525168599878264 := rows2_le_of_rowsJ2 213 214 c22250R_213_0

theorem t22250R_252 : rows2 355 360 ≤ 64422908934668919 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5794 rows22250R_5795 (by norm_num)

theorem t22250R_251 : rows2 353 360 ≤ 88757284364579403 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5793 t22250R_252 (by norm_num)

theorem t22250R_250 : rows2 351 360 ≤ 112332965081540940 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5792 t22250R_251 (by norm_num)

theorem t22250R_249 : rows2 349 360 ≤ 135196555405409711 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5791 t22250R_250 (by norm_num)

theorem t22250R_248 : rows2 346 360 ≤ 168236403169738423 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5790 t22250R_249 (by norm_num)

theorem t22250R_247 : rows2 343 360 ≤ 199830294350527744 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5789 t22250R_248 (by norm_num)

theorem t22250R_246 : rows2 340 360 ≤ 230131592656532200 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5788 t22250R_247 (by norm_num)

theorem t22250R_245 : rows2 289 360 ≤ 260034627171049053 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5787 t22250R_246 (by norm_num)

theorem t22250R_244 : rows2 287 360 ≤ 280034399672048754 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5786 t22250R_245 (by norm_num)

theorem t22250R_243 : rows2 285 360 ≤ 299931187938592360 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5785 t22250R_244 (by norm_num)

theorem t22250R_242 : rows2 283 360 ≤ 319728880544820320 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5784 t22250R_243 (by norm_num)

theorem t22250R_241 : rows2 281 360 ≤ 339418718570260943 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5783 t22250R_242 (by norm_num)

theorem t22250R_240 : rows2 279 360 ≤ 358999070131846992 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5782 t22250R_241 (by norm_num)

theorem t22250R_239 : rows2 277 360 ≤ 378475123513281257 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5781 t22250R_240 (by norm_num)

theorem t22250R_238 : rows2 275 360 ≤ 397839334418423209 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5780 t22250R_239 (by norm_num)

theorem t22250R_237 : rows2 273 360 ≤ 417091113227810753 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5779 t22250R_238 (by norm_num)

theorem t22250R_236 : rows2 271 360 ≤ 436236544706447975 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5778 t22250R_237 (by norm_num)

theorem t22250R_235 : rows2 269 360 ≤ 455268934888848248 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5777 t22250R_236 (by norm_num)

theorem t22250R_234 : rows2 267 360 ≤ 474188417497392778 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5776 t22250R_235 (by norm_num)

theorem t22250R_233 : rows2 265 360 ≤ 493001694910502324 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5775 t22250R_234 (by norm_num)

theorem t22250R_232 : rows2 263 360 ≤ 511702668197412878 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5774 t22250R_233 (by norm_num)

theorem t22250R_231 : rows2 261 360 ≤ 530291971175677412 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5773 t22250R_232 (by norm_num)

theorem t22250R_230 : rows2 259 360 ≤ 548776729127640232 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5772 t22250R_231 (by norm_num)

theorem t22250R_229 : rows2 257 360 ≤ 567151257003948598 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5771 t22250R_230 (by norm_num)

theorem t22250R_228 : rows2 255 360 ≤ 585434890477340866 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5770 t22250R_229 (by norm_num)

theorem t22250R_227 : rows2 253 360 ≤ 603626738491677908 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5769 t22250R_228 (by norm_num)

theorem t22250R_226 : rows2 251 360 ≤ 621726059460057690 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5768 t22250R_227 (by norm_num)

theorem t22250R_225 : rows2 249 360 ≤ 639732247323680515 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5767 t22250R_226 (by norm_num)

theorem t22250R_224 : rows2 247 360 ≤ 657279385004686250 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5766 t22250R_225 (by norm_num)

theorem t22250R_223 : rows2 245 360 ≤ 674387345655772333 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5765 t22250R_224 (by norm_num)

theorem t22250R_222 : rows2 243 360 ≤ 691074603661005017 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5764 t22250R_223 (by norm_num)

theorem t22250R_221 : rows2 241 360 ≤ 707358358017652062 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5763 t22250R_222 (by norm_num)

theorem t22250R_220 : rows2 239 360 ≤ 723254642505400678 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5762 t22250R_221 (by norm_num)

theorem t22250R_219 : rows2 237 360 ≤ 738778424276781394 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5761 t22250R_220 (by norm_num)

theorem t22250R_218 : rows2 235 360 ≤ 753943692273631720 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5760 t22250R_219 (by norm_num)

theorem t22250R_217 : rows2 233 360 ≤ 768768268839715608 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5759 t22250R_218 (by norm_num)

theorem t22250R_216 : rows2 231 360 ≤ 783273807356461134 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5758 t22250R_217 (by norm_num)

theorem t22250R_215 : rows2 229 360 ≤ 797481088152440715 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5757 t22250R_216 (by norm_num)

theorem t22250R_214 : rows2 227 360 ≤ 811410087841556491 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5756 t22250R_215 (by norm_num)

theorem t22250R_213 : rows2 225 360 ≤ 825080042850110806 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5755 t22250R_214 (by norm_num)

theorem t22250R_212 : rows2 223 360 ≤ 838509507765608683 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5754 t22250R_213 (by norm_num)

theorem t22250R_211 : rows2 221 360 ≤ 851483005675900305 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5753 t22250R_212 (by norm_num)

theorem t22250R_210 : rows2 220 360 ≤ 857786713997932238 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5752 t22250R_211 (by norm_num)

theorem t22250R_209 : rows2 219 360 ≤ 863971617228195652 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5751 t22250R_210 (by norm_num)

theorem t22250R_208 : rows2 218 360 ≤ 870040251779515889 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5750 t22250R_209 (by norm_num)

theorem t22250R_207 : rows2 217 360 ≤ 875995173052613444 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5749 t22250R_208 (by norm_num)

theorem t22250R_206 : rows2 216 360 ≤ 881838952233266889 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5748 t22250R_207 (by norm_num)

theorem t22250R_205 : rows2 215 360 ≤ 887574256511320873 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5747 t22250R_206 (by norm_num)

theorem t22250R_204 : rows2 214 360 ≤ 893203761240806281 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_5746 t22250R_205 (by norm_num)

theorem t22250R_203 : rows2 213 360 ≤ 898728929840684545 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_213 t22250R_204 (by norm_num)

theorem t22250R_202 : rows2 212 360 ≤ 904151316802937915 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_212 t22250R_203 (by norm_num)

theorem t22250R_201 : rows2 211 360 ≤ 909472484418094732 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_211 t22250R_202 (by norm_num)

theorem t22250R_200 : rows2 210 360 ≤ 914694001579890358 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_210 t22250R_201 (by norm_num)

theorem t22250R_199 : rows2 209 360 ≤ 919816955258691671 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_209 t22250R_200 (by norm_num)

theorem t22250R_198 : rows2 208 360 ≤ 924841875353230395 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_208 t22250R_199 (by norm_num)

theorem t22250R_197 : rows2 207 360 ≤ 929769299021072677 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_207 t22250R_198 (by norm_num)

theorem t22250R_196 : rows2 206 360 ≤ 934599842875938675 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_206 t22250R_197 (by norm_num)

theorem t22250R_195 : rows2 205 360 ≤ 939334127981650082 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_205 t22250R_196 (by norm_num)

theorem t22250R_194 : rows2 204 360 ≤ 943972779866066307 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_204 t22250R_195 (by norm_num)

theorem t22250R_193 : rows2 203 360 ≤ 948516498357681456 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_203 t22250R_194 (by norm_num)

theorem t22250R_192 : rows2 202 360 ≤ 952965870285838013 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_202 t22250R_193 (by norm_num)

theorem t22250R_191 : rows2 201 360 ≤ 957321486489718910 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_201 t22250R_192 (by norm_num)

theorem t22250R_190 : rows2 200 360 ≤ 961582174296039706 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_200 t22250R_191 (by norm_num)

theorem t22250R_189 : rows2 199 360 ≤ 965744238103230645 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_199 t22250R_190 (by norm_num)

theorem t22250R_188 : rows2 198 360 ≤ 969806479244159171 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_198 t22250R_189 (by norm_num)

theorem t22250R_187 : rows2 197 360 ≤ 973765107218523425 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_197 t22250R_188 (by norm_num)

theorem t22250R_186 : rows2 196 360 ≤ 977619173886877663 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_196 t22250R_187 (by norm_num)

theorem t22250R_185 : rows2 195 360 ≤ 981365041688379862 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_195 t22250R_186 (by norm_num)

theorem t22250R_184 : rows2 194 360 ≤ 985002077436898038 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_194 t22250R_185 (by norm_num)

theorem t22250R_183 : rows2 193 360 ≤ 988526827857783303 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_193 t22250R_184 (by norm_num)

theorem t22250R_182 : rows2 192 360 ≤ 991938772029949031 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_192 t22250R_183 (by norm_num)

theorem t22250R_181 : rows2 191 360 ≤ 995234615137185493 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_191 t22250R_182 (by norm_num)

theorem t22250R_180 : rows2 190 360 ≤ 998413982874876881 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_190 t22250R_181 (by norm_num)

theorem t22250R_179 : rows2 189 360 ≤ 1001473658017190362 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_189 t22250R_180 (by norm_num)

theorem t22250R_178 : rows2 188 360 ≤ 1004513134255585972 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_188 t22250R_179 (by norm_num)

theorem t22250R_177 : rows2 187 360 ≤ 1007531831212009104 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_187 t22250R_178 (by norm_num)

theorem t22250R_176 : rows2 186 360 ≤ 1010531530479331532 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_186 t22250R_177 (by norm_num)

theorem t22250R_175 : rows2 185 360 ≤ 1013511226095553177 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_185 t22250R_176 (by norm_num)

theorem t22250R_174 : rows2 184 360 ≤ 1016467003093152194 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_184 t22250R_175 (by norm_num)

theorem t22250R_173 : rows2 183 360 ≤ 1019398042683283703 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_183 t22250R_174 (by norm_num)

theorem t22250R_172 : rows2 182 360 ≤ 1022313644252796423 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_182 t22250R_173 (by norm_num)

theorem t22250R_171 : rows2 181 360 ≤ 1025207111511748032 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_181 t22250R_172 (by norm_num)

theorem t22250R_170 : rows2 180 360 ≤ 1028081095454273819 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_180 t22250R_171 (by norm_num)

theorem t22250R_169 : rows2 179 360 ≤ 1030942151916964668 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_179 t22250R_170 (by norm_num)

theorem t22250R_168 : rows2 178 360 ≤ 1033786472211434905 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_178 t22250R_169 (by norm_num)

theorem t22250R_167 : rows2 177 360 ≤ 1036613945199375076 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_177 t22250R_168 (by norm_num)

theorem t22250R_166 : rows2 176 360 ≤ 1039434034401120539 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_176 t22250R_167 (by norm_num)

theorem t22250R_165 : rows2 175 360 ≤ 1042240150290652000 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_175 t22250R_166 (by norm_num)

theorem t22250R_164 : rows2 174 360 ≤ 1045035044524725660 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_174 t22250R_165 (by norm_num)

theorem t22250R_163 : rows2 173 360 ≤ 1047825453867677432 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_173 t22250R_164 (by norm_num)

theorem t22250R_162 : rows2 172 360 ≤ 1050607604095301673 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_172 t22250R_163 (by norm_num)

theorem t22250R_161 : rows2 171 360 ≤ 1053381506180987961 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_171 t22250R_162 (by norm_num)

theorem t22250R_160 : rows2 170 360 ≤ 1056156739983151702 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_170 t22250R_161 (by norm_num)

theorem t22250R_159 : rows2 169 360 ≤ 1058926775605764368 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_169 t22250R_160 (by norm_num)

theorem t22250R_158 : rows2 168 360 ≤ 1061694420187281987 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_168 t22250R_159 (by norm_num)

theorem t22250R_157 : rows2 167 360 ≤ 1064465436425465358 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_167 t22250R_158 (by norm_num)

theorem t22250R_156 : rows2 166 360 ≤ 1067234915146006578 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_166 t22250R_157 (by norm_num)

theorem t22250R_155 : rows2 165 360 ≤ 1070001837043386108 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_165 t22250R_156 (by norm_num)

theorem t22250R_154 : rows2 164 360 ≤ 1072668474059948084 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_164 t22250R_155 (by norm_num)

theorem t22250R_153 : rows2 163 360 ≤ 1075226213357235183 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_163 t22250R_154 (by norm_num)

theorem t22250R_152 : rows2 162 360 ≤ 1077675229242079334 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_162 t22250R_153 (by norm_num)

theorem t22250R_151 : rows2 161 360 ≤ 1080019877521556249 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_161 t22250R_152 (by norm_num)

theorem t22250R_150 : rows2 160 360 ≤ 1082253648314547462 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_160 t22250R_151 (by norm_num)

theorem t22250R_149 : rows2 159 360 ≤ 1084374019854817337 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_159 t22250R_150 (by norm_num)

theorem t22250R_148 : rows2 158 360 ≤ 1086388027245893993 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_158 t22250R_149 (by norm_num)

theorem t22250R_147 : rows2 157 360 ≤ 1088286444295417813 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_157 t22250R_148 (by norm_num)

theorem t22250R_146 : rows2 156 360 ≤ 1090069502519758767 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_156 t22250R_147 (by norm_num)

theorem t22250R_145 : rows2 155 360 ≤ 1091741469214731028 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_155 t22250R_146 (by norm_num)

theorem t22250R_144 : rows2 154 360 ≤ 1093288785922993204 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_154 t22250R_145 (by norm_num)

theorem t22250R_143 : rows2 153 360 ≤ 1094709372848105294 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_153 t22250R_144 (by norm_num)

theorem t22250R_142 : rows2 152 360 ≤ 1096088834804125196 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_152 t22250R_143 (by norm_num)

theorem t22250R_141 : rows2 151 360 ≤ 1097337040789632612 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_151 t22250R_142 (by norm_num)

theorem t22250R_140 : rows2 150 360 ≤ 1098537004435274569 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_150 t22250R_141 (by norm_num)

theorem t22250R_139 : rows2 149 360 ≤ 1099600725550356067 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_149 t22250R_140 (by norm_num)

theorem t22250R_138 : rows2 148 360 ≤ 1100607962204700207 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_148 t22250R_139 (by norm_num)

theorem t22250R_137 : rows2 147 360 ≤ 1101473545912764652 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_147 t22250R_138 (by norm_num)

theorem t22250R_136 : rows2 146 360 ≤ 1102274935506529863 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_146 t22250R_137 (by norm_num)

theorem t22250R_135 : rows2 145 360 ≤ 1102928918432078508 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_145 t22250R_136 (by norm_num)

theorem t22250R_134 : rows2 144 360 ≤ 1103510225219130878 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_144 t22250R_135 (by norm_num)

theorem t22250R_133 : rows2 143 360 ≤ 1104088291197991019 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_143 t22250R_134 (by norm_num)

theorem t22250R_132 : rows2 142 360 ≤ 1104740665940499771 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_142 t22250R_133 (by norm_num)

theorem t22250R_131 : rows2 141 360 ≤ 1105393266590200583 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_141 t22250R_132 (by norm_num)

theorem t22250R_130 : rows2 140 360 ≤ 1106120629895397890 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_140 t22250R_131 (by norm_num)

theorem t22250R_129 : rows2 139 360 ≤ 1106848969622917784 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_139 t22250R_130 (by norm_num)

theorem t22250R_128 : rows2 138 360 ≤ 1107653423126708756 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_138 t22250R_129 (by norm_num)

theorem t22250R_127 : rows2 137 360 ≤ 1108460770118455076 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_137 t22250R_128 (by norm_num)

theorem t22250R_126 : rows2 136 360 ≤ 1109345853854788652 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_136 t22250R_127 (by norm_num)

theorem t22250R_125 : rows2 135 360 ≤ 1110236021920419927 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_135 t22250R_126 (by norm_num)

theorem t22250R_124 : rows2 134 360 ≤ 1111205999516849735 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_134 t22250R_125 (by norm_num)

theorem t22250R_123 : rows2 133 360 ≤ 1112181700190606715 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_133 t22250R_124 (by norm_num)

theorem t22250R_122 : rows2 132 360 ≤ 1113238998156376490 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_132 t22250R_123 (by norm_num)

theorem t22250R_121 : rows2 131 360 ≤ 1114302967556176230 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_131 t22250R_122 (by norm_num)

theorem t22250R_120 : rows2 130 360 ≤ 1115450691913733151 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_130 t22250R_121 (by norm_num)

theorem t22250R_119 : rows2 129 360 ≤ 1116606373670719795 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_129 t22250R_120 (by norm_num)

theorem t22250R_118 : rows2 128 360 ≤ 1117848413744481587 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_128 t22250R_119 (by norm_num)

theorem t22250R_117 : rows2 127 360 ≤ 1119100455114941077 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_127 t22250R_118 (by norm_num)

theorem t22250R_116 : rows2 126 360 ≤ 1120442163850024297 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_126 t22250R_117 (by norm_num)

theorem t22250R_115 : rows2 125 360 ≤ 1121796282779746068 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_125 t22250R_116 (by norm_num)

theorem t22250R_114 : rows2 124 360 ≤ 1123243950705013495 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_124 t22250R_115 (by norm_num)

theorem t22250R_113 : rows2 123 360 ≤ 1124705918804103778 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_123 t22250R_114 (by norm_num)

theorem t22250R_112 : rows2 122 360 ≤ 1126264597474913854 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_122 t22250R_113 (by norm_num)

theorem t22250R_111 : rows2 121 360 ≤ 1127839293493496758 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_121 t22250R_112 (by norm_num)

theorem t22250R_110 : rows2 120 360 ≤ 1129541696937190429 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_120 t22250R_111 (by norm_num)

theorem t22250R_109 : rows2 119 360 ≤ 1131096805478908943 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_119 t22250R_110 (by norm_num)

theorem t22250R_108 : rows2 118 360 ≤ 1132584905639076938 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_118 t22250R_109 (by norm_num)

theorem t22250R_107 : rows2 117 360 ≤ 1133917289585842687 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_117 t22250R_108 (by norm_num)

theorem t22250R_106 : rows2 116 360 ≤ 1135175585976392312 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_116 t22250R_107 (by norm_num)

theorem t22250R_105 : rows2 115 360 ≤ 1136270344713192455 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_115 t22250R_106 (by norm_num)

theorem t22250R_104 : rows2 114 360 ≤ 1137284556438116964 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_114 t22250R_105 (by norm_num)

theorem t22250R_103 : rows2 113 360 ≤ 1138127009653716838 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_113 t22250R_104 (by norm_num)

theorem t22250R_102 : rows2 112 360 ≤ 1138882132159808013 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_112 t22250R_103 (by norm_num)

theorem t22250R_101 : rows2 111 360 ≤ 1139455500202404009 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_111 t22250R_102 (by norm_num)

theorem t22250R_100 : rows2 110 360 ≤ 1139932932376743502 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_110 t22250R_101 (by norm_num)

theorem t22250R_99 : rows2 109 360 ≤ 1140189072396402879 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_109 t22250R_100 (by norm_num)

theorem t22250R_98 : rows2 108 360 ≤ 1140433295226218479 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_108 t22250R_99 (by norm_num)

theorem t22250R_97 : rows2 107 360 ≤ 1140666649568123988 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_107 t22250R_98 (by norm_num)

theorem t22250R_96 : rows2 106 360 ≤ 1140893529953965168 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_106 t22250R_97 (by norm_num)

theorem t22250R_95 : rows2 105 360 ≤ 1141114223355187070 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_105 t22250R_96 (by norm_num)

theorem t22250R_94 : rows2 104 360 ≤ 1141332205026022469 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_104 t22250R_95 (by norm_num)

theorem t22250R_93 : rows2 103 360 ≤ 1141548360658505456 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_103 t22250R_94 (by norm_num)

theorem t22250R_92 : rows2 102 360 ≤ 1141765069542238183 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_102 t22250R_93 (by norm_num)

theorem t22250R_91 : rows2 101 360 ≤ 1141981485220870954 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_101 t22250R_92 (by norm_num)

theorem t22250R_90 : rows2 100 360 ≤ 1142198604512250130 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_100 t22250R_91 (by norm_num)

theorem t22250R_89 : rows2 99 360 ≤ 1142412564265880697 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_99 t22250R_90 (by norm_num)

theorem t22250R_88 : rows2 98 360 ≤ 1142623213001764024 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_98 t22250R_89 (by norm_num)

theorem t22250R_87 : rows2 97 360 ≤ 1142825341445027680 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_97 t22250R_88 (by norm_num)

theorem t22250R_86 : rows2 96 360 ≤ 1143017848593688748 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_96 t22250R_87 (by norm_num)

theorem t22250R_85 : rows2 95 360 ≤ 1143194930118989117 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_95 t22250R_86 (by norm_num)

theorem t22250R_84 : rows2 94 360 ≤ 1143353726498514328 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_94 t22250R_85 (by norm_num)

theorem t22250R_83 : rows2 93 360 ≤ 1143486719468230426 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_93 t22250R_84 (by norm_num)

theorem t22250R_82 : rows2 92 360 ≤ 1143594108143955387 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_92 t22250R_83 (by norm_num)

theorem t22250R_81 : rows2 91 360 ≤ 1143678284479406824 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_91 t22250R_82 (by norm_num)

theorem t22250R_80 : rows2 90 360 ≤ 1143744247026575364 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_90 t22250R_81 (by norm_num)

theorem t22250R_79 : rows2 89 360 ≤ 1143794585240881746 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_89 t22250R_80 (by norm_num)

theorem t22250R_78 : rows2 88 360 ≤ 1143833239621434715 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_88 t22250R_79 (by norm_num)

theorem t22250R_77 : rows2 87 360 ≤ 1143861839186057298 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_87 t22250R_78 (by norm_num)

theorem t22250R_76 : rows2 86 360 ≤ 1143885735677867217 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_86 t22250R_77 (by norm_num)

theorem t22250R_75 : rows2 85 360 ≤ 1143905492369803035 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_85 t22250R_76 (by norm_num)

theorem t22250R_74 : rows2 84 360 ≤ 1143923846548561369 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_84 t22250R_75 (by norm_num)

theorem t22250R_73 : rows2 83 360 ≤ 1143941868851529872 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_83 t22250R_74 (by norm_num)

theorem t22250R_72 : rows2 82 360 ≤ 1143961368407994149 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_82 t22250R_73 (by norm_num)

theorem t22250R_71 : rows2 81 360 ≤ 1143985308799027435 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_81 t22250R_72 (by norm_num)

theorem t22250R_70 : rows2 80 360 ≤ 1144015110614577461 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_80 t22250R_71 (by norm_num)

theorem t22250R_69 : rows2 79 360 ≤ 1144052113074082508 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_79 t22250R_70 (by norm_num)

theorem t22250R_68 : rows2 78 360 ≤ 1144097922522862740 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_78 t22250R_69 (by norm_num)

theorem t22250R_67 : rows2 77 360 ≤ 1144152878120527600 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_77 t22250R_68 (by norm_num)

theorem t22250R_66 : rows2 76 360 ≤ 1144217301344670069 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_76 t22250R_67 (by norm_num)

theorem t22250R_65 : rows2 75 360 ≤ 1144290910816209943 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_75 t22250R_66 (by norm_num)

theorem t22250R_64 : rows2 74 360 ≤ 1144373383690772101 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_74 t22250R_65 (by norm_num)

theorem t22250R_63 : rows2 73 360 ≤ 1144464742939038524 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_73 t22250R_64 (by norm_num)

theorem t22250R_62 : rows2 72 360 ≤ 1144564980839294296 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_72 t22250R_63 (by norm_num)

theorem t22250R_61 : rows2 71 360 ≤ 1144673402474397434 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_71 t22250R_62 (by norm_num)

theorem t22250R_60 : rows2 70 360 ≤ 1144789330823393018 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_70 t22250R_61 (by norm_num)

theorem t22250R_59 : rows2 69 360 ≤ 1144910765163245355 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_69 t22250R_60 (by norm_num)

theorem t22250R_58 : rows2 68 360 ≤ 1145036020634547886 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_68 t22250R_59 (by norm_num)

theorem t22250R_57 : rows2 67 360 ≤ 1145162761772092592 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_67 t22250R_58 (by norm_num)

theorem t22250R_56 : rows2 66 360 ≤ 1145288909685905135 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_66 t22250R_57 (by norm_num)

theorem t22250R_55 : rows2 65 360 ≤ 1145411945320132830 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_65 t22250R_56 (by norm_num)

theorem t22250R_54 : rows2 64 360 ≤ 1145529388674186871 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_64 t22250R_55 (by norm_num)

theorem t22250R_53 : rows2 63 360 ≤ 1145637792853679031 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_63 t22250R_54 (by norm_num)

theorem t22250R_52 : rows2 62 360 ≤ 1145735307766807901 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_62 t22250R_53 (by norm_num)

theorem t22250R_51 : rows2 61 360 ≤ 1145821451320412207 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_61 t22250R_52 (by norm_num)

theorem t22250R_50 : rows2 60 360 ≤ 1145896091785919741 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_60 t22250R_51 (by norm_num)

theorem t22250R_49 : rows2 59 360 ≤ 1145959559206598229 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_59 t22250R_50 (by norm_num)

theorem t22250R_48 : rows2 58 360 ≤ 1146012611089244628 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_58 t22250R_49 (by norm_num)

theorem t22250R_47 : rows2 57 360 ≤ 1146056204019331094 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_57 t22250R_48 (by norm_num)

theorem t22250R_46 : rows2 56 360 ≤ 1146091587279545300 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_56 t22250R_47 (by norm_num)

theorem t22250R_45 : rows2 55 360 ≤ 1146120113213846765 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_55 t22250R_46 (by norm_num)

theorem t22250R_44 : rows2 54 360 ≤ 1146143118159008247 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_54 t22250R_45 (by norm_num)

theorem t22250R_43 : rows2 53 360 ≤ 1146161703743027959 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_53 t22250R_44 (by norm_num)

theorem t22250R_42 : rows2 52 360 ≤ 1146176802627281757 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_52 t22250R_43 (by norm_num)

theorem t22250R_41 : rows2 51 360 ≤ 1146189348373635317 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_51 t22250R_42 (by norm_num)

theorem t22250R_40 : rows2 50 360 ≤ 1146200354967044493 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_50 t22250R_41 (by norm_num)

theorem t22250R_39 : rows2 49 360 ≤ 1146210505207470988 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_49 t22250R_40 (by norm_num)

theorem t22250R_38 : rows2 48 360 ≤ 1146220340536733362 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_48 t22250R_39 (by norm_num)

theorem t22250R_37 : rows2 47 360 ≤ 1146230373157676030 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_47 t22250R_38 (by norm_num)

theorem t22250R_36 : rows2 46 360 ≤ 1146241172966644082 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_46 t22250R_37 (by norm_num)

theorem t22250R_35 : rows2 45 360 ≤ 1146252898384850963 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_45 t22250R_36 (by norm_num)

theorem t22250R_34 : rows2 44 360 ≤ 1146265572814826816 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_44 t22250R_35 (by norm_num)

theorem t22250R_33 : rows2 43 360 ≤ 1146279183892977664 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_43 t22250R_34 (by norm_num)

theorem t22250R_32 : rows2 42 360 ≤ 1146293855504685772 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_42 t22250R_33 (by norm_num)

theorem t22250R_31 : rows2 41 360 ≤ 1146309501763996163 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_41 t22250R_32 (by norm_num)

theorem t22250R_30 : rows2 40 360 ≤ 1146325995757301549 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_40 t22250R_31 (by norm_num)

theorem t22250R_29 : rows2 39 360 ≤ 1146343176798517160 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_39 t22250R_30 (by norm_num)

theorem t22250R_28 : rows2 38 360 ≤ 1146360667694602238 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_38 t22250R_29 (by norm_num)

theorem t22250R_27 : rows2 37 360 ≤ 1146378331102625215 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_37 t22250R_28 (by norm_num)

theorem t22250R_26 : rows2 36 360 ≤ 1146396049298275864 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_36 t22250R_27 (by norm_num)

theorem t22250R_25 : rows2 35 360 ≤ 1146413754102892284 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_35 t22250R_26 (by norm_num)

theorem t22250R_24 : rows2 34 360 ≤ 1146431437002077111 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_34 t22250R_25 (by norm_num)

theorem t22250R_23 : rows2 33 360 ≤ 1146449123476627940 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_33 t22250R_24 (by norm_num)

theorem t22250R_22 : rows2 32 360 ≤ 1146466753283862229 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_32 t22250R_23 (by norm_num)

theorem t22250R_21 : rows2 31 360 ≤ 1146484196740654968 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_31 t22250R_22 (by norm_num)

theorem t22250R_20 : rows2 30 360 ≤ 1146501268016552417 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_30 t22250R_21 (by norm_num)

theorem t22250R_19 : rows2 29 360 ≤ 1146517746475427558 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_29 t22250R_20 (by norm_num)

theorem t22250R_18 : rows2 28 360 ≤ 1146533401736608498 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_28 t22250R_19 (by norm_num)

theorem t22250R_17 : rows2 27 360 ≤ 1146548018082118841 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_27 t22250R_18 (by norm_num)

theorem t22250R_16 : rows2 26 360 ≤ 1146561392682087080 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_26 t22250R_17 (by norm_num)

theorem t22250R_15 : rows2 25 360 ≤ 1146573373901564369 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_25 t22250R_16 (by norm_num)

theorem t22250R_14 : rows2 24 360 ≤ 1146583841725622383 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_24 t22250R_15 (by norm_num)

theorem t22250R_13 : rows2 23 360 ≤ 1146592759278053506 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_23 t22250R_14 (by norm_num)

theorem t22250R_12 : rows2 22 360 ≤ 1146600195176839345 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_22 t22250R_13 (by norm_num)

theorem t22250R_11 : rows2 21 360 ≤ 1146606330849780396 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_21 t22250R_12 (by norm_num)

theorem t22250R_10 : rows2 20 360 ≤ 1146611441350242741 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_20 t22250R_11 (by norm_num)

theorem t22250R_9 : rows2 19 360 ≤ 1146615843524195491 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_19 t22250R_10 (by norm_num)

theorem t22250R_8 : rows2 18 360 ≤ 1146619826564053500 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_18 t22250R_9 (by norm_num)

theorem t22250R_7 : rows2 17 360 ≤ 1146623678215901536 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_17 t22250R_8 (by norm_num)

theorem t22250R_6 : rows2 16 360 ≤ 1146627560870142497 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_16 t22250R_7 (by norm_num)

theorem t22250R_5 : rows2 15 360 ≤ 1146631529791258280 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_15 t22250R_6 (by norm_num)

theorem t22250R_4 : rows2 14 360 ≤ 1146635542307692914 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22250R_14 t22250R_5 (by norm_num)

theorem t22250R_3 : rows2 13 360 ≤ 1146639483370580888 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_3 t22250R_4 (by norm_num)

theorem t22250R_2 : rows2 12 360 ≤ 1146643198021307909 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_2 t22250R_3 (by norm_num)

theorem t22250R_1 : rows2 10 360 ≤ 1146649375562376485 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_1 t22250R_2 (by norm_num)

theorem t22250R_0 : rows2 0 360 ≤ 1146656663135250298 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22250R_0 t22250R_1 (by norm_num)

/-- **The refined certificate on `grid22250R`**: the loss's bound is less than `K`, the 5796 parts checked by the
kernel. -/
theorem total2_lt_22250R : total2 < K := by
  rw [total2_eq_rows2_full]
  exact lt_of_le_of_lt t22250R_0 (by decide +kernel)

end

end SieveCert

#print axioms SieveCert.total2_lt_22250R
