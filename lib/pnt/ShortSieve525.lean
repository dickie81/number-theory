/-
# θ = 21/40: the certificate's 204 root cells

The certificates of the root cells, one module each (`ShortSieve525Ckkjj`, `ShortSieve525Okkjj`, written by
`tools/short/enc/cells.py`), assembled by `ShortSieveCert.primes_of_certs`: for large `x` and
`x^{21/40} ≤ y ≤ x^{1−ρ}`, `π(x) − π(x − y) ≥ (1 − L/2^50 − ε) y/log x` with
`L = 16717861072716289` (`14.848443`: region C `14.238056`, outside it `0.610387`), given Li's
Lemmas 3.1, 3.2 and 4.1 (`ShortSieveCert.Hyps`). The bound is positive when `L < 2^50`.

The file imports the 204 cell modules.
-/
import ShortSieve525C0202
import ShortSieve525C0203
import ShortSieve525C0204
import ShortSieve525C0205
import ShortSieve525C0206
import ShortSieve525C0207
import ShortSieve525C0208
import ShortSieve525C0209
import ShortSieve525C0302
import ShortSieve525C0303
import ShortSieve525C0304
import ShortSieve525C0305
import ShortSieve525C0306
import ShortSieve525C0307
import ShortSieve525C0308
import ShortSieve525C0309
import ShortSieve525C0402
import ShortSieve525C0403
import ShortSieve525C0404
import ShortSieve525C0405
import ShortSieve525C0406
import ShortSieve525C0407
import ShortSieve525C0408
import ShortSieve525C0409
import ShortSieve525C0502
import ShortSieve525C0503
import ShortSieve525C0504
import ShortSieve525C0505
import ShortSieve525C0506
import ShortSieve525C0507
import ShortSieve525C0508
import ShortSieve525C0509
import ShortSieve525C0602
import ShortSieve525C0603
import ShortSieve525C0604
import ShortSieve525C0605
import ShortSieve525C0606
import ShortSieve525C0607
import ShortSieve525C0608
import ShortSieve525C0609
import ShortSieve525C0702
import ShortSieve525C0703
import ShortSieve525C0704
import ShortSieve525C0705
import ShortSieve525C0706
import ShortSieve525C0707
import ShortSieve525C0708
import ShortSieve525C0709
import ShortSieve525C0802
import ShortSieve525C0803
import ShortSieve525C0804
import ShortSieve525C0805
import ShortSieve525C0806
import ShortSieve525C0807
import ShortSieve525C0808
import ShortSieve525C0809
import ShortSieve525C0902
import ShortSieve525C0903
import ShortSieve525C0904
import ShortSieve525C0905
import ShortSieve525C0906
import ShortSieve525C0907
import ShortSieve525C0908
import ShortSieve525C0909
import ShortSieve525C1002
import ShortSieve525C1003
import ShortSieve525C1004
import ShortSieve525C1005
import ShortSieve525C1006
import ShortSieve525C1007
import ShortSieve525C1008
import ShortSieve525C1009
import ShortSieve525C1102
import ShortSieve525C1103
import ShortSieve525C1104
import ShortSieve525C1105
import ShortSieve525C1106
import ShortSieve525C1107
import ShortSieve525C1108
import ShortSieve525C1109
import ShortSieve525C1202
import ShortSieve525C1203
import ShortSieve525C1204
import ShortSieve525C1205
import ShortSieve525C1206
import ShortSieve525C1207
import ShortSieve525C1208
import ShortSieve525C1209
import ShortSieve525C1302
import ShortSieve525C1303
import ShortSieve525C1304
import ShortSieve525C1305
import ShortSieve525C1306
import ShortSieve525C1307
import ShortSieve525C1308
import ShortSieve525C1309
import ShortSieve525C1402
import ShortSieve525C1403
import ShortSieve525C1404
import ShortSieve525C1405
import ShortSieve525C1406
import ShortSieve525C1407
import ShortSieve525C1408
import ShortSieve525C1409
import ShortSieve525C1502
import ShortSieve525C1503
import ShortSieve525C1504
import ShortSieve525C1505
import ShortSieve525C1506
import ShortSieve525C1507
import ShortSieve525C1508
import ShortSieve525C1509
import ShortSieve525C1602
import ShortSieve525C1603
import ShortSieve525C1604
import ShortSieve525C1605
import ShortSieve525C1606
import ShortSieve525C1607
import ShortSieve525C1608
import ShortSieve525C1609
import ShortSieve525C1702
import ShortSieve525C1703
import ShortSieve525C1704
import ShortSieve525C1705
import ShortSieve525C1706
import ShortSieve525C1707
import ShortSieve525C1708
import ShortSieve525C1709
import ShortSieve525C1802
import ShortSieve525C1803
import ShortSieve525C1804
import ShortSieve525C1805
import ShortSieve525C1806
import ShortSieve525C1807
import ShortSieve525C1808
import ShortSieve525C1809
import ShortSieve525C1902
import ShortSieve525C1903
import ShortSieve525C1904
import ShortSieve525C1905
import ShortSieve525C1906
import ShortSieve525C1907
import ShortSieve525C1908
import ShortSieve525C1909
import ShortSieve525O1008
import ShortSieve525O1009
import ShortSieve525O1010
import ShortSieve525O1011
import ShortSieve525O1012
import ShortSieve525O1013
import ShortSieve525O1108
import ShortSieve525O1109
import ShortSieve525O1110
import ShortSieve525O1111
import ShortSieve525O1112
import ShortSieve525O1113
import ShortSieve525O1208
import ShortSieve525O1209
import ShortSieve525O1210
import ShortSieve525O1211
import ShortSieve525O1212
import ShortSieve525O1213
import ShortSieve525O1308
import ShortSieve525O1309
import ShortSieve525O1310
import ShortSieve525O1311
import ShortSieve525O1312
import ShortSieve525O1313
import ShortSieve525O1408
import ShortSieve525O1409
import ShortSieve525O1410
import ShortSieve525O1411
import ShortSieve525O1412
import ShortSieve525O1413
import ShortSieve525O1508
import ShortSieve525O1509
import ShortSieve525O1510
import ShortSieve525O1511
import ShortSieve525O1512
import ShortSieve525O1513
import ShortSieve525O1608
import ShortSieve525O1609
import ShortSieve525O1610
import ShortSieve525O1611
import ShortSieve525O1612
import ShortSieve525O1613
import ShortSieve525O1708
import ShortSieve525O1709
import ShortSieve525O1710
import ShortSieve525O1711
import ShortSieve525O1712
import ShortSieve525O1713
import ShortSieve525O1808
import ShortSieve525O1809
import ShortSieve525O1810
import ShortSieve525O1811
import ShortSieve525O1812
import ShortSieve525O1813
import ShortSieve525O1908
import ShortSieve525O1909
import ShortSieve525O1910
import ShortSieve525O1911
import ShortSieve525O1912
import ShortSieve525O1913

/-! The certificates of the root cells, their losses (units `2^-50`), and the lower bound for primes. -/

namespace ShortSieve525

open ShortSieveCert Finset Filter

/-- The certificates of region C's cells `(k, j)`, `2 ≤ k ≤ 19`, `2 ≤ j ≤ 9`, in the order of `(k, j)`. -/
noncomputable def certsC : List Cert := [
    C0202, C0203, C0204, C0205, C0206, C0207, C0208, C0209, C0302, C0303,
    C0304, C0305, C0306, C0307, C0308, C0309, C0402, C0403, C0404, C0405,
    C0406, C0407, C0408, C0409, C0502, C0503, C0504, C0505, C0506, C0507,
    C0508, C0509, C0602, C0603, C0604, C0605, C0606, C0607, C0608, C0609,
    C0702, C0703, C0704, C0705, C0706, C0707, C0708, C0709, C0802, C0803,
    C0804, C0805, C0806, C0807, C0808, C0809, C0902, C0903, C0904, C0905,
    C0906, C0907, C0908, C0909, C1002, C1003, C1004, C1005, C1006, C1007,
    C1008, C1009, C1102, C1103, C1104, C1105, C1106, C1107, C1108, C1109,
    C1202, C1203, C1204, C1205, C1206, C1207, C1208, C1209, C1302, C1303,
    C1304, C1305, C1306, C1307, C1308, C1309, C1402, C1403, C1404, C1405,
    C1406, C1407, C1408, C1409, C1502, C1503, C1504, C1505, C1506, C1507,
    C1508, C1509, C1602, C1603, C1604, C1605, C1606, C1607, C1608, C1609,
    C1702, C1703, C1704, C1705, C1706, C1707, C1708, C1709, C1802, C1803,
    C1804, C1805, C1806, C1807, C1808, C1809, C1902, C1903, C1904, C1905,
    C1906, C1907, C1908, C1909]

/-- The certificates of the cells `(k, j)` outside region C, `10 ≤ k ≤ 19`, `8 ≤ j ≤ 13`. -/
noncomputable def certsO : List Cert := [
    O1008, O1009, O1010, O1011, O1012, O1013, O1108, O1109, O1110, O1111,
    O1112, O1113, O1208, O1209, O1210, O1211, O1212, O1213, O1308, O1309,
    O1310, O1311, O1312, O1313, O1408, O1409, O1410, O1411, O1412, O1413,
    O1508, O1509, O1510, O1511, O1512, O1513, O1608, O1609, O1610, O1611,
    O1612, O1613, O1708, O1709, O1710, O1711, O1712, O1713, O1808, O1809,
    O1810, O1811, O1812, O1813, O1908, O1909, O1910, O1911, O1912, O1913]

/-- The losses of region C's cells. -/
def lossesC : List ℕ := [
    1104541038824058, 1, 0, 0, 0, 0,
    0, 0, 1237085963304526, 360816739374649, 1, 0,
    0, 0, 0, 0, 775387809304162, 477161728706419,
    161042083478564, 1, 0, 0, 0, 0,
    777596891229078, 388798445614540, 233279067368724, 85535658058420, 1, 0,
    0, 0, 515753040297436, 328206480065424, 196923888039254, 131282592026170,
    50793860024699, 1, 0, 0, 568049677037920, 284024838518960,
    170414903111376, 113609935407585, 81149953862561, 32604892186647, 1, 0,
    375543953260562, 250362635435796, 150217581261477, 100145054174319, 71532181553085, 53782229266122,
    22248741830360, 1, 447707301015418, 223853650507710, 134312190304626, 89541460203084,
    63958185859346, 48144385668245, 37445633297524, 15597967525252, 283405148065586, 202432248545558,
    121459349127335, 80972899418223, 57837785298731, 43537267422547, 33861704973000, 26360033828466,
    369519183853474, 184759591926738, 110855755156043, 73903836770696, 52788454836212, 39736394869835,
    30838753894155, 16244675508363, 212411738314177, 169929390568256, 101957634340953, 67971756227303,
    48688002118671, 36546851468952, 28176870316726, 7497964296613, 314612128823807, 157306064411904,
    94383638647142, 62922425764762, 45109256670292, 33831942502719, 25756742666774, 0,
    146430583529291, 146430583415646, 87858350049387, 58572233366259, 41990592011639, 31484928446532,
    16254366780719, 0, 273926177596710, 136963088798355, 82177853279013, 54785235519343,
    39275683045398, 29327829007345, 7649777718038, 0, 31659572056596, 128646544507076,
    77187926704245, 51622403387074, 36890821835834, 27253023487874, 11775702639721, 0,
    242565875164994, 121282937582497, 72769762549498, 48690916362475, 34779225973196, 26281510440727,
    24765269453812, 1, 0, 0, 68830346832569, 46055017130846,
    32862643393616, 26770963671675, 25376642647169, 11768877758578, 107395374879638, 108826359181274,
    65295815508764, 43690029764688, 30934390196890, 27512591719415, 26262019368607, 25678418937323]

/-- The losses of the cells outside region C. -/
def lossesO : List ℕ := [
    0, 7801979234718, 12538430789481, 1, 0, 0,
    0, 15569803915553, 23079944623183, 11653226175881, 1, 0,
    1, 23585970908147, 22554084680946, 21870627569436, 11187542008144, 1,
    7557878156202, 23198487100424, 22270547616441, 21692091834235, 21413988092200, 7135610928524,
    15548141579780, 23034283817299, 22211630823863, 21745652554875, 19933514841397, 1,
    24238123003888, 23083926670410, 22373652003674, 22034657275714, 9695249208249, 0,
    24392526877785, 23350111199296, 22766358419367, 20696689471510, 1, 0,
    11654244448520, 23848037251877, 23414436573842, 10180189821969, 0, 0,
    0, 24607653476113, 22146888127751, 1, 0, 0,
    0, 12163461601890, 11005036695233, 0, 0, 0]

/-- The certificate of a root cell. -/
noncomputable def cert (r : Bool) (c : ℕ × ℕ) : Cert :=
  if r then certsC.getD ((c.1 - 2) * 8 + (c.2 - 2)) .out else certsO.getD ((c.1 - 10) * 6 + (c.2 - 8)) .out

/-- The loss of a root cell. -/
def loss (r : Bool) (c : ℕ × ℕ) : ℕ :=
  if r then lossesC.getD ((c.1 - 2) * 8 + (c.2 - 2)) 0 else lossesO.getD ((c.1 - 10) * 6 + (c.2 - 8)) 0

theorem run_cert : ∀ r, ∀ c ∈ ShortSieveThree.cells r,
    run 1 (cert r c) (.std 1) (cellCons c.1 r) (cellBox c.1 c.2) true = some (loss r c) := by
  rintro (_ | _) ⟨k, j⟩ hc <;>
    simp only [ShortSieveThree.cells, Bool.false_eq_true, ↓reduceIte, mem_product, mem_Icc] at hc <;>
    obtain ⟨⟨hk₁, hk₂⟩, hj₁, hj₂⟩ := hc <;> interval_cases k <;> interval_cases j
  exacts [
    O1008_run, O1009_run, O1010_run, O1011_run, O1012_run, O1013_run, O1108_run, O1109_run,
    O1110_run, O1111_run, O1112_run, O1113_run, O1208_run, O1209_run, O1210_run, O1211_run,
    O1212_run, O1213_run, O1308_run, O1309_run, O1310_run, O1311_run, O1312_run, O1313_run,
    O1408_run, O1409_run, O1410_run, O1411_run, O1412_run, O1413_run, O1508_run, O1509_run,
    O1510_run, O1511_run, O1512_run, O1513_run, O1608_run, O1609_run, O1610_run, O1611_run,
    O1612_run, O1613_run, O1708_run, O1709_run, O1710_run, O1711_run, O1712_run, O1713_run,
    O1808_run, O1809_run, O1810_run, O1811_run, O1812_run, O1813_run, O1908_run, O1909_run,
    O1910_run, O1911_run, O1912_run, O1913_run, C0202_run, C0203_run, C0204_run, C0205_run,
    C0206_run, C0207_run, C0208_run, C0209_run, C0302_run, C0303_run, C0304_run, C0305_run,
    C0306_run, C0307_run, C0308_run, C0309_run, C0402_run, C0403_run, C0404_run, C0405_run,
    C0406_run, C0407_run, C0408_run, C0409_run, C0502_run, C0503_run, C0504_run, C0505_run,
    C0506_run, C0507_run, C0508_run, C0509_run, C0602_run, C0603_run, C0604_run, C0605_run,
    C0606_run, C0607_run, C0608_run, C0609_run, C0702_run, C0703_run, C0704_run, C0705_run,
    C0706_run, C0707_run, C0708_run, C0709_run, C0802_run, C0803_run, C0804_run, C0805_run,
    C0806_run, C0807_run, C0808_run, C0809_run, C0902_run, C0903_run, C0904_run, C0905_run,
    C0906_run, C0907_run, C0908_run, C0909_run, C1002_run, C1003_run, C1004_run, C1005_run,
    C1006_run, C1007_run, C1008_run, C1009_run, C1102_run, C1103_run, C1104_run, C1105_run,
    C1106_run, C1107_run, C1108_run, C1109_run, C1202_run, C1203_run, C1204_run, C1205_run,
    C1206_run, C1207_run, C1208_run, C1209_run, C1302_run, C1303_run, C1304_run, C1305_run,
    C1306_run, C1307_run, C1308_run, C1309_run, C1402_run, C1403_run, C1404_run, C1405_run,
    C1406_run, C1407_run, C1408_run, C1409_run, C1502_run, C1503_run, C1504_run, C1505_run,
    C1506_run, C1507_run, C1508_run, C1509_run, C1602_run, C1603_run, C1604_run, C1605_run,
    C1606_run, C1607_run, C1608_run, C1609_run, C1702_run, C1703_run, C1704_run, C1705_run,
    C1706_run, C1707_run, C1708_run, C1709_run, C1802_run, C1803_run, C1804_run, C1805_run,
    C1806_run, C1807_run, C1808_run, C1809_run, C1902_run, C1903_run, C1904_run, C1905_run,
    C1906_run, C1907_run, C1908_run, C1909_run]

theorem loss_sum : ∑ c ∈ ShortSieveThree.cells true, loss true c + ∑ c ∈ ShortSieveThree.cells false, loss false c =
    16717861072716289 := by
  decide +kernel

/-- **The lower bound for primes in short intervals at `θ = 21/40` from the certificate.** With Li's
Lemmas 3.1, 3.2 and 4.1 (`Hyps`), `π(x) − π(x − y) ≥ (1 − L/2^50 − ε) y/log x` for large `x` and
`x^{21/40} ≤ y ≤ x^{1−ρ}`, with the certificate's loss `L = 16717861072716289`. -/
theorem primes_525 {ρ c : ℝ} (H : Hyps ρ c) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ^ (21 / 40 : ℝ) ≤ y → y ≤ x ^ (1 - ρ) →
      (1 - (16717861072716289 : ℝ) / SC - ε) * y / Real.log x ≤ ((Ioc ⌊x - y⌋₊ ⌊x⌋₊).filter Nat.Prime).card := by
  have h : ∑ c ∈ ShortSieveThree.cells true, (loss true c : ℝ) / SC +
      ∑ c ∈ ShortSieveThree.cells false, (loss false c : ℝ) / SC = (16717861072716289 : ℝ) / SC := by
    rw [← sum_div, ← sum_div, ← add_div]
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ) / SC) loss_sum
  simpa only [h] using primes_of_certs H one_pos cert loss run_cert

end ShortSieve525
