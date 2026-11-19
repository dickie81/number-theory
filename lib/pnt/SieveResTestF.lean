/-
# The resonant window's tests in the kernel's fastest form are the tests

`SieveResTestFDefs.lean` writes `resYH` and `resXH`, and the functions that they call, again in the form that the
kernel evaluates fastest: a list by its recursor, `cond` and `&&` as the recursor of `Bool` (`andF` at the head of a
body), and the piece of an interval's end by bisection in both tests. This file proves that they are the same
functions, so that a search may call either and its soundness is that of the other.

* `rec_cond`, `cond_and`, `andF_eq`: the recursor of `Bool` is `cond`; with `false` in the case `false`, `&&`.
* `minNF_eq` … `pieceCF_eq`: the functions that branch, by definition. `pieceC_eq_pieceOf`: the piece by bisection
  is the piece by the scan, on each of the eighteen ranges of an end that the pieces' tops cut (`ble_t`, `ble_f`).
* `addTermsF_eq` … `sndSumF_eq`: the functions on lists, by induction on the list.
* `chkIF_eq` … `resYHF_eq`, `resXHF_eq`: the tests, from those. **`resYHF_eq`**: the test at the two corners;
  **`resXHF_eq`**: the test with the lines named by the hint.

The file imports `SieveResTestFDefs.lean` only.
-/
import SieveResTestFDefs

namespace SieveResTest

universe u

/-- The recursor of `Bool` with a constant motive is `cond`. -/
theorem rec_cond {α : Sort u} (c : Bool) (t e : α) : Bool.rec (motive := fun _ => α) e t c = cond c t e := by
  cases c <;> rfl

/-- `cond a b false` is `a && b` (the recursor of `Bool` with `false` in the case `false`, by `rec_cond`). -/
theorem cond_and (a b : Bool) : cond a b false = (a && b) := by
  cases a <;> rfl

/-- `andF a b` is `a && b`. -/
theorem andF_eq (a b : Bool) : andF a b = (a && b) := by
  cases a <;> rfl

/-! ### The functions that branch -/

theorem minNF_eq : minNF = minN := by funext a b; simp only [minNF, minN, rec_cond]

theorem maxNF_eq : maxNF = maxN := by funext a b; simp only [maxNF, maxN, rec_cond]

theorem clampLF_eq : clampLF = clampL := by funext c1 yuP yuN ydP ydN a b cc; simp only [clampLF, clampL, rec_cond]

theorem mkTmKF_eq : mkTmKF = mkTmK := by funext lo k0; simp only [mkTmKF, mkTmK, rec_cond]

theorem mkTmF_eq : mkTmF = mkTm := by funext lo; simp only [mkTmF, mkTm, mkTmKF_eq]

theorem lvGF_eq : lvGF = lvG := by funext lo hi k; simp only [lvGF, lvG, rec_cond, cond_and, maxNF_eq]

theorem lvValF_eq : lvValF = lvVal := by funext lo k x; simp only [lvValF, lvVal, maxNF_eq]

theorem lvUF_eq : lvUF = lvU := by funext lo k g a x; simp only [lvUF, lvU, rec_cond, lvValF_eq]

theorem mkTvF_eq : mkTvF = mkTv := by funext ub lo; simp only [mkTvF, mkTv, mkTmKF_eq, lvGF_eq]

theorem mkTvHF_eq : mkTvHF = mkTvH := by funext lo hi; simp only [mkTvHF, mkTvH, mkTmKF_eq, lvGF_eq]


theorem pieceCF_eq : pieceCF = pieceC := by funext b; simp only [pieceCF, pieceC, rec_cond]

/-- `Nat.ble b t` is `true` where `b ≤ t`. -/
theorem ble_t {b t : Nat} (h : b ≤ t) : Nat.ble b t = true := Nat.ble_eq_true_of_le h

/-- `Nat.ble b t` is `false` where `t < b`. -/
theorem ble_f {b t : Nat} (h : t < b) : Nat.ble b t = false := by
  cases hb : Nat.ble b t
  · rfl
  · exact absurd (Nat.le_of_ble_eq_true hb) (Nat.not_le_of_gt h)

/-- **The piece by bisection is the piece by the scan**: `pieceC` compares `b` with the tops of the pieces that
`pieceOf` scans (`get tFT p`, increasing in `p`); on each of the eighteen ranges of `b` that they cut, both are its
piece. -/
theorem pieceC_eq_pieceOf : pieceC = pieceOf := by
  funext b
  have hs : pieceOf b =
      cond (Nat.ble b 6210403838148882377) 0 (cond (Nat.ble b 6327432045883067909) 1
        (cond (Nat.ble b 6506976623818538820) 2 (cond (Nat.ble b 6689141809598112703) 3
        (cond (Nat.ble b 6873985410747762418) 4 (cond (Nat.ble b 7061566947609045205) 5
        (cond (Nat.ble b 7251947717250131954) 6 (cond (Nat.ble b 7445190860260040799) 7
        (cond (Nat.ble b 7641361430578972243) 8 (cond (Nat.ble b 7840526468526980238) 9
        (cond (Nat.ble b 8042755077203197321) 10 (cond (Nat.ble b 8248118502438512073) 11
        (cond (Nat.ble b 8456690216496028348) 12 (cond (Nat.ble b 8668546005725876889) 13
        (cond (Nat.ble b 8883764062394065609) 14 (cond (Nat.ble b 9102425080919114670) 15
        (cond (Nat.ble b 9154280273435530746) 16 17)))))))))))))))) := rfl
  rw [hs, pieceC]
  by_cases h0 : b ≤ 6210403838148882377
  · simp (disch := omega) only [ble_t, Bool.cond_true]
  by_cases h1 : b ≤ 6327432045883067909
  · simp (disch := omega) only [ble_t, ble_f, Bool.cond_true, Bool.cond_false]
  by_cases h2 : b ≤ 6506976623818538820
  · simp (disch := omega) only [ble_t, ble_f, Bool.cond_true, Bool.cond_false]
  by_cases h3 : b ≤ 6689141809598112703
  · simp (disch := omega) only [ble_t, ble_f, Bool.cond_true, Bool.cond_false]
  by_cases h4 : b ≤ 6873985410747762418
  · simp (disch := omega) only [ble_t, ble_f, Bool.cond_true, Bool.cond_false]
  by_cases h5 : b ≤ 7061566947609045205
  · simp (disch := omega) only [ble_t, ble_f, Bool.cond_true, Bool.cond_false]
  by_cases h6 : b ≤ 7251947717250131954
  · simp (disch := omega) only [ble_t, ble_f, Bool.cond_true, Bool.cond_false]
  by_cases h7 : b ≤ 7445190860260040799
  · simp (disch := omega) only [ble_t, ble_f, Bool.cond_true, Bool.cond_false]
  by_cases h8 : b ≤ 7641361430578972243
  · simp (disch := omega) only [ble_t, ble_f, Bool.cond_true, Bool.cond_false]
  by_cases h9 : b ≤ 7840526468526980238
  · simp (disch := omega) only [ble_t, ble_f, Bool.cond_true, Bool.cond_false]
  by_cases h10 : b ≤ 8042755077203197321
  · simp (disch := omega) only [ble_t, ble_f, Bool.cond_true, Bool.cond_false]
  by_cases h11 : b ≤ 8248118502438512073
  · simp (disch := omega) only [ble_t, ble_f, Bool.cond_true, Bool.cond_false]
  by_cases h12 : b ≤ 8456690216496028348
  · simp (disch := omega) only [ble_t, ble_f, Bool.cond_true, Bool.cond_false]
  by_cases h13 : b ≤ 8668546005725876889
  · simp (disch := omega) only [ble_t, ble_f, Bool.cond_true, Bool.cond_false]
  by_cases h14 : b ≤ 8883764062394065609
  · simp (disch := omega) only [ble_t, ble_f, Bool.cond_true, Bool.cond_false]
  by_cases h15 : b ≤ 9102425080919114670
  · simp (disch := omega) only [ble_t, ble_f, Bool.cond_true, Bool.cond_false]
  by_cases h16 : b ≤ 9154280273435530746
  · simp (disch := omega) only [ble_t, ble_f, Bool.cond_true, Bool.cond_false]
  simp (disch := omega) only [ble_f, Bool.cond_false]

/-! ### The functions on lists -/

theorem addTermsF_eq (dS iax : Nat) :
    ∀ (ts : List Tm) (h p0 n0 n1 : Nat), addTermsF dS iax ts h p0 n0 n1 = addTerms dS iax ts h p0 n0 n1 := by
  intro ts
  induction ts with
  | nil => intro h p0 n0 n1; rfl
  | cons t ts ih =>
    intro h p0 n0 n1
    simp only [addTermsF] at ih ⊢
    simp only [ih]
    simp only [addTerms, rec_cond]

theorem addTerms2F_eq (dS iax a b : Nat) :
    ∀ (vs : List Tv) (h p0 n0 n1 va vb : Nat),
      addTerms2F dS iax a b vs h p0 n0 n1 va vb = addTerms2 dS iax a b vs h p0 n0 n1 va vb := by
  intro vs
  induction vs with
  | nil => intro h p0 n0 n1 va vb; rfl
  | cons v vs ih =>
    intro h p0 n0 n1 va vb
    simp only [addTerms2F] at ih ⊢
    simp only [ih]
    simp only [addTerms2, rec_cond, lvUF_eq]

theorem hpSumF_eq : ∀ ts : List Tm, hpSumF ts = hpSum ts := by
  intro ts
  induction ts with
  | nil => rfl
  | cons t ts ih => exact congrArg (Nat.add (mulF t.lo HP)) ih

theorem hpSum2F_eq : ∀ vs : List Tv, hpSum2F vs = hpSum2 vs := by
  intro vs
  induction vs with
  | nil => rfl
  | cons v vs ih => exact congrArg (Nat.add (mulF v.t.lo HP)) ih

theorem sumNF_eq : ∀ xs : List Nat, sumNF xs = sumN xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (Nat.add x) ih

theorem lenTF_eq : ∀ ts : List Tm, lenTF ts = ts.length := by
  intro ts
  induction ts with
  | nil => rfl
  | cons t ts ih => exact congrArg Nat.succ ih

theorem lenVF_eq : ∀ vs : List Tv, lenVF vs = lenV vs := by
  intro vs
  induction vs with
  | nil => rfl
  | cons v vs ih => exact congrArg Nat.succ ih

theorem lenVF_length : ∀ vs : List Tv, lenVF vs = vs.length := by
  intro vs
  induction vs with
  | nil => rfl
  | cons v vs ih => exact congrArg Nat.succ ih

theorem okYF_eq (Lnum Lden : Nat) : ∀ cells : List (Nat × Nat), okYF Lnum Lden cells = okY Lnum Lden cells := by
  intro cells
  induction cells with
  | nil => rfl
  | cons c cs ih =>
    simp only [okYF] at ih ⊢
    simp only [ih]
    simp only [okY, rec_cond, cond_and]

theorem mapTmF_eq (Lnum Lden : Nat) :
    ∀ cs : List Nat, mapTmF Lnum Lden cs = cs.map fun c => mkTmF (loOf Lnum Lden c) := by
  intro cs
  induction cs with
  | nil => rfl
  | cons c cs ih => exact congrArg (List.cons (mkTmF (loOf Lnum Lden c))) ih

theorem mapLoOfF_eq (Lnum Lden : Nat) : ∀ cs : List Nat, mapLoOfF Lnum Lden cs = cs.map (loOf Lnum Lden) := by
  intro cs
  induction cs with
  | nil => rfl
  | cons c cs ih => exact congrArg (List.cons (loOf Lnum Lden c)) ih

theorem mapTvF_eq (ub : Nat) : ∀ los : List Nat, mapTvF ub los = los.map (mkTvF ub) := by
  intro los
  induction los with
  | nil => rfl
  | cons lo los ih => exact congrArg (List.cons (mkTvF ub lo)) ih

theorem endsF_eq (Lnum Lden : Nat) :
    ∀ cells : List (Nat × Nat), endsF Lnum Lden cells = cells.map fun c => (loW Lnum Lden c.1, hiW Lnum Lden c.2) := by
  intro cells
  induction cells with
  | nil => rfl
  | cons c cs ih => exact congrArg (List.cons (loW Lnum Lden c.1, hiW Lnum Lden c.2)) ih

theorem mapHiF_eq : ∀ ps : List (Nat × Nat), mapHiF ps = ps.map fun p => mkTvHF p.1 p.2 := by
  intro ps
  induction ps with
  | nil => rfl
  | cons p ps ih => exact congrArg (List.cons (mkTvHF p.1 p.2)) ih

theorem mapLoF_eq (u : Nat) : ∀ ps : List (Nat × Nat), mapLoF u ps = ps.map fun p => mkTvF u p.1 := by
  intro ps
  induction ps with
  | nil => rfl
  | cons p ps ih => exact congrArg (List.cons (mkTvF u p.1)) ih

theorem fstSumF_eq : ∀ ps : List (Nat × Nat), fstSumF ps = sumN (ps.map fun p => p.1) := by
  intro ps
  induction ps with
  | nil => rfl
  | cons p ps ih => exact congrArg (Nat.add p.1) ih

theorem sndSumF_eq : ∀ ps : List (Nat × Nat), sndSumF ps = sumN (ps.map fun p => p.2) := by
  intro ps
  induction ps with
  | nil => rfl
  | cons p ps ih => exact congrArg (Nat.add p.2) ih

/-! ### The tests -/

theorem chkIF_eq : chkIF = chkI := by
  funext ts ltm dS iax a b ch cl
  simp only [chkIF, chkI, addTermsF_eq, andF_eq]

theorem chkI2F_eq : chkI2F = chkI2 := by
  funext vs ltm dS iax a b ch cl
  simp only [chkI2F, chkI2, addTerms2F_eq, andF_eq]

theorem intv3F_eq : intv3F = intv3 := by
  funext vs c1 yuP yuN ydP ydN ltm a pa r
  simp only [intv3F, intv3, chkI2F_eq, clampLF_eq, maxNF_eq, minNF_eq, pieceCF_eq, pieceC_eq_pieceOf, rec_cond,
    cond_and, andF_eq]

theorem runI3F_eq : runI3F = runI3 := by
  funext vs w c1 yuP yuN ydP ydN ltm
  simp only [runI3F, runI3, intv3F_eq, pieceCF_eq, pieceC_eq_pieceOf, andF_eq]

theorem resTM3F_eq : resTM3F = resTM3 := by
  funext vs mlo ltm k h
  simp only [resTM3F, resTM3, hpSum2F_eq, lenVF_eq, runI3F_eq, minNF_eq, andF_eq]

theorem resYF_eq : resYF = resY := by
  funext Lnum Lden cells kH hH kL hL
  simp only [resYF, resY, okYF_eq, endsF_eq, fstSumF_eq, sndSumF_eq, mapHiF_eq, mapLoF_eq, mkTvHF_eq, mkTvF_eq,
    resTM3F_eq, rec_cond, cond_and, andF_eq]

/-- **The test at the two corners in the kernel's fastest form is `resYH`.** -/
theorem resYHF_eq (Lnum Lden : Nat) (cells : List (Nat × Nat)) (s : Nat) :
    resYHF Lnum Lden cells s = resYH Lnum Lden cells s := by
  simp only [resYHF, resYH, resYF_eq]

theorem intvHF_eq : intvHF = intvH := by
  funext ts c1 yuP yuN ydP ydN ltm a pa r
  simp only [intvHF, intvH, chkIF_eq, clampLF_eq, maxNF_eq, minNF_eq, pieceCF_eq, rec_cond, cond_and, andF_eq]

theorem runIHF_eq : runIHF = runIH := by
  funext ts w c1 yuP yuN ydP ydN ltm
  simp only [runIHF, runIH, intvHF_eq, pieceCF_eq, andF_eq]

theorem resTMHF_eq : resTMHF = resTMH := by
  funext ts mlo ltm k h
  simp only [resTMHF, resTMH, hpSumF_eq, lenTF_eq, runIHF_eq, minNF_eq, andF_eq]

theorem resTHF_eq : resTHF = resTH := by
  funext Lnum Lden cs hs k h
  simp only [resTHF, resTH, mapTmF_eq, mkTmF_eq, resTMHF_eq, andF_eq]

theorem intv2HF_eq : intv2HF = intv2H := by
  funext vs c1 yuP yuN ydP ydN ltm a pa r
  simp only [intv2HF, intv2H, chkI2F_eq, clampLF_eq, maxNF_eq, minNF_eq, pieceCF_eq, rec_cond, cond_and, andF_eq]

theorem runI2HF_eq : runI2HF = runI2H := by
  funext vs w c1 yuP yuN ydP ydN ltm
  simp only [runI2HF, runI2H, intv2HF_eq, pieceCF_eq, andF_eq]

theorem resTM2HF_eq : resTM2HF = resTM2H := by
  funext vs mlo ltm k h
  simp only [resTM2HF, resTM2H, hpSum2F_eq, lenVF_length, runI2HF_eq, minNF_eq, andF_eq]

theorem resT2HF_eq : resT2HF = resT2H := by
  funext Lnum Lden cs hs k h
  simp only [resT2HF, resT2H, mapLoOfF_eq, sumNF_eq, mapTvF_eq, mkTvF_eq, resTM2HF_eq, andF_eq]

/-- **The test with the lines named by the hint in the kernel's fastest form is `resXH`.** -/
theorem resXHF_eq (Lnum Lden : Nat) (cs : List Nat) (hs k h : Nat) :
    resXHF Lnum Lden cs hs k h = resXH Lnum Lden cs hs k h := by
  simp only [resXHF, resXH, resT2HF_eq, resTHF_eq, rec_cond]

end SieveResTest
