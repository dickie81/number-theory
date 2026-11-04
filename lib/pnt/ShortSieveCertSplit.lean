import ShortSieveCertCheck

/-!
# A certificate checked in parts

`run` on a node from `run` on its children. Each lemma takes the node's own condition (checked by `decide +kernel`
on its state) and its children's results, so a cell's certificate can be checked in pieces: its top by these lemmas,
and each subtree below a cut point by `decide +kernel` on its own, an auxiliary lemma with its own kernel caches. The
kernel's memory grows with the reductions of one check, so a whole cell cannot be one check (`ShortSieveCertData`
writes the cells this way).
-/

namespace ShortSieveCert

variable {E : ℤ} {S : Shp} {Γ : List Con} {B : Box} {b : Bool} {L : ℕ}

/-- `run` on a moved end (`Cert.up`) from its condition and `run` on the child, the box with the end moved. -/
theorem run_up_of {j : ℕ} {lower : Bool} {i : ℕ} {v : ℤ} {t : Cert}
    (h : i < Γ.length ∧ upOK (Γ.getD i ⟨LF.zero, false⟩) E B j lower v = true)
    (ht : run E t S Γ (cutAt B j lower v) b = some L) : run E (.up j lower i v t) S Γ B b = some L := by
  rw [run, ite_eq_left h, ht]

/-- `run` on a combined constraint (`Cert.comb`) from `run` on the child, with the constraint added. -/
theorem run_comb_of {i j c : ℕ} {t : Cert} (h : i < Γ.length ∧ j < Γ.length)
    (ht : run E t S (combCon (Γ.getD i ⟨LF.zero, false⟩) (Γ.getD j ⟨LF.zero, false⟩) c :: Γ) B b = some L) :
    run E (.comb i j c t) S Γ B b = some L := by
  rw [run, ite_eq_left h, ht]

/-- `run` on a split by a constraint from its condition and `run` on the two children: the losses add. -/
theorem run_split_of {C : Con} {u w : ℕ} {t₁ t₂ : Cert} {L₁ L₂ : ℕ}
    (h : fits [C] S.n = true ∧ u < S.k + S.m ∧ w < S.k + S.m ∧ wtN S C.L u ≠ wtN S C.L w)
    (h₁ : run E t₁ S (C :: Γ) B b = some L₁) (h₂ : run E t₂ S (C.neg :: Γ) B b = some L₂) (hL : L₁ + L₂ = L) :
    run E (.split C u w t₁ t₂) S Γ B b = some L := by
  rw [run, ite_eq_left h, h₁, h₂, ← hL]
  rfl

/-- `run` on a box cut from its condition and `run` on the two halves: the losses add. -/
theorem run_cut_of {j : ℕ} {p : ℤ} {u w : ℕ} {t₁ t₂ : Cert} {L₁ L₂ : ℕ}
    (h : u < S.k + S.m ∧ w < S.k + S.m ∧ wtN S (ltCon j p).L u ≠ wtN S (ltCon j p).L w)
    (h₁ : run E t₁ S Γ (B.modify j fun b' => (b'.1, min b'.2 p)) b = some L₁)
    (h₂ : run E t₂ S Γ (B.modify j fun b' => (max b'.1 p, b'.2)) b = some L₂) (hL : L₁ + L₂ = L) :
    run E (.cut j p u w t₁ t₂) S Γ B b = some L := by
  rw [run, ite_eq_left h, h₁, h₂, ← hL]
  rfl

/-- `run` on Buchstab's step of a standard node from its Type I test and `run` on the child. -/
theorem run_dec_std_of {k : ℕ} {acts labels : List ℕ} {kind : ℕ} {t : Cert}
    (h : actsOK Γ acts B.length = true ∧
      typeICheck (stdItems (k + 1)) (k + 1) E B (actsOf Γ acts) labels kind = true)
    (ht : run E t (.std (k + 1)) (geCon (k + 1) :: (Γ ++ [ordCon k])) (B ++ [(NU0, (B.getD k (0, 0)).2)]) (!b) =
      some L) :
    run E (.dec acts labels kind t) (.std k) Γ B b = some L := by
  rw [run, ite_eq_left h, ht]

/-- `run` on Buchstab's step on the last of two rough items from its Type I test and `run` on the child. -/
theorem run_dec_two_of {acts labels : List ℕ} {kind : ℕ} {t : Cert} (hS : ∀ k, S ≠ .std k)
    (h : S.m = 2 ∧ actsOK Γ acts B.length = true ∧
      typeICheck S.items (S.k + 1) E B (actsOf Γ acts) labels kind = true)
    (ht : run E t (.last S) (geL (S.items.getD (S.k + 1) LF.zero) B.length ::
          (Γ ++ [ordL (S.items.getD (S.sN 1) LF.zero) B.length]))
        (B ++ [(NU0, (S.items.getD (S.sN 1) LF.zero).maxB B E)]) (!b) = some L) :
    run E (.dec acts labels kind t) S Γ B b = some L := by
  cases S with
  | std k => exact absurd rfl (hS k)
  | rev k => simp only [run]; rw [ite_eq_left h]; exact ht
  | last S' => simp only [run]; rw [ite_eq_left h]; exact ht
  | swap S' => simp only [run]; rw [ite_eq_left h]; exact ht

/-- `run` on a role reversal of a standard node from its Type I test and `run` on the reversed child. -/
theorem run_rev_std_of {k : ℕ} {acts labels : List ℕ} {kind : ℕ} {t : Cert}
    (h : actsOK Γ acts B.length = true ∧ typeICheck (stdItems (k + 2)) 0 E B (actsOf Γ acts) labels kind = true)
    (ht : run E t (.rev k) (Γ ++ [halfCon k]) (B ++ [(NU0, (B.getD 0 (0, 0)).2)]) (!b) = some L) :
    run E (.rev acts labels kind t) (.std (k + 1)) Γ B b = some L := by
  rw [run, ite_eq_left h, ht]

/-- `run` on the swap of the two rough items from `run` on the swapped node. -/
theorem run_swap_of {t : Cert} (h : S.m = 2) (ht : run E t (.swap S) Γ B b = some L) :
    run E (.swap t) S Γ B b = some L := by
  rw [run, ite_eq_left h, ht]

end ShortSieveCert
