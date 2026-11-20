import AxiomTools

/-!
# What one proposition generates

With excluded middle, a proposition `p` generates four propositions up to equivalence: `False`, `p`, `¬p`, `True`.
Without it, it generates infinitely many. This file proves both halves, with no axiom.

The formulas in one variable form a ladder (Rieger, Nishimura):

    A 0 = p            B 0 = ¬p
    A (k+1) = A k ∨ B k            B (k+1) = A (k+1) → A k

so `A 1` is `p ∨ ¬p`, `B 1` is equivalent to `¬¬p`, `A 2` to `¬p ∨ ¬¬p` and `B 2` to `¬¬p → p`.

* `Derivable` is derivability in intuitionistic propositional logic (a Hilbert system). What is derivable holds
  for every proposition of Lean (`sound_eval`).
* `Forces` is truth in one Kripke model: the worlds are the natural numbers, world `w` sees itself and every `v`
  with `v + 2 ≤ w`, and `p` holds at world `0` only. What is derivable holds at every world (`sound`).
* In that model `A k` holds exactly at the worlds `≤ k`, and `B k` at the worlds `< k` and at `k + 1` (`truth`).
  So no formula of the ladder is derivable (`not_derivable_A`, `not_derivable_B`), and no two are equivalent
  (`A_A`, `B_B`, `A_B`).
* With excluded middle as a hypothesis the ladder collapses: `A k` holds for `k ≥ 1` and `B k` for `k ≥ 2`
  (`collapse_A`, `collapse_B`), and `B 1` is equivalent to `p` (`B_one`).
-/

namespace Ladder

/-- Formulas in one variable. -/
inductive Form where
  | var : Form
  | bot : Form
  | conj : Form → Form → Form
  | disj : Form → Form → Form
  | imp : Form → Form → Form

open Form

/-- The formula read as a proposition of Lean, with `p` for the variable. -/
def eval (p : Prop) : Form → Prop
  | var => p
  | bot => False
  | conj a b => eval p a ∧ eval p b
  | disj a b => eval p a ∨ eval p b
  | imp a b => eval p a → eval p b

/-- The two sides of the ladder. -/
def pair : Nat → Form × Form
  | 0 => (var, imp var bot)
  | k + 1 => (disj (pair k).1 (pair k).2, imp (disj (pair k).1 (pair k).2) (pair k).1)

def A (k : Nat) : Form := (pair k).1
def B (k : Nat) : Form := (pair k).2

theorem A_succ (k : Nat) : A (k + 1) = disj (A k) (B k) := rfl
theorem B_succ (k : Nat) : B (k + 1) = imp (A (k + 1)) (A k) := rfl

/-! ## Intuitionistic propositional logic -/

inductive Derivable : Form → Prop
  | k (a b : Form) : Derivable (imp a (imp b a))
  | s (a b c : Form) : Derivable (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  | andI (a b : Form) : Derivable (imp a (imp b (conj a b)))
  | andL (a b : Form) : Derivable (imp (conj a b) a)
  | andR (a b : Form) : Derivable (imp (conj a b) b)
  | orL (a b : Form) : Derivable (imp a (disj a b))
  | orR (a b : Form) : Derivable (imp b (disj a b))
  | orE (a b c : Form) : Derivable (imp (imp a c) (imp (imp b c) (imp (disj a b) c)))
  | exFalso (a : Form) : Derivable (imp bot a)
  | mp {a b : Form} : Derivable (imp a b) → Derivable a → Derivable b

/-- What intuitionistic logic derives holds for every proposition, with no axiom. -/
theorem sound_eval {φ : Form} (h : Derivable φ) (p : Prop) : eval p φ := by
  induction h with
  | k a b => exact fun ha _ => ha
  | s a b c => exact fun h1 h2 ha => h1 ha (h2 ha)
  | andI a b => exact fun ha hb => ⟨ha, hb⟩
  | andL a b => exact fun h => h.1
  | andR a b => exact fun h => h.2
  | orL a b => exact fun ha => Or.inl ha
  | orR a b => exact fun hb => Or.inr hb
  | orE a b c => exact fun h1 h2 h => h.elim h1 h2
  | exFalso a => exact fun h => h.elim
  | mp _ _ ih1 ih2 => exact ih1 ih2

/-! ## The model -/

/-- World `w` sees itself and the worlds at least two below. -/
def Sees (w v : Nat) : Prop := v = w ∨ v + 2 ≤ w

theorem Sees.refl (w : Nat) : Sees w w := Or.inl rfl

theorem Sees.le {w v : Nat} (h : Sees w v) : v ≤ w :=
  h.elim (fun e => Nat.le_of_eq e) (fun h2 => Nat.le_trans (Nat.le_add_right v 2) h2)

theorem Sees.trans {w v u : Nat} (h1 : Sees w v) (h2 : Sees v u) : Sees w u :=
  h1.elim (fun e => e ▸ h2)
    (fun hv => h2.elim (fun e => Or.inr (e.symm ▸ hv))
      (fun hu => Or.inr (Nat.le_trans hu (Nat.le_trans (Nat.le_add_right v 2) hv))))

/-- Truth at a world. The variable holds at world `0` only. -/
def Forces : Form → Nat → Prop
  | var, w => w = 0
  | bot, _ => False
  | conj a b, w => Forces a w ∧ Forces b w
  | disj a b, w => Forces a w ∨ Forces b w
  | imp a b, w => ∀ v, Sees w v → Forces a v → Forces b v

/-- What holds at a world holds at the worlds it sees. -/
theorem persist : ∀ (φ : Form) {w v : Nat}, Sees w v → Forces φ w → Forces φ v
  | var, w, v, hs, h => by
    have h0 : w = 0 := h
    show v = 0
    exact Nat.eq_zero_of_le_zero (h0 ▸ hs.le)
  | bot, _, _, _, h => h
  | conj a b, _, _, hs, h => ⟨persist a hs h.1, persist b hs h.2⟩
  | disj a b, _, _, hs, h => h.elim (fun ha => Or.inl (persist a hs ha)) (fun hb => Or.inr (persist b hs hb))
  | imp _ _, _, _, hs, h => fun u hu => h u (hs.trans hu)

/-- What intuitionistic logic derives holds at every world. -/
theorem sound {φ : Form} (h : Derivable φ) : ∀ w, Forces φ w := by
  induction h with
  | k a b => exact fun _ _ _ ha _ hvu _ => persist a hvu ha
  | s a b c => exact fun _ _ _ h1 _ hvu h2 t hut ha => h1 t (hvu.trans hut) ha t (Sees.refl t) (h2 t hut ha)
  | andI a b => exact fun _ _ _ ha _ hvu hb => ⟨persist a hvu ha, hb⟩
  | andL a b => exact fun _ _ _ h => h.1
  | andR a b => exact fun _ _ _ h => h.2
  | orL a b => exact fun _ _ _ ha => Or.inl ha
  | orR a b => exact fun _ _ _ hb => Or.inr hb
  | orE a b c =>
    exact fun _ _ _ h1 _ hvu h2 t hut h => h.elim (fun ha => h1 t (hvu.trans hut) ha) (fun hb => h2 t hut hb)
  | exFalso a => exact fun _ _ _ h => h.elim
  | mp _ _ ih1 ih2 => exact fun w => ih1 w w (Sees.refl w) (ih2 w)

theorem imp_sound {φ ψ : Form} (h : Derivable (imp φ ψ)) (w : Nat) : Forces φ w → Forces ψ w :=
  sound h w w (Sees.refl w)

/-! ## Where each formula of the ladder holds -/

theorem truth : ∀ k, (∀ w, Forces (A k) w ↔ w ≤ k) ∧ (∀ w, Forces (B k) w ↔ w < k ∨ w = k + 1)
  | 0 => by
    refine ⟨fun w => Nat.le_zero.symm, fun w => ?_⟩
    show (∀ v, Sees w v → v = 0 → False) ↔ w < 0 ∨ w = 0 + 1
    constructor
    · intro h
      cases w with
      | zero => exact (h 0 (Sees.refl 0) rfl).elim
      | succ w =>
        cases w with
        | zero => exact Or.inr rfl
        | succ w => exact (h 0 (Or.inr (Nat.le_add_left 2 w)) rfl).elim
    · intro h v hs hv
      cases h with
      | inl h0 => exact absurd h0 (Nat.not_lt_zero w)
      | inr h1 =>
        rw [h1, hv] at hs
        cases hs with
        | inl e => exact Nat.noConfusion e
        | inr hle => exact absurd hle (by decide)
  | k + 1 => by
    have ih := truth k
    have hA' : ∀ w, Forces (A (k + 1)) w ↔ w ≤ k + 1 := by
      intro w
      show Forces (A k) w ∨ Forces (B k) w ↔ w ≤ k + 1
      constructor
      · intro h
        cases h with
        | inl ha => exact Nat.le_succ_of_le ((ih.1 w).mp ha)
        | inr hb =>
          cases (ih.2 w).mp hb with
          | inl hlt => exact Nat.le_succ_of_le (Nat.le_of_lt hlt)
          | inr heq => exact Nat.le_of_eq heq
      · intro h
        cases Nat.le_or_eq_of_le_succ h with
        | inl hle => exact Or.inl ((ih.1 w).mpr hle)
        | inr heq => exact Or.inr ((ih.2 w).mpr (Or.inr heq))
    refine ⟨hA', fun w => ?_⟩
    show (∀ v, Sees w v → Forces (A (k + 1)) v → Forces (A k) v) ↔ w < k + 1 ∨ w = k + 1 + 1
    constructor
    · intro h
      cases Nat.lt_trichotomy w (k + 1) with
      | inl hlt => exact Or.inl hlt
      | inr h2 =>
        cases h2 with
        | inl heq =>
          -- w = k + 1 sees itself, where A (k + 1) holds and A k does not
          have hle : w ≤ k := (ih.1 w).mp (h w (Sees.refl w) ((hA' w).mpr (Nat.le_of_eq heq)))
          rw [heq] at hle
          exact absurd hle (Nat.not_succ_le_self k)
        | inr hgt =>
          cases Nat.eq_or_lt_of_le hgt with
          | inl heq => exact Or.inr heq.symm
          | inr hlt =>
            -- w ≥ k + 3 sees k + 1, where A (k + 1) holds and A k does not
            have hle : k + 1 ≤ k := (ih.1 (k + 1)).mp (h (k + 1) (Or.inr hlt) ((hA' (k + 1)).mpr (Nat.le_refl _)))
            exact absurd hle (Nat.not_succ_le_self k)
    · intro h v hs hv
      apply (ih.1 v).mpr
      cases h with
      | inl hlt => exact Nat.le_trans hs.le (Nat.le_of_lt_succ hlt)
      | inr heq =>
        cases hs with
        | inl e =>
          -- v = w = k + 2, where A (k + 1) does not hold
          have hle : v ≤ k + 1 := (hA' v).mp hv
          rw [e, heq] at hle
          exact absurd hle (Nat.not_succ_le_self (k + 1))
        | inr hle =>
          rw [heq] at hle
          exact Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hle)

theorem A_fails (k : Nat) : ¬ Forces (A k) (k + 1) :=
  fun h => Nat.not_succ_le_self k (((truth k).1 (k + 1)).mp h)

theorem B_fails (k : Nat) : ¬ Forces (B k) k :=
  fun h => (((truth k).2 k).mp h).elim (Nat.lt_irrefl k) (fun e => Nat.succ_ne_self k e.symm)

/-! ## No formula of the ladder is derivable, and no two are equivalent -/

theorem not_derivable_A (k : Nat) : ¬ Derivable (A k) := fun h => A_fails k (sound h (k + 1))

theorem not_derivable_B (k : Nat) : ¬ Derivable (B k) := fun h => B_fails k (sound h k)

/-- Excluded middle, `p ∨ ¬p`, is not derivable. -/
theorem not_derivable_em : ¬ Derivable (disj var (imp var bot)) := not_derivable_A 1

theorem A_A {j k : Nat} (h : j < k) : ¬ Derivable (imp (A k) (A j)) := fun hd =>
  Nat.lt_irrefl j (Nat.lt_of_lt_of_le h (((truth j).1 k).mp (imp_sound hd k (((truth k).1 k).mpr (Nat.le_refl k)))))

theorem B_B {j k : Nat} (h : j < k) : ¬ Derivable (imp (B k) (B j)) := fun hd =>
  (((truth j).2 (k + 1)).mp (imp_sound hd (k + 1) (((truth k).2 (k + 1)).mpr (Or.inr rfl)))).elim
    (fun hlt => Nat.lt_irrefl j (Nat.lt_trans (Nat.lt_trans h (Nat.lt_succ_self k)) hlt))
    (fun heq => Nat.lt_irrefl j (Nat.succ.inj heq ▸ h))

theorem A_B (j k : Nat) : ¬ (Derivable (imp (A j) (B k)) ∧ Derivable (imp (B k) (A j))) := fun ⟨h1, h2⟩ =>
  match Nat.lt_or_ge k j with
  | .inl hkj =>
    -- world k: A j holds there, B k does not
    B_fails k (imp_sound h1 k (((truth j).1 k).mpr (Nat.le_of_lt hkj)))
  | .inr hjk =>
    -- world k + 1: B k holds there, A j does not
    have hle : k + 1 ≤ j := ((truth j).1 (k + 1)).mp (imp_sound h2 (k + 1) (((truth k).2 (k + 1)).mpr (Or.inr rfl)))
    Nat.not_succ_le_self k (Nat.le_trans hle hjk)

/-! ## With excluded middle the ladder collapses -/

theorem collapse_A (em : ∀ p : Prop, p ∨ ¬p) (p : Prop) : ∀ k, eval p (A (k + 1))
  | 0 => (em p).elim Or.inl Or.inr
  | k + 1 => Or.inl (collapse_A em p k)

theorem collapse_B (em : ∀ p : Prop, p ∨ ¬p) (p : Prop) (k : Nat) : eval p (B (k + 2)) :=
  fun _ => collapse_A em p k

theorem B_one (em : ∀ p : Prop, p ∨ ¬p) (p : Prop) : eval p (B 1) ↔ p :=
  ⟨fun h => h ((em p).elim Or.inl Or.inr), fun hp _ => hp⟩

/-! ## The first rungs are the classical principles -/

theorem A_one : (∀ p, eval p (A 1)) ↔ ∀ p : Prop, p ∨ ¬p := Iff.rfl

theorem A_two : (∀ p, eval p (A 2)) ↔ ∀ p : Prop, ¬p ∨ ¬¬p :=
  ⟨fun h p => (h p).elim
      (fun h1 => h1.elim (fun hp => Or.inr (fun hn => hn hp)) Or.inl)
      (fun h2 => Or.inr (fun hn => hn (h2 (Or.inr hn)))),
   fun h p => (h p).elim (fun hn => Or.inl (Or.inr hn))
      (fun hnn => Or.inr (fun h' => h'.elim id (fun hn => absurd hn hnn)))⟩

theorem B_two : (∀ p, eval p (B 2)) ↔ ∀ p : Prop, ¬¬p → p :=
  ⟨fun h p hnn =>
      (h p (Or.inr (fun h' => h'.elim id (fun hn => absurd hn hnn)))).elim id (fun hn => absurd hn hnn),
   fun dne p _ => dne (p ∨ ¬p) (fun h => h (Or.inr (fun hp => h (Or.inl hp))))⟩

end Ladder

#axioms_table Ladder
