import AxiomTools

/-!
# The axioms as hypotheses

With no axiom, excluded middle, propositional extensionality, function extensionality and choice are not theorems.
They are still propositions, and the implications between them are theorems, free of axioms. This file proves
the ones below; the last command checks that none depends on an axiom.

    EM ⟺ DNE ⟺ Peirce              EM ⟹ Linear ⟹ WEM ⟺ DeMorgan
    TwoValued ⟺ EM ∧ PropExt        EM ⟹ LPO ⟺ WLPO ∧ MP
    a choice function on the predicates of Bool, with PropExt and FunExt for them, gives EM (Diaconescu)
    Quot.sound at a function type gives function extensionality at that type
-/

namespace Principles

universe u v

/-- Excluded middle. -/
def EM : Prop := ∀ p : Prop, p ∨ ¬p
/-- Double negation elimination. -/
def DNE : Prop := ∀ p : Prop, ¬¬p → p
/-- Peirce's law. -/
def Peirce : Prop := ∀ p q : Prop, ((p → q) → p) → p
/-- Weak excluded middle. -/
def WEM : Prop := ∀ p : Prop, ¬p ∨ ¬¬p
/-- The De Morgan law that fails without excluded middle. -/
def DeMorgan : Prop := ∀ p q : Prop, ¬(p ∧ q) → ¬p ∨ ¬q
/-- Any two propositions are comparable (Gödel and Dummett's axiom). -/
def Linear : Prop := ∀ p q : Prop, (p → q) ∨ (q → p)
/-- Equivalent propositions are equal. -/
def PropExt : Prop := ∀ p q : Prop, (p ↔ q) → p = q
/-- There are two propositions. -/
def TwoValued : Prop := ∀ p : Prop, p = True ∨ p = False
/-- The limited principle of omniscience: a sequence of bits has a `true` or has none. -/
def LPO : Prop := ∀ f : Nat → Bool, (∃ n, f n = true) ∨ ∀ n, f n = false
/-- The weak limited principle of omniscience. -/
def WLPO : Prop := ∀ f : Nat → Bool, (∀ n, f n = false) ∨ ¬ ∀ n, f n = false
/-- Markov's principle: a sequence of bits that is not all `false` has a `true`. -/
def MP : Prop := ∀ f : Nat → Bool, (¬ ∀ n, f n = false) → ∃ n, f n = true

/-! ## Classical logic -/

theorem em_iff_dne : EM ↔ DNE :=
  ⟨fun em p h => (em p).elim id (fun hn => absurd hn h),
   fun dne p => dne (p ∨ ¬p) (fun h => h (Or.inr (fun hp => h (Or.inl hp))))⟩

theorem em_iff_peirce : EM ↔ Peirce :=
  ⟨fun em p _ h => (em p).elim id (fun hn => h (fun hp => absurd hp hn)),
   fun peirce p => peirce (p ∨ ¬p) False (fun h => Or.inr (fun hp => h (Or.inl hp)))⟩

/-- Each instance of excluded middle is not false. The quantifier cannot be moved inside the double negation. -/
theorem not_not_em (p : Prop) : ¬¬(p ∨ ¬p) :=
  fun h => h (Or.inr (fun hp => h (Or.inl hp)))

/-- Excluded middle holds for a decidable proposition. -/
theorem em_of_decidable (p : Prop) [d : Decidable p] : p ∨ ¬p :=
  match d with
  | .isTrue h => Or.inl h
  | .isFalse h => Or.inr h

/-- Three negations are one. -/
theorem not_not_not {p : Prop} : ¬¬¬p ↔ ¬p :=
  ⟨fun h hp => h (fun hn => hn hp), fun hn h => h hn⟩

/-! ## Between intuitionistic and classical logic -/

theorem linear_of_em (em : EM) : Linear :=
  fun p _ => (em p).elim (fun hp => Or.inr (fun _ => hp)) (fun hn => Or.inl (fun hp => absurd hp hn))

theorem wem_of_linear (lin : Linear) : WEM :=
  fun p => (lin p (¬p)).elim (fun h => Or.inl (fun hp => h hp hp)) (fun h => Or.inr (fun hn => hn (h hn)))

theorem wem_iff_deMorgan : WEM ↔ DeMorgan :=
  ⟨fun wem p _ h => (wem p).elim Or.inl (fun hnn => Or.inr (fun hq => hnn (fun hp => h ⟨hp, hq⟩))),
   fun dm p => dm p (¬p) (fun h => h.2 h.1)⟩

/-! ## The propositions as a type -/

theorem true_ne_false : True ≠ False :=
  fun h => Eq.mp h trivial

theorem twoValued_iff : TwoValued ↔ EM ∧ PropExt :=
  ⟨fun tv =>
    ⟨fun p => (tv p).elim (fun h => Or.inl (Eq.mpr h trivial)) (fun h => Or.inr (fun hp => Eq.mp h hp)),
     fun p q hpq =>
      (tv p).elim
        (fun hp => (tv q).elim (fun hq => hp.trans hq.symm)
          (fun hq => (Eq.mp hq (hpq.mp (Eq.mpr hp trivial))).elim))
        (fun hp => (tv q).elim (fun hq => (Eq.mp hp (hpq.mpr (Eq.mpr hq trivial))).elim)
          (fun hq => hp.trans hq.symm))⟩,
   fun ⟨em, pe⟩ p =>
    (em p).elim (fun hp => Or.inl (pe p True ⟨fun _ => trivial, fun _ => hp⟩))
      (fun hn => Or.inr (pe p False ⟨hn, False.elim⟩))⟩

/-- Cantor: no function from a type onto its predicates. Equality of predicates is only used to transport. -/
theorem cantor {α : Sort u} (f : α → α → Prop) : ∃ s : α → Prop, ∀ a, f a ≠ s :=
  ⟨fun a => ¬ f a a, fun a h =>
    have h' : f a a = ¬ f a a := congrFun h a
    have hn : ¬ f a a := fun hf => Eq.mp h' hf hf
    hn (Eq.mpr h' hn)⟩

/-! ## Sequences of bits -/

theorem lpo_of_em (em : EM) : LPO :=
  fun f => (em (∃ n, f n = true)).elim Or.inl
    (fun hne => Or.inr (fun n =>
      match h : f n with
      | false => rfl
      | true => absurd ⟨n, h⟩ hne))

theorem wlpo_of_lpo (lpo : LPO) : WLPO :=
  fun f => (lpo f).elim (fun ⟨n, hn⟩ => Or.inr (fun hall => Bool.noConfusion ((hall n).symm.trans hn))) Or.inl

theorem mp_of_lpo (lpo : LPO) : MP :=
  fun f hn => (lpo f).elim id (fun hall => absurd hall hn)

theorem lpo_iff : LPO ↔ WLPO ∧ MP :=
  ⟨fun lpo => ⟨wlpo_of_lpo lpo, mp_of_lpo lpo⟩,
   fun ⟨wlpo, mp⟩ f => (wlpo f).elim Or.inr (fun h => Or.inl (mp f h))⟩

/-! ## Diaconescu: choice and extensionality give excluded middle -/

/-- A function `ε` that picks, from each predicate on `Bool` that holds somewhere, a point where it holds; with
extensionality for those predicates, every proposition is decided. Take `U b := b = true ∨ p` and
`V b := b = false ∨ p`. If `p` holds then `U = V`, so `ε U = ε V`; so if `ε U = true` and `ε V = false`, `p` fails. -/
theorem em_of_choice (ε : (Bool → Prop) → Bool) (hε : ∀ P : Bool → Prop, (∃ b, P b) → P (ε P))
    (pe : PropExt) (fe : ∀ P Q : Bool → Prop, (∀ b, P b = Q b) → P = Q) : EM :=
  fun p =>
    let U : Bool → Prop := fun b => b = true ∨ p
    let V : Bool → Prop := fun b => b = false ∨ p
    have hU : U (ε U) := hε U ⟨true, Or.inl rfl⟩
    have hV : V (ε V) := hε V ⟨false, Or.inl rfl⟩
    hU.elim
      (fun hu => hV.elim
        (fun hv => Or.inr (fun hp =>
          have hUV : U = V := fe U V (fun _ => pe _ _ ⟨fun _ => Or.inr hp, fun _ => Or.inr hp⟩)
          have h : ε U = ε V := congrArg ε hUV
          Bool.noConfusion (hu.symm.trans (h.trans hv))))
        Or.inl)
      Or.inl

/-! ## Function extensionality from the soundness of quotients -/

/-- `Quot.sound` for the type of functions gives function extensionality for it. The step that makes it work is
a rule of the kernel, not an axiom: `Quot.lift f h (Quot.mk r a)` computes to `f a`. -/
theorem funext_of_sound {α : Sort u} {β : α → Sort v}
    (sound : ∀ (r : (∀ x, β x) → (∀ x, β x) → Prop) (f g : ∀ x, β x), r f g → Quot.mk r f = Quot.mk r g)
    (f g : ∀ x, β x) (h : ∀ x, f x = g x) : f = g :=
  let eqv : (∀ x, β x) → (∀ x, β x) → Prop := fun f g => ∀ x, f x = g x
  let app : Quot eqv → ∀ x, β x := fun q x => Quot.lift (fun f : ∀ x, β x => f x) (fun _ _ h => h x) q
  show app (Quot.mk eqv f) = app (Quot.mk eqv g) from congrArg app (sound eqv f g h)

end Principles

#axioms_table Principles
