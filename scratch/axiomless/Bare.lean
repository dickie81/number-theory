prelude

/-!
# The kernel alone

This file imports nothing (`prelude`): not even `Init`, where Lean declares `Eq`, `Nat` and its three axioms. What
is left is what the kernel provides without any declaration: sorts, functions, inductive types with their
recursors, and computation. From those alone the file builds equality, the natural numbers and the commutativity of
addition. Check it with `lean scratch/axiomless/Bare.lean`.

The definitions are `noncomputable` because the compiler, not the kernel, needs constants of `Init` (`lcAny`) and
does not compile recursors. There are no tactics here either: their syntax is declared in `Init`.
-/

universe u v

/-! 1. Sorts and functions exist with no declaration at all. -/
noncomputable def id' {α : Sort u} (a : α) : α := a
noncomputable def comp' {α : Sort u} {β : Sort v} {γ : Sort u} (g : β → γ) (f : α → β) : α → γ := fun a => g (f a)

/-! 2. An inductive type with no constructor, and one with one. -/
inductive Nothing : Prop
inductive Something : Prop where
  | intro : Something

/-! 3. Equality, as an inductive family. Its recursor is the whole theory of equality. -/
inductive Eq {α : Sort u} : α → α → Prop where
  | refl (a : α) : Eq a a

theorem Eq.symm {α : Sort u} {a b : α} (h : Eq a b) : Eq b a :=
  @Eq.rec α a (fun x _ => Eq x a) (Eq.refl a) b h

theorem Eq.trans {α : Sort u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  @Eq.rec α b (fun x _ => Eq a x) h₁ c h₂

theorem Eq.congr {α : Sort u} {β : Sort v} (f : α → β) {a b : α} (h : Eq a b) : Eq (f a) (f b) :=
  @Eq.rec α a (fun x _ => Eq (f a) (f x)) (Eq.refl (f a)) b h

/-! 4. Any two proofs of a proposition are equal, by a rule of the kernel. So two proofs of an equality are equal:
what other systems add as an axiom (uniqueness of identity proofs) holds here by `refl`. -/
theorem proof_irrel {p : Prop} (h₁ h₂ : p) : Eq h₁ h₂ := Eq.refl h₁

theorem uip {α : Sort u} {a b : α} (h₁ h₂ : Eq a b) : Eq h₁ h₂ := Eq.refl h₁

/-! 5. Quotients. Once an equality exists, the kernel adds `Quot`, `Quot.mk`, `Quot.lift` and `Quot.ind` on
request. They are not axioms, and `Quot.lift` computes on `Quot.mk`. Only `Quot.sound`, which `Init` declares, is
an axiom. -/
init_quot

theorem Quot.lift_mk {α : Sort u} {β : Sort v} (r : α → α → Prop) (f : α → β)
    (h : ∀ a b, r a b → Eq (f a) (f b)) (a : α) : Eq (Quot.lift f h (Quot.mk r a)) (f a) :=
  Eq.refl (f a)

/-! 6. Numbers. -/
inductive N : Type where
  | z : N
  | s : N → N

noncomputable def N.add (a : N) : N → N :=
  @N.rec (fun _ => N) a (fun _ r => N.s r)

theorem N.zero_add (b : N) : Eq (N.add N.z b) b :=
  @N.rec (fun b => Eq (N.add N.z b) b) (Eq.refl N.z) (fun _ ih => Eq.congr N.s ih) b

theorem N.succ_add (a b : N) : Eq (N.add (N.s a) b) (N.s (N.add a b)) :=
  @N.rec (fun b => Eq (N.add (N.s a) b) (N.s (N.add a b))) (Eq.refl (N.s a)) (fun _ ih => Eq.congr N.s ih) b

theorem N.add_comm (a b : N) : Eq (N.add a b) (N.add b a) :=
  @N.rec (fun b => Eq (N.add a b) (N.add b a))
    (Eq.symm (N.zero_add a))
    (fun b ih => Eq.trans (Eq.congr N.s ih) (Eq.symm (N.succ_add b a))) b

/-! 7. The kernel computes: `2 + 2 = 4` by reduction alone. -/
theorem two_add_two : Eq (N.add (N.s (N.s N.z)) (N.s (N.s N.z))) (N.s (N.s (N.s (N.s N.z)))) :=
  Eq.refl (N.s (N.s (N.s (N.s N.z))))

#print axioms N.add_comm
#print axioms two_add_two
#print axioms uip
#print axioms Quot.lift_mk
