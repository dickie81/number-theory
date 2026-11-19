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

-- 1. Sorts and functions exist with no declaration at all.
noncomputable def id' {α : Sort u} (a : α) : α := a
noncomputable def comp' {α : Sort u} {β : Sort v} {γ : Sort u} (g : β → γ) (f : α → β) : α → γ := fun a => g (f a)

-- 2. An inductive type with no constructors, and one with one.
inductive Nothing : Prop
inductive Something : Prop where
  | intro : Something

-- 3. Equality, as an inductive family.
inductive Same {α : Sort u} (a : α) : α → Prop where
  | refl : Same a a

-- its recursor is the whole theory of equality
theorem Same.symm {α : Sort u} {a b : α} (h : Same a b) : Same b a :=
  @Same.rec α a (fun x _ => Same x a) Same.refl b h

theorem Same.trans {α : Sort u} {a b c : α} (h₁ : Same a b) (h₂ : Same b c) : Same a c :=
  @Same.rec α b (fun x _ => Same a x) h₁ c h₂

theorem Same.congr {α : Sort u} {β : Sort v} (f : α → β) {a b : α} (h : Same a b) : Same (f a) (f b) :=
  @Same.rec α a (fun x _ => Same (f a) (f x)) Same.refl b h

-- 4. Numbers.
inductive N : Type where
  | z : N
  | s : N → N

noncomputable def N.add (a : N) : N → N :=
  @N.rec (fun _ => N) a (fun _ r => N.s r)

theorem N.zero_add (b : N) : Same (N.add N.z b) b :=
  @N.rec (fun b => Same (N.add N.z b) b) Same.refl (fun _ ih => Same.congr N.s ih) b

theorem N.succ_add (a b : N) : Same (N.add (N.s a) b) (N.s (N.add a b)) :=
  @N.rec (fun b => Same (N.add (N.s a) b) (N.s (N.add a b))) Same.refl (fun _ ih => Same.congr N.s ih) b

theorem N.add_comm (a b : N) : Same (N.add a b) (N.add b a) :=
  @N.rec (fun b => Same (N.add a b) (N.add b a))
    (Same.symm (N.zero_add a))
    (fun b ih => Same.trans (Same.congr N.s ih) (Same.symm (N.succ_add b a))) b

-- 5. Does the kernel compute?  2 + 2 = 4 by reduction alone.
theorem two_add_two : Same (N.add (N.s (N.s N.z)) (N.s (N.s N.z))) (N.s (N.s (N.s (N.s N.z)))) := Same.refl

#print axioms N.add_comm
#print axioms two_add_two
