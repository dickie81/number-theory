import ShortSieveCertCell
import ShortSieveCertChain2

/-!
# The certificate's checker

A certificate node arose from a root cell by Buchstab's steps, role reversals and swaps of its two rough items: its
shape (`Shp`). The checker computes from the shape what its checks need (the number of primes and of coordinates,
the items' forms, the sifting primes and the coordinates' rows), and `Desc` ties a shape to its typed node data.

* `Desc.data`: the shape's computed data are the typed data's.
* `Desc.itemsOK`, `Desc.fit`: the items' forms are `DEN` times their exponents and use only the node's coordinates.
-/

open Finset Real Filter

namespace ShortSieveCert

open ShortSieveNode ShortSieveTree

/-- The shape of a certificate node, as it arose from a root cell: a standard node with `k + 1` primes, the role
reversal of the standard node with `k + 2` primes, Buchstab's step on the last of two rough items, or the swap of the
two rough items. -/
inductive Shp
  | std (k : ℕ)
  | rev (k : ℕ)
  | last (S : Shp)
  | swap (S : Shp)

namespace Shp

/-- The number of primes. -/
def k : Shp → ℕ
  | std k => k + 1
  | rev k => k + 2
  | last S => S.k + 1
  | swap S => S.k

/-- The number of rough items. -/
def m : Shp → ℕ
  | std _ => 1
  | rev _ => 2
  | last S => S.m
  | swap S => S.m

/-- The number of coordinates. -/
def n : Shp → ℕ
  | std k => k + 1
  | rev k => k + 3
  | last S => S.n + 1
  | swap S => S.n

/-- The items' forms, in canonical order. -/
def items : Shp → List LF
  | std k => stdItems (k + 1)
  | rev k => revItems k
  | last S => lastItems S.items S.k 1 S.n
  | swap S => swapItems S.items S.k

/-- The sifting prime of the rough item `i`. -/
def sN : Shp → ℕ → ℕ
  | std k, _ => k
  | rev k, i => if i = 0 then k + 1 else 0
  | last S, i => if i = 1 then S.k else S.sN i
  | swap S, i => S.sN (1 - i)

/-- The coefficient, in the coordinate `j`, of the item at the canonical position `p`. -/
def AN : Shp → ℕ → ℕ → ℤ
  | std k, j, p => if p = j ∧ p < k + 1 then 1 else 0
  | rev k, j, p => if p = 0 then (if j = 0 ∨ j = k + 2 then 1 else 0)
      else if p ≤ k + 1 then (if p = j then 1 else 0) else if p = k + 3 ∧ j = 0 then 1 else 0
  | last S, j, p => if j = S.n then (if p = S.k then 1 else 0)
      else if p < S.k then S.AN j p else if p = S.k then S.AN j (S.k + 1) else S.AN j (p - 1)
  | swap S, j, p => if p = S.k then S.AN j (S.k + 1) else if p = S.k + 1 then S.AN j S.k else S.AN j p

/-- The chain of the rough item `i` of a node with two rough items: the primes from the item's first one, at the role
reversal, down to its sifting prime. -/
def chain : Shp → ℕ → List ℕ
  | std k, _ => List.range (k + 1)
  | rev k, i => if i = 0 then (List.range (k + 1)).map (· + 1) else [0]
  | last S, i => if i = 1 then S.chain 1 ++ [S.k] else S.chain i
  | swap S, i => S.chain (1 - i)

end Shp

/-- **The typed data of a shape**: its primes, rough items, sifting primes, rows, items' forms and coordinates. -/
inductive Desc : Shp → (k m : ℕ) → (Fin m → Fin k) → Rows k m → List LF → ℕ → Prop
  | std (k : ℕ) : Desc (.std k) (k + 1) 1 (fun _ => Fin.last k) (stdRows (k + 1)) (stdItems (k + 1)) (k + 1)
  | rev (k : ℕ) : Desc (.rev k) (k + 2) 2 (revS (k + 1)) (revRows (k + 1)) (revItems k) (k + 3)
  | last {S : Shp} {k : ℕ} {s : Fin 2 → Fin k} {A : Rows k 2} {items : List LF} {n : ℕ} :
      Desc S k 2 s A items n → Desc (.last S) (k + 1) 2
        (Function.update (fun i => (s i).castSucc) (Fin.last 1) (Fin.last k)) (buchRows A (Fin.last 1) n)
        (lastItems items k 1 n) (n + 1)
  | swap {S : Shp} {k : ℕ} {s : Fin 2 → Fin k} {A : Rows k 2} {items : List LF} {n : ℕ} :
      Desc S k 2 s A items n → Desc (.swap S) k 2 (fun i => s i.rev) (swapRows A) (swapItems items k) n

/-- **A shape's computed data are its typed data's.** -/
theorem Desc.data {S : Shp} {k m : ℕ} {s : Fin m → Fin k} {A : Rows k m} {items : List LF} {n : ℕ}
    (h : Desc S k m s A items n) :
    S.k = k ∧ S.m = m ∧ S.n = n ∧ S.items = items ∧ (∀ i : Fin m, S.sN i = s i) ∧
      ∀ j t, S.AN j (canon t) = A j t := by
  induction h with
  | std k =>
    refine ⟨rfl, rfl, rfl, rfl, fun i => rfl, fun j t => ?_⟩
    rcases t with a | i
    · have ha := a.isLt
      simp only [Shp.AN, canon, Sum.elim_inl, stdRows]
      split_ifs <;> omega
    · simp only [Shp.AN, canon, Sum.elim_inr, stdRows]
      split_ifs <;> omega
  | rev k =>
    refine ⟨rfl, rfl, rfl, rfl, fun i => ?_, fun j t => ?_⟩
    · have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      rcases hi with rfl | rfl
      · show (if (0 : ℕ) = 0 then k + 1 else 0) = (revS (k + 1) (Fin.castSucc 0)).val
        rw [revS, Fin.snoc_castSucc]
        simp
      · show (if (1 : ℕ) = 0 then k + 1 else 0) = (revS (k + 1) (Fin.last 1)).val
        rw [revS, Fin.snoc_last]
        simp
    rcases t with a | i
    · have ha := a.isLt
      simp only [Shp.AN, canon, Sum.elim_inl, revRows]
      split_ifs <;> omega
    · have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      rcases hi with rfl | rfl
      · simp only [Shp.AN, canon, Sum.elim_inr, revRows, Fin.val_zero, Fin.isValue]
        split_ifs <;> first | omega | simp_all
      · simp only [Shp.AN, canon, Sum.elim_inr, revRows, Fin.val_one, Fin.isValue]
        split_ifs <;> first | omega | simp_all
  | @last S k s A items n h ih =>
    obtain ⟨hk, hm, hn, hit, hs, hA⟩ := ih
    refine ⟨by simp [Shp.k, hk], by simp [Shp.m, hm], by simp [Shp.n, hn], by simp [Shp.items, hit, hk, hn],
      fun i => ?_, fun j t => ?_⟩
    · have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      rcases hi with rfl | rfl
      · have := hs 0
        simp only [Shp.sN, Fin.val_zero, zero_ne_one, ↓reduceIte] at this ⊢
        rw [Function.update_of_ne (by decide)]
        simpa using this
      · simp only [Shp.sN, Fin.val_one, ↓reduceIte, hk]
        rw [show (1 : Fin 2) = Fin.last 1 from rfl, Function.update_self]
        simp
    · rcases t with a | i
      · induction a using Fin.lastCases with
        | last =>
          simp only [Shp.AN, hn, hk, canon, Sum.elim_inl, Fin.val_last, buchRows, Fin.lastCases_last,
            Fin.ext_iff]
          split_ifs <;> first | omega | exact hA j (Sum.inr 1)
        | cast a =>
          have ha := a.isLt
          simp only [Shp.AN, hn, hk, canon, Sum.elim_inl, Fin.val_castSucc, buchRows, Fin.lastCases_castSucc,
            Fin.ext_iff, Fin.val_last]
          split_ifs <;> first | omega | exact hA j (Sum.inl a)
      · simp only [Shp.AN, hn, hk, canon, Sum.elim_inr, buchRows]
        split_ifs <;> first | omega | (rw [show k + 1 + (i : ℕ) - 1 = k + i by omega]; exact hA j (Sum.inr i))
  | @swap S k s A items n h ih =>
    obtain ⟨hk, hm, hn, hit, hs, hA⟩ := ih
    refine ⟨by simp [Shp.k, hk], by simp [Shp.m, hm], by simp [Shp.n, hn], by simp [Shp.items, hit, hk],
      fun i => ?_, fun j t => ?_⟩
    · have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      rcases hi with rfl | rfl
      · simpa [Shp.sN] using hs 1
      · simpa [Shp.sN] using hs 0
    · rcases t with a | i
      · have ha := a.isLt
        simp only [Shp.AN, canon, Sum.elim_inl, hk, swapRows, Sum.map_inl, id]
        split_ifs <;> first | omega | exact hA j (Sum.inl a)
      · have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
        rcases hi with rfl | rfl
        · simp only [Shp.AN, canon, Sum.elim_inr, hk, swapRows, Sum.map_inr, Fin.val_zero, add_zero]
          split_ifs <;> first | omega | exact hA j (Sum.inr 1)
        · simp only [Shp.AN, canon, Sum.elim_inr, hk, swapRows, Sum.map_inr, Fin.val_one]
          split_ifs <;> first | omega | exact hA j (Sum.inr 0)

/-- The items' forms of a shape use only its coordinates. -/
theorem Desc.fit {S : Shp} {k m : ℕ} {s : Fin m → Fin k} {A : Rows k m} {items : List LF} {n : ℕ}
    (h : Desc S k m s A items n) : ∀ L ∈ items, L.c.length ≤ n := by
  induction h with
  | std k => exact stdItems_length_le (k + 1)
  | rev k =>
    intro L hL
    obtain ⟨p, rfl⟩ := List.mem_ofFn.1 hL
    unfold revItemF
    split_ifs
    all_goals simp [unitLF, LF.add, LF.smul, length_addC]
    all_goals omega
  | @last S k s A items n h ih =>
    intro L hL
    obtain ⟨p, rfl⟩ := List.mem_ofFn.1 hL
    unfold lastItemF
    split_ifs
    · exact (length_getD_le ih _).trans (by omega)
    · simp [unitLF]
    · exact (length_getD_le ih _).trans (by omega)
    · have := length_getD_le ih (k + 1)
      simp only [LF.add, LF.smul, length_addC, List.length_map, unitLF, List.length_append,
        List.length_replicate, List.length_singleton]
      omega
  | @swap S k s A items n h ih =>
    intro L hL
    obtain ⟨p, rfl⟩ := List.mem_ofFn.1 hL
    unfold swapItemF
    split_ifs <;> exact length_getD_le ih _

/-- The items' forms of a shape are `DEN` times their exponents. -/
theorem Desc.itemsOK {S : Shp} {k m : ℕ} {s : Fin m → Fin k} {A : Rows k m} {items : List LF} {n : ℕ}
    (h : Desc S k m s A items n) : ItemsOK A items := by
  induction h with
  | std k => exact itemsOK_std (k + 1)
  | rev k => exact itemsOK_rev k
  | last h ih => exact itemsOK_last ih h.fit
  | swap h ih => exact itemsOK_swap ih

theorem Desc.k_pos {S : Shp} {k m : ℕ} {s : Fin m → Fin k} {A : Rows k m} {items : List LF} {n : ℕ}
    (h : Desc S k m s A items n) : 0 < k ∧ 0 < m := by
  induction h with
  | std k => exact ⟨by omega, by omega⟩
  | rev k => exact ⟨by omega, by omega⟩
  | last h ih => exact ⟨by omega, by omega⟩
  | swap h ih => exact ih

/-! ### The checker -/

/-- The length of a box is kept by its tightening. -/
theorem length_tightenList (E : ℤ) : ∀ (cs : List Con) (B : Box), (tightenList E cs B).length = B.length
  | [], _ => rfl
  | C :: cs, B => by
    have h1 : (tightenCon E B C).length = B.length := by
      unfold tightenCon
      suffices h : ∀ (js : List ℕ) (B' : Box), (js.foldl (tightenOne C E) B').length = B'.length from h _ _
      intro js
      induction js with
      | nil => intro B'; rfl
      | cons j js ih => intro B'; rw [List.foldl_cons, ih, length_tightenOne]
    show (tightenList E cs (tightenCon E B C)).length = B.length
    rw [length_tightenList E cs, h1]

/-- The Type II check's `P = (1 − θ + κ) DEN` and `K = κ DEN` at `θ = 21/40`, `κ = 2^{−20}`. -/
def tiiP : ℤ := 95 * 2 ^ 29 + 102400

/-- The Type II check's `K = κ DEN`, `κ = 2^{−20}`. -/
def tiiK : ℤ := 102400

/-- Lemma 4.1's `D₁ = (2θ − 1) DEN` at `θ = 21/40`. -/
def g2D1 : ℤ := 5 * 2 ^ 30

/-- Lemma 4.1's `D₂ = (1 − γ) DEN` at `γ = 1/10`. -/
def g2D2 : ℤ := 90 * 2 ^ 30

/-- The active constraints' forms, by their positions among the constraints. -/
def actsOf (Γ : List Con) (acts : List ℕ) : List LF := acts.map fun i => (Γ.getD i ⟨LF.zero, false⟩).L

/-- The active constraints are among the constraints, and their forms use only the box's coordinates. -/
def actsOK (Γ : List Con) (acts : List ℕ) (n : ℕ) : Bool :=
  acts.all (fun i => decide (i < Γ.length)) && (actsOf Γ acts).all fun g => decide (g.c.length ≤ n)

/-- The weight of a form on the item at the canonical position `p`, from the shape's rows. -/
def wtN (S : Shp) (L : LF) (p : ℕ) : ℤ := ((List.range L.c.length).map fun j => L.c.getD j 0 * S.AN j p).sum - L.ce

/-- The constraints order the primes of a standard node with `k + 1` primes: they hold `ordCon j` for `j < k`. -/
def ordOK (Γ : List Con) (k : ℕ) : Bool :=
  (List.range k).all fun j => Γ.any fun C => C.strict && decide (C.L.c0 = 0) && decide (C.L.ce = 0) &&
    decide (C.L.c = List.replicate j 0 ++ [-1, 1])

/-- The factor of the prime `j` of a dropped standard node with `k + 1` primes. -/
def stdFactor (k : ℕ) (B : Box) (j : ℕ) : ℕ :=
  if j = k then invF (B.getD j (0, 0)).1 (B.getD j (0, 0)).2 else trF (B.getD j (0, 0)).1 (B.getD j (0, 0)).2

/-- The primes' part of a dropped standard node's loss, units `1/SC`: the chain bound (`chain`, when the constraints
order the primes), or else the product of their factors. On disjoint ranges the two agree, and the kernel computes the
product in a few multiplications. -/
def stdPart (k : ℕ) (B : Box) (chain : Bool) : Option ℕ :=
  if chain then (chainDP (fun i => (B.getD i (0, 0)).1) (fun i => (B.getD i (0, 0)).2) (fun i => decide (i = k))
      (k + 1)).map Prod.fst
  else some (prodSC ((List.range (k + 1)).map (stdFactor k B)))

/-- **The dropped standard node's loss**, units `1/SC`: `ω*`'s bound on the box (`omUpK`, units `1/K`) times the
primes' part (`stdPart`), if the box's lower ends are positive and `DEN − Σ_j X_j ≥ 0` on it. -/
def dropStd (E : ℤ) (k : ℕ) (Γ : List Con) (B : Box) (acts : List ℕ) (chain : Bool) : Option ℕ :=
  if actsOK Γ acts B.length = true ∧ k + 1 ≤ B.length ∧
      (List.range (k + 1)).all (fun j => decide (0 < (B.getD j (0, 0)).1 ∧
        (B.getD j (0, 0)).1 ≤ (B.getD j (0, 0)).2)) = true ∧
      0 ≤ (numF k).minD B E (actsOf Γ acts) ∧ (!chain || ordOK Γ k) = true then
    (stdPart k B chain).map fun D => SieveCert.cdiv (omUpK ((numF k).minD B E (actsOf Γ acts)).toNat
      (B.getD k (0, 0)).2.toNat ((numF k).maxD B E (actsOf Γ acts)).toNat (B.getD k (0, 0)).1.toNat * D) SieveCert.K
  else none

/-- The item in the coordinate `0` of a node with two rough items. -/
def gOf (S : Shp) : ℕ := if S.AN 0 (S.k + 1) = 1 then 1 else 0

/-- The factor of the prime `a` of a dropped node with two rough items sifted by the primes `sc` and `sg`. -/
def twoFactor (items : List LF) (B : Box) (E : ℤ) (sc sg a : ℕ) : ℕ :=
  if a = sc ∨ a = sg then invF (loF items B E a) (hiF items B E a) else trF (loF items B E a) (hiF items B E a)

/-- **The chain bounds of a node with two rough items**, units `1/SC`: the programme on each of the chains `c₁`, `c₂`,
if they partition the `K` primes and the constraints order them. -/
def chainTwo (E : ℤ) (Γ : List Con) (B : Box) (it : List LF) (K sc sg : ℕ) (c₁ c₂ : List ℕ) : Option (ℕ × ℕ) :=
  if decide (c₁ ++ c₂).Nodup = true ∧ (c₁ ++ c₂).all (fun a => decide (a < K)) = true ∧
      (List.range K).all (fun a => decide (a ∈ c₁ ++ c₂)) = true ∧ chainOK Γ it c₁ = true ∧
      chainOK Γ it c₂ = true then
    match chainDP (fun i => loF it B E (c₁.getD i 0)) (fun i => hiF it B E (c₁.getD i 0))
        (fun i => decide (c₁.getD i 0 = sc ∨ c₁.getD i 0 = sg)) c₁.length,
      chainDP (fun i => loF it B E (c₂.getD i 0)) (fun i => hiF it B E (c₂.getD i 0))
        (fun i => decide (c₂.getD i 0 = sc ∨ c₂.getD i 0 = sg)) c₂.length with
    | some (D₁, _), some (D₂, _) => some (D₁, D₂)
    | _, _ => none
  else none

/-- The primes' factors of a dropped node with two rough items, units `1/SC`: its two chain bounds (`chain`), or else
each prime's factor. -/
def twoParts (chain : Bool) (E : ℤ) (Γ : List Con) (B : Box) (it : List LF) (K sc sg : ℕ) (c₁ c₂ : List ℕ) :
    List ℕ :=
  match if chain then chainTwo E Γ B it K sc sg c₁ c₂ else none with
  | some (D₁, D₂) => [D₁, D₂]
  | none => (List.range K).map (twoFactor it B E sc sg)

/-- **The dropped node with two rough items' loss**, units `1/SC`: the bounds of `ω*` for the two items (units `1/K`),
the coordinate `0`'s width and the primes' factors (`twoParts`), if the coordinate `0` is the item `g` times the primes
with coefficient `1`. -/
def dropTwo (E : ℤ) (S : Shp) (Γ : List Con) (B : Box) (acts : List ℕ) (chain : Bool) : Option ℕ :=
  let g := gOf S
  let c := 1 - g
  let K := S.k
  let it := S.items
  let acts' := actsOf Γ acts
  let Nc := numC (it.getD (K + c) LF.zero)
  let J := (Finset.range K).filter (fun a => S.AN 0 a = 1)
  let sc := S.sN c
  let sg := S.sN g
  if actsOK Γ acts B.length = true ∧ 0 < B.length ∧ sc ≠ sg ∧ sc < K ∧ sg < K ∧
      (List.range K).all (fun a => decide ((S.AN 0 a = 0 ∨ S.AN 0 a = 1) ∧ 0 < loF it B E a ∧
        loF it B E a ≤ hiF it B E a)) = true ∧
      S.AN 0 (K + g) = 1 ∧ S.AN 0 (K + c) = 0 ∧ NU0 ≤ loF it B E sg ∧ 0 < (B.getD 0 (0, 0)).1 ∧
      (B.getD 0 (0, 0)).1 ≤ (B.getD 0 (0, 0)).2 ∧ 0 ≤ Nc.minD B E acts' then
    some (SieveCert.cdiv (omUpK (Nc.minD B E acts').toNat (hiF it B E sc).toNat (Nc.maxD B E acts').toNat
        (loF it B E sc).toNat *
      omUpK (max 0 ((B.getD 0 (0, 0)).1 - ∑ a ∈ J, hiF it B E a)).toNat (hiF it B E sg).toNat
        (max 0 ((B.getD 0 (0, 0)).2 - ∑ a ∈ J, loF it B E a)).toNat (loF it B E sg).toNat *
      prodSC (SieveCert.cdiv (SC * ((B.getD 0 (0, 0)).2 - (B.getD 0 (0, 0)).1).toNat) DEN ::
        twoParts chain E Γ B it K sc sg (S.chain 0) (S.chain 1))) (SieveCert.K * SieveCert.K))
  else none

/-- The constraint `C + c D`, of `C`'s strictness: it holds where `C` and `D` do. -/
def combCon (C D : Con) (c : ℕ) : Con := ⟨C.L.add (D.L.smul c), C.strict⟩

/-- **A certificate**: the decisions on a node and its descendants. -/
inductive Cert
  | out
  | outC (i : ℕ)
  | outE (j : ℕ)
  | tighten (t : Cert)
  | up (j : ℕ) (lower : Bool) (i : ℕ) (v : ℤ) (t : Cert)
  | comb (i j c : ℕ) (t : Cert)
  | split (C : Con) (u w : ℕ) (t₁ t₂ : Cert)
  | cut (j : ℕ) (p : ℤ) (u w : ℕ) (t₁ t₂ : Cert)
  | tii (acts labels : List ℕ) (ng : ℕ)
  | g2 (acts labels : List ℕ)
  | dec (acts labels : List ℕ) (kind : ℕ) (t : Cert)
  | rev (acts labels : List ℕ) (kind : ℕ) (t : Cert)
  | swap (t : Cert)
  | drop (acts : List ℕ) (chain : Bool)

/-- **The checker**: the loss of a node with shape `S`, constraints `Γ` and box `B`, of sign `+` (`b`) or `−`, in units
`1/SC`, if the certificate's decisions pass. -/
def run (E : ℤ) : Cert → Shp → List Con → Box → Bool → Option ℕ
  | .out, _, Γ, B, _ => if Out E Γ B = true then some 0 else none
  | .outC i, _, Γ, B, _ => if i < Γ.length ∧ (Γ.getD i ⟨LF.zero, false⟩).fails B E = true then some 0 else none
  | .outE j, _, _, B, _ => if j < B.length ∧ (B.getD j (0, 0)).2 ≤ (B.getD j (0, 0)).1 then some 0 else none
  | .tighten t, S, Γ, B, b => run E t S Γ (tightenList E Γ B) b
  | .up j lower i v t, S, Γ, B, b =>
    if i < Γ.length ∧ upOK (Γ.getD i ⟨LF.zero, false⟩) E B j lower v = true then run E t S Γ (cutAt B j lower v) b
    else none
  | .comb i j c t, S, Γ, B, b =>
    if i < Γ.length ∧ j < Γ.length then
      run E t S (combCon (Γ.getD i ⟨LF.zero, false⟩) (Γ.getD j ⟨LF.zero, false⟩) c :: Γ) B b
    else none
  | .split C u w t₁ t₂, S, Γ, B, b =>
    if fits [C] S.n = true ∧ u < S.k + S.m ∧ w < S.k + S.m ∧ wtN S C.L u ≠ wtN S C.L w then
      (run E t₁ S (C :: Γ) B b).bind fun L₁ => (run E t₂ S (C.neg :: Γ) B b).map (L₁ + ·)
    else none
  | .cut j p u w t₁ t₂, S, Γ, B, b =>
    if u < S.k + S.m ∧ w < S.k + S.m ∧ wtN S (ltCon j p).L u ≠ wtN S (ltCon j p).L w then
      (run E t₁ S Γ (B.modify j fun b' => (b'.1, min b'.2 p)) b).bind fun L₁ =>
        (run E t₂ S Γ (B.modify j fun b' => (max b'.1 p, b'.2)) b).map (L₁ + ·)
    else none
  | .tii acts labels ng, S, Γ, B, _ =>
    if actsOK Γ acts B.length = true ∧ labels.length = S.k + S.m ∧
        (List.range (S.k + S.m)).all (fun p => decide (labels.getD p 0 < ng)) = true ∧
        tiiCheck tiiP tiiK E B (actsOf Γ acts) S.items labels ng = true then some 0 else none
  | .g2 acts labels, S, Γ, B, _ =>
    if actsOK Γ acts B.length = true ∧ labels.length = S.k + S.m ∧
        (List.range (S.k + S.m)).all (fun p => decide (labels.getD p 0 < 3)) = true ∧
        g2Check g2D1 g2D2 E B (actsOf Γ acts) S.items labels = true then some 0 else none
  | .dec acts labels kind t, .std k, Γ, B, b =>
    if actsOK Γ acts B.length = true ∧
        typeICheck (stdItems (k + 1)) (k + 1) E B (actsOf Γ acts) labels kind = true then
      run E t (.std (k + 1)) (geCon (k + 1) :: (Γ ++ [ordCon k])) (B ++ [(NU0, (B.getD k (0, 0)).2)]) (!b)
    else none
  | .dec acts labels kind t, S, Γ, B, b =>
    if S.m = 2 ∧ actsOK Γ acts B.length = true ∧
        typeICheck S.items (S.k + 1) E B (actsOf Γ acts) labels kind = true then
      run E t (.last S) (geL (S.items.getD (S.k + 1) LF.zero) B.length ::
          (Γ ++ [ordL (S.items.getD (S.sN 1) LF.zero) B.length]))
        (B ++ [(NU0, (S.items.getD (S.sN 1) LF.zero).maxB B E)]) (!b)
    else none
  | .rev acts labels kind t, .std (k + 1), Γ, B, b =>
    if actsOK Γ acts B.length = true ∧ typeICheck (stdItems (k + 2)) 0 E B (actsOf Γ acts) labels kind = true then
      run E t (.rev k) (Γ ++ [halfCon k]) (B ++ [(NU0, (B.getD 0 (0, 0)).2)]) (!b)
    else none
  | .rev _ _ _ _, _, _, _, _ => none
  | .swap t, S, Γ, B, b => if S.m = 2 then run E t (.swap S) Γ B b else none
  | .drop acts c, .std k, Γ, B, true => dropStd E k Γ B acts c
  | .drop acts c, S, Γ, B, true => if S.m = 2 then dropTwo E S Γ B acts c else none
  | .drop _ _, _, _, _, false => none

/-! ### The checker's soundness -/

theorem combCon_holds {C D : Con} {c : ℕ} {X : ℕ → ℝ} {H : ℝ} (hC : C.Holds X H) (hD : D.Holds X H) :
    (combCon C D c).Holds X H := by
  have hD' := Con.val_le hD
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hcD : (c : ℝ) * D.L.val X H ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hD'
  unfold combCon Con.Holds at *
  simp only [LF.val_add, LF.val_smul, Int.cast_natCast]
  split_ifs at hC ⊢ <;> linarith

/-- A constraint combined from two of the constraints keeps the invariant. -/
theorem Sound.comb {N : Node} {A : Rows N.k N.m} {E : ℤ} {Γ : List Con} {B : Box} (h : Sound N A E Γ B) {C D : Con}
    (hC : C ∈ Γ) (hD : D ∈ Γ) (c : ℕ) : Sound N A E (combCon C D c :: Γ) B := by
  intro x hx v hv1 hv2 hc hH
  obtain ⟨hB, hΓ⟩ := h x hx v hv1 hv2 hc hH
  refine ⟨hB, fun c' hc' => ?_⟩
  rcases List.mem_cons.1 hc' with rfl | hc'
  · exact combCon_holds (hΓ C hC) (hΓ D hD)
  · exact hΓ c' hc'

/-- A form's weight on an item is the one computed from the shape's rows. -/
theorem Desc.wt_eq {S : Shp} {k m : ℕ} {s : Fin m → Fin k} {A : Rows k m} {items : List LF} {n : ℕ}
    (h : Desc S k m s A items n) (L : LF) (t : Fin k ⊕ Fin m) : wt A L t = (wtN S L (canon t) : ℝ) := by
  obtain ⟨-, -, -, -, -, hA⟩ := h.data
  unfold wt wtN
  rw [Int.cast_sub, cast_list_sum_map_range]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [Int.cast_mul, hA j t]

theorem canon_lt {k m : ℕ} (t : Fin k ⊕ Fin m) : canon t < k + m := by
  rcases t with a | i
  · show a.val < k + m; have := a.isLt; omega
  · show k + i.val < k + m; have := i.isLt; omega

/-- The item at a canonical position. -/
def decanon {k m : ℕ} (p : ℕ) (hp : p < k + m) : Fin k ⊕ Fin m :=
  if h : p < k then Sum.inl ⟨p, h⟩ else Sum.inr ⟨p - k, by omega⟩

theorem canon_decanon {k m : ℕ} {p : ℕ} (hp : p < k + m) : canon (decanon p hp : Fin k ⊕ Fin m) = p := by
  unfold decanon
  split_ifs with h
  · rfl
  · show k + (p - k) = p
    omega

/-- A condition with two items of different weights, and its negation, keep the conditions not functions of the product
alone. -/
theorem condsOK_cons {k m : ℕ} {A : Rows k m} {conds : List (Cond k m)} (h : CondsOK conds) {C : Con}
    {u w : Fin k ⊕ Fin m} (huw : wt A C.L u ≠ wt A C.L w) :
    CondsOK (toCond A C :: conds) ∧ CondsOK ((toCond A C).neg :: conds) := by
  have he : ∀ t, Sum.elim (toCond A C).e (toCond A C).f t = wt A C.L t := by
    rintro (a | i) <;> rfl
  have hn : ∀ t, Sum.elim (toCond A C).neg.e (toCond A C).neg.f t = -wt A C.L t := by
    rintro (a | i) <;> rfl
  refine ⟨fun C' hC' => ?_, fun C' hC' => ?_⟩
  · rcases List.mem_cons.1 hC' with rfl | hC'
    · exact ⟨u, w, by rw [he, he]; exact huw⟩
    · exact h C' hC'
  · rcases List.mem_cons.1 hC' with rfl | hC'
    · refine ⟨u, w, fun hh => huw ?_⟩
      rw [hn, hn] at hh
      linarith
    · exact h C' hC'

/-- The active constraints of a passing check are among the constraints and use only the box's coordinates. -/
theorem acts_of_OK {Γ : List Con} {acts : List ℕ} {n : ℕ} (h : actsOK Γ acts n = true) :
    (∀ g ∈ actsOf Γ acts, ∃ c ∈ Γ, c.L = g) ∧ ∀ g ∈ actsOf Γ acts, g.c.length ≤ n := by
  unfold actsOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  refine ⟨fun g hg => ?_, h.2⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
  exact ⟨Γ.getD i ⟨LF.zero, false⟩, by rw [List.getD_eq_getElem _ _ (h.1 i hi)]; exact List.getElem_mem _, rfl⟩

theorem fits_iff {cs : List Con} {n : ℕ} : fits cs n = true ↔ ∀ C ∈ cs, C.L.c.length ≤ n := by
  simp [fits]

theorem fits_std_child {k : ℕ} {Γ : List Con} (hf : fits Γ (k + 1) = true) :
    fits (geCon (k + 1) :: (Γ ++ [ordCon k])) (k + 2) = true := by
  rw [fits_iff] at hf ⊢
  intro C hC
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | hC | rfl
  · simp [geCon]
  · exact (hf C hC).trans (by omega)
  · simp [ordCon]

theorem fits_rev_child {k : ℕ} {Γ : List Con} (hf : fits Γ (k + 2) = true) :
    fits (Γ ++ [halfCon k]) (k + 3) = true := by
  rw [fits_iff] at hf ⊢
  intro C hC
  simp only [List.mem_append, List.mem_singleton] at hC
  rcases hC with hC | rfl
  · exact (hf C hC).trans (by omega)
  · simp [halfCon]

theorem fits_last_child {n : ℕ} {Γ : List Con} (hf : fits Γ n = true) {F G : LF} (hF : F.c.length ≤ n)
    (hG : G.c.length ≤ n) : fits (geL G n :: (Γ ++ [ordL F n])) (n + 1) = true := by
  rw [fits_iff] at hf ⊢
  intro C hC
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | hC | rfl
  · simp only [geL, LF.add, LF.smul, length_addC, List.length_map, unitLF, List.length_append,
      List.length_replicate, List.length_singleton]
    omega
  · exact (hf C hC).trans (by omega)
  · simp only [ordL, LF.add, LF.smul, length_addC, List.length_map, unitLF, List.length_append,
      List.length_replicate, List.length_singleton]
    omega

theorem fits_cons {n : ℕ} {Γ : List Con} (hf : fits Γ n = true) {C : Con} (hC : fits [C] n = true) :
    fits (C :: Γ) n = true ∧ fits (C.neg :: Γ) n = true := by
  rw [fits_iff] at hf hC ⊢
  rw [fits_iff]
  have h1 : C.L.c.length ≤ n := hC C List.mem_cons_self
  refine ⟨fun C' hC' => ?_, fun C' hC' => ?_⟩
  · rcases List.mem_cons.1 hC' with rfl | hC'
    · exact h1
    · exact hf C' hC'
  · rcases List.mem_cons.1 hC' with rfl | hC'
    · simpa [Con.neg] using h1
    · exact hf C' hC'

theorem Inv.std {k : ℕ} {conds : List (Cond (k + 1) 1)} (h : Inv (std k conds)) : StdInv k conds :=
  fun x hx v hv1 hv2 hc => ⟨(h x hx v hv1 hv2 hc).1, (h x hx v hv1 hv2 hc).2 0⟩

/-! ### The drops' losses in fixed point -/

theorem ordOK_mem {Γ : List Con} {k : ℕ} (h : ordOK Γ k = true) : ∀ j < k, ordCon j ∈ Γ := by
  intro j hj
  simp only [ordOK, List.all_eq_true, List.mem_range, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨C, hC, ⟨⟨hs, h0⟩, he⟩, hc⟩ := h j hj
  obtain ⟨⟨c0, c, ce⟩, st⟩ := C
  simp only at hs h0 he hc
  subst hs h0 he hc
  exact hC

/-- **The dropped standard node's loss is sound.** -/
theorem dropStd_sound {ρ : ℝ} (hρ : 0 < ρ) (hρ20 : 12 * ρ < 1 / 20) {E : ℤ} (hE : 0 < E) {k : ℕ}
    {conds : List (Cond (k + 1) 1)} {Γ : List Con} {B : Box} (h : Sound (std k conds) (stdRows (k + 1)) E Γ B)
    (hinv : StdInv k conds) {acts : List ℕ} {chain : Bool} {L : ℕ} (hd : dropStd E k Γ B acts chain = some L) :
    OK (21 / 40) ρ 1 (fun x y => ((std k conds).count x y : ℝ)) (L / SC) := by
  unfold dropStd at hd
  split_ifs at hd with hcheck
  obtain ⟨D, hD, rfl⟩ := Option.map_eq_some_iff.1 hd
  obtain ⟨hacts, hlen, hbox, hn0, hord⟩ := hcheck
  obtain ⟨ha1, ha2⟩ := acts_of_OK hacts
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hbox
  set a := (numF k).minD B E (actsOf Γ acts) with ha
  set b := (numF k).maxD B E (actsOf Γ acts) with hb
  set lo := (B.getD k (0, 0)).1 with hlo
  set hi := (B.getD k (0, 0)).2 with hhi
  obtain ⟨hlo0, hlohi⟩ := hbox k (by omega)
  have hloN : 0 < lo.toNat := by omega
  have hhiN : 0 < hi.toNat := by omega
  set Ω : ℝ := (omUpK a.toNat hi.toNat b.toNat lo.toNat : ℝ) / SieveCert.K with hΩ
  have hK := SieveCert.K_pos'
  have hΩ0 : 0 ≤ Ω := by positivity
  have hω : ∀ u : ℝ, (a : ℝ) / hi ≤ u → u ≤ (b : ℝ) / lo → SieveCert.omegaC u ≤ Ω := by
    intro u h1 h2
    refine omegaC_le_omUpK hhiN hloN ?_ ?_
    · have e1 : ((a.toNat : ℕ) : ℝ) = a := by exact_mod_cast Int.toNat_of_nonneg hn0
      have e2 : ((hi.toNat : ℕ) : ℝ) = hi := by exact_mod_cast Int.toNat_of_nonneg (by omega)
      rwa [e1, e2]
    · have e1 : (b : ℝ) ≤ ((b.toNat : ℕ) : ℝ) := by exact_mod_cast Int.self_le_toNat b
      have e2 : ((lo.toNat : ℕ) : ℝ) = lo := by exact_mod_cast Int.toNat_of_nonneg (by omega)
      rw [e2]
      exact h2.trans (div_le_div_of_nonneg_right e1 (by exact_mod_cast hlo0.le))
  have hS := SC_pos
  -- the primes' part: the product of their factors, or the chain bound
  have key : ∃ X : ℝ, X ≤ (D : ℝ) / SC ∧ OK (21 / 40) ρ 1 (fun x y => ((std k conds).count x y : ℝ)) (Ω * X) := by
    cases chain
    · simp only [stdPart, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hD
      subst hD
      refine ⟨_, ?_, h.OK_of_drop hE hinv hlen (fun j hj => (hbox j hj).1) (fun j hj => (hbox j hj).2) ha1 ha2 hn0
        hΩ0 hω (θ := 21 / 40) hρ hρ20⟩
      have hfac : ∀ j : Fin (k + 1), (if j = Fin.last k then (DEN : ℝ) / (B.getD j (0, 0)).1 -
          DEN / (B.getD j (0, 0)).2 else trB (B.getD j (0, 0)).1 (B.getD j (0, 0)).2) ≤
            (stdFactor k B j : ℝ) / SC := by
        intro j
        obtain ⟨h1, h2⟩ := hbox j j.isLt
        unfold stdFactor
        by_cases hj : j = Fin.last k
        · rw [ite_eq_left hj, ite_eq_left (by rw [hj]; rfl)]
          exact inv_le_invF h1 h2
        · rw [ite_eq_right hj, ite_eq_right (fun h' => hj (Fin.ext (by simpa using h')))]
          exact trB_le_trF h1 h2
      have hfac0 : ∀ j : Fin (k + 1), 0 ≤ (if j = Fin.last k then (DEN : ℝ) / (B.getD j (0, 0)).1 -
          DEN / (B.getD j (0, 0)).2 else trB (B.getD j (0, 0)).1 (B.getD j (0, 0)).2) := by
        intro j
        obtain ⟨h1, h2⟩ := hbox j j.isLt
        have h1' : (0 : ℝ) < (B.getD j (0, 0)).1 := by exact_mod_cast h1
        have h2' : ((B.getD j (0, 0)).1 : ℝ) ≤ (B.getD j (0, 0)).2 := by exact_mod_cast h2
        split_ifs
        · have := div_le_div_of_nonneg_left DEN_pos.le h1' h2'
          linarith
        · unfold trB
          have h3 : (0 : ℝ) ≤ ((B.getD j (0, 0)).2 - (B.getD j (0, 0)).1) := by linarith
          have h4 : (0 : ℝ) ≤ ((B.getD j (0, 0)).2 + (B.getD j (0, 0)).1) := by linarith
          have h5 : (0 : ℝ) < 2 * (B.getD j (0, 0)).1 * (B.getD j (0, 0)).2 :=
            mul_pos (mul_pos two_pos h1') (by linarith)
          exact div_nonneg (mul_nonneg h3 h4) h5.le
      refine le_trans (Finset.prod_le_prod₀ (fun j _ => hfac0 j) fun j _ => hfac j) ?_
      have e : (∏ j : Fin (k + 1), (stdFactor k B j : ℝ) / SC) =
          (((List.range (k + 1)).map (stdFactor k B)).map fun f : ℕ => (f : ℝ) / SC).prod := by
        rw [List.map_map, list_prod_map_range]
        exact Fin.prod_univ_eq_prod_range (fun j => (stdFactor k B j : ℝ) / SC) (k + 1)
      rw [e]
      exact prod_le_prodSC _
    · simp only [stdPart, ↓reduceIte] at hD
      obtain ⟨⟨D', eK⟩, hD', rfl⟩ := Option.map_eq_some_iff.1 hD
      simp only [Bool.not_true, Bool.false_or] at hord
      obtain ⟨heK, hP⟩ := chainDP_sound hD'
      exact ⟨_, le_rfl, h.OK_of_dropC hE hinv hlen (fun j hj => (hbox j hj).1) (ordOK_mem hord) ha1 ha2 hn0 hΩ0 hω
        heK (by positivity) hP (θ := 21 / 40) hρ hρ20⟩
  obtain ⟨X, hXD, hdrop⟩ := key
  refine OK_mono ?_ hdrop
  have hc := SieveOmegaB.div_le_cdiv (omUpK a.toNat hi.toNat b.toNat lo.toNat * D) SieveCert.K
    (by norm_num [SieveCert.K])
  push_cast at hc
  calc Ω * X ≤ Ω * ((D : ℝ) / SC) := mul_le_mul_of_nonneg_left hXD hΩ0
    _ = ((omUpK a.toNat hi.toNat b.toNat lo.toNat : ℝ) * D / SieveCert.K) / SC := by rw [hΩ]; ring
    _ ≤ _ := div_le_div_of_nonneg_right hc hS.le

/-- A sum over the primes with a property of their positions. -/
theorem sum_filter_fin {k : ℕ} (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℝ) :
    ∑ a ∈ univ.filter (fun a : Fin k => P a), f a = ∑ a ∈ (Finset.range k).filter P, f a := by
  rw [sum_filter, sum_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if P i then f i else 0) k

/-- **The chain bounds of a node with two rough items are sound**: the chains partition the primes, the constraints
order them, and the chain sums below their last breakpoints have the limit superiors at most the bounds. -/
theorem chainTwo_sound {E : ℤ} {Γ : List Con} {B : Box} {it : List LF} {K sc sg : ℕ} {c₁ c₂ : List ℕ} {D₁ D₂ : ℕ}
    (h : chainTwo E Γ B it K sc sg c₁ c₂ = some (D₁, D₂)) :
    (c₁ ++ c₂).Nodup ∧ (∀ a, a ∈ c₁ ++ c₂ ↔ a < K) ∧ ShortSieveCert.chainOK Γ it c₁ = true ∧
      ShortSieveCert.chainOK Γ it c₂ = true ∧ ∃ e₁ e₂ : ℤ, (∀ i < c₁.length, hiF it B E (c₁.getD i 0) ≤ e₁) ∧
        (∀ i < c₂.length, hiF it B E (c₂.getD i 0) ≤ e₂) ∧
        SieveRough.EvLe (fun x => ShortSieveChain.chainSum (ShortSieveChain.sfx
          (fun i => twoMem it B E sc sg x (c₁.getD i 0)) c₁.length 0) (thr x e₁)) (D₁ / SC) ∧
        SieveRough.EvLe (fun x => ShortSieveChain.chainSum (ShortSieveChain.sfx
          (fun i => twoMem it B E sc sg x (c₂.getD i 0)) c₂.length 0) (thr x e₂)) (D₂ / SC) := by
  unfold chainTwo at h
  split_ifs at h with hcheck
  obtain ⟨hnd, hlt, hall, hc1, hc2⟩ := hcheck
  simp only [List.all_eq_true, decide_eq_true_eq, List.mem_range] at hlt hall hnd
  cases h1 : chainDP (fun i => loF it B E (c₁.getD i 0)) (fun i => hiF it B E (c₁.getD i 0))
      (fun i => decide (c₁.getD i 0 = sc ∨ c₁.getD i 0 = sg)) c₁.length with
  | none => simp only [h1] at h; exact absurd h (by simp)
  | some p₁ =>
    cases h2 : chainDP (fun i => loF it B E (c₂.getD i 0)) (fun i => hiF it B E (c₂.getD i 0))
        (fun i => decide (c₂.getD i 0 = sc ∨ c₂.getD i 0 = sg)) c₂.length with
    | none => simp only [h1, h2] at h; exact absurd h (by simp)
    | some p₂ =>
      obtain ⟨D₁', e₁⟩ := p₁
      obtain ⟨D₂', e₂⟩ := p₂
      simp only [h1, h2, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨he1, hP1⟩ := chainDP_sound h1
      obtain ⟨he2, hP2⟩ := chainDP_sound h2
      exact ⟨hnd, fun a => ⟨hlt a, hall a⟩, hc1, hc2, e₁, e₂, he1, he2, hP1, hP2⟩

/-- **The dropped node with two rough items' loss is sound.** -/
theorem dropTwo_sound {ρ : ℝ} (hρ : 0 < ρ) (hρ20 : 12 * ρ < 1 / 20) {E : ℤ} (hE : 0 < E) {S : Shp} {k : ℕ}
    {s : Fin 2 → Fin k} {A : Rows k 2} {items : List LF} {n : ℕ} (hD : Desc S k 2 s A items n)
    {conds : List (Cond k 2)} {Γ : List Con} {B : Box} (h : Sound ⟨k, 2, s, conds⟩ A E Γ B)
    (hinv : Inv ⟨k, 2, s, conds⟩) (hlen : B.length = n) {acts : List ℕ} {chain : Bool} {L : ℕ}
    (hd : dropTwo E S Γ B acts chain = some L) :
    OK (21 / 40) ρ 1 (fun x y => ((⟨k, 2, s, conds⟩ : Node).count x y : ℝ)) (L / SC) := by
  obtain ⟨hk, -, -, hit, hs, hA⟩ := hD.data
  unfold dropTwo at hd
  simp only [hk, hit] at hd
  -- the item `g` of the coordinate `0`, and the other `c`
  set g : Fin 2 := if S.AN 0 (k + 1) = 1 then 1 else 0 with hg
  have hgv : gOf S = (g : ℕ) := by
    simp only [hg, gOf, hk]
    split_ifs <;> rfl
  have hcv : 1 - gOf S = (g.rev : ℕ) := by
    rw [Fin.val_rev, hgv]
    omega
  rw [hcv, hgv, hs g.rev, hs g] at hd
  split_ifs at hd with hcheck
  obtain rfl := (Option.some.inj hd).symm
  obtain ⟨hacts, hB0, hsne, hsc, hsg, hall, hAg, hAc, hNU, hlo0, hlohi0, hn0⟩ := hcheck
  obtain ⟨ha1, ha2⟩ := acts_of_OK hacts
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
  have hAg' : A 0 (Sum.inr g) = 1 := by rw [← hA 0 (Sum.inr g)]; exact hAg
  have hAc' : A 0 (Sum.inr g.rev) = 0 := by rw [← hA 0 (Sum.inr g.rev)]; exact hAc
  have hA0 : ∀ a : Fin k, A 0 (Sum.inl a) = 0 ∨ A 0 (Sum.inl a) = 1 := fun a => by
    rw [← hA 0 (Sum.inl a)]
    exact (hall a a.isLt).1
  have hsg' : s g.rev ≠ s g := fun he => hsne (by rw [he])
  have hlo : ∀ a : Fin k, 0 < loF items B E a := fun a => (hall a a.isLt).2.1
  have hlohi : ∀ a : Fin k, loF items B E a ≤ hiF items B E a := fun a => (hall a a.isLt).2.2
  -- the bounds of `ω*`
  set Nc := numC (items.getD (k + g.rev) LF.zero) with hNc
  set J := (Finset.range k).filter (fun a => S.AN 0 a = 1) with hJ
  have hJ' : ∀ f : ℕ → ℝ, ∑ a ∈ univ.filter (fun a : Fin k => A 0 (Sum.inl a) = 1), f a = ∑ a ∈ J, f a := by
    intro f
    rw [hJ, ← sum_filter_fin (fun a => S.AN 0 a = 1) f]
    refine sum_congr ?_ fun _ _ => rfl
    ext a
    simp only [mem_filter, mem_univ, true_and]
    rw [← hA 0 (Sum.inl a)]
    rfl
  have hK := SieveCert.K_pos'
  set lc := loF items B E (s g.rev) with hlc
  set hc := hiF items B E (s g.rev) with hhc
  set lg := loF items B E (s g) with hlg
  set hg' := hiF items B E (s g) with hhg
  have hlc0 := hlo (s g.rev)
  have hlg0 := hlo (s g)
  have hlchc := hlohi (s g.rev)
  have hlghg := hlohi (s g)
  set Ωc : ℝ := (omUpK (Nc.minD B E (actsOf Γ acts)).toNat hc.toNat (Nc.maxD B E (actsOf Γ acts)).toNat
    lc.toNat : ℝ) / SieveCert.K with hΩc
  set Ωg : ℝ := (omUpK (max 0 ((B.getD 0 (0, 0)).1 - ∑ a ∈ J, hiF items B E a)).toNat hg'.toNat
    (max 0 ((B.getD 0 (0, 0)).2 - ∑ a ∈ J, loF items B E a)).toNat lg.toNat : ℝ) / SieveCert.K with hΩg
  have hΩc0 : 0 ≤ Ωc := by positivity
  have hΩg0 : 0 ≤ Ωg := by positivity
  have hωc : ∀ u : ℝ, (Nc.minD B E (actsOf Γ acts) : ℝ) / hc ≤ u → u ≤ (Nc.maxD B E (actsOf Γ acts) : ℝ) / lc →
      SieveCert.omegaC u ≤ Ωc := by
    intro u h1 h2
    refine omegaC_le_omUpK (by omega) (by omega) ?_ ?_
    · have e1 : (((Nc.minD B E (actsOf Γ acts)).toNat : ℕ) : ℝ) = Nc.minD B E (actsOf Γ acts) := by
        exact_mod_cast Int.toNat_of_nonneg hn0
      have e2 : ((hc.toNat : ℕ) : ℝ) = hc := by exact_mod_cast Int.toNat_of_nonneg (by omega)
      rwa [e1, e2]
    · have e1 : (Nc.maxD B E (actsOf Γ acts) : ℝ) ≤ (((Nc.maxD B E (actsOf Γ acts)).toNat : ℕ) : ℝ) := by
        exact_mod_cast Int.self_le_toNat _
      have e2 : ((lc.toNat : ℕ) : ℝ) = lc := by exact_mod_cast Int.toNat_of_nonneg (by omega)
      rw [e2]
      exact h2.trans (div_le_div_of_nonneg_right e1 (by exact_mod_cast hlc0.le))
  have hωg : ∀ u : ℝ, (((B.getD 0 (0, 0)).1 : ℝ) - ∑ a ∈ univ.filter (fun a => A 0 (Sum.inl a) = 1),
      (hiF items B E a : ℝ)) / hg' ≤ u →
      u ≤ (((B.getD 0 (0, 0)).2 : ℝ) - ∑ a ∈ univ.filter (fun a => A 0 (Sum.inl a) = 1), (loF items B E a : ℝ)) /
        lg → SieveCert.omegaC u ≤ Ωg := by
    intro u h1 h2
    rw [hJ' fun a => (hiF items B E a : ℝ)] at h1
    rw [hJ' fun a => (loF items B E a : ℝ)] at h2
    by_cases hu : u < 0
    · unfold SieveCert.omegaC
      rw [ite_eq_left (by linarith)]
      exact hΩg0
    push Not at hu
    refine omegaC_le_omUpK (by omega) (by omega) ?_ ?_
    · have e2 : ((hg'.toNat : ℕ) : ℝ) = hg' := by exact_mod_cast Int.toNat_of_nonneg (by omega)
      rw [e2]
      rcases le_or_gt ((B.getD 0 (0, 0)).1 - ∑ a ∈ J, hiF items B E a) 0 with hN | hN
      · rw [max_eq_left hN]
        simpa using hu
      · rw [max_eq_right hN.le]
        have e1 : ((((B.getD 0 (0, 0)).1 - ∑ a ∈ J, hiF items B E a).toNat : ℕ) : ℝ) =
            ((B.getD 0 (0, 0)).1 : ℝ) - ∑ a ∈ J, (hiF items B E a : ℝ) := by
          have h' : ((((B.getD 0 (0, 0)).1 - ∑ a ∈ J, hiF items B E a).toNat : ℕ) : ℝ) =
              (((B.getD 0 (0, 0)).1 - ∑ a ∈ J, hiF items B E a : ℤ) : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hN.le
          rw [h']
          push_cast
          rfl
        rw [e1]
        exact h1
    · have e2 : ((lg.toNat : ℕ) : ℝ) = lg := by exact_mod_cast Int.toNat_of_nonneg (by omega)
      have e1 : ((B.getD 0 (0, 0)).2 : ℝ) - ∑ a ∈ J, (loF items B E a : ℝ) ≤
          (((max 0 ((B.getD 0 (0, 0)).2 - ∑ a ∈ J, loF items B E a)).toNat : ℕ) : ℝ) := by
        have := Int.self_le_toNat (max 0 ((B.getD 0 (0, 0)).2 - ∑ a ∈ J, loF items B E a))
        have h3 := le_max_right (0 : ℤ) ((B.getD 0 (0, 0)).2 - ∑ a ∈ J, loF items B E a)
        have h4 : (((B.getD 0 (0, 0)).2 - ∑ a ∈ J, loF items B E a : ℤ) : ℝ) ≤
            (((max 0 ((B.getD 0 (0, 0)).2 - ∑ a ∈ J, loF items B E a)).toNat : ℤ) : ℝ) := by
          exact_mod_cast h3.trans this
        push_cast at h4
        exact h4
      rw [e2]
      exact h2.trans (div_le_div_of_nonneg_right e1 (by exact_mod_cast hlg0.le))
  -- the primes' part: the chain bounds, or else the primes' factors
  set W := SieveCert.cdiv (SC * ((B.getD 0 (0, 0)).2 - (B.getD 0 (0, 0)).1).toNat) DEN with hW
  set Fs := twoParts chain E Γ B items k (s g.rev) (s g) (S.chain 0) (S.chain 1) with hFs
  set P := prodSC (W :: Fs) with hP
  have hS := SC_pos
  have hD0 := DEN_pos
  have hWb : (((B.getD 0 (0, 0)).2 : ℝ) - (B.getD 0 (0, 0)).1) / DEN ≤ (W : ℝ) / SC := by
    have h1 := SieveOmegaB.div_le_cdiv (SC * ((B.getD 0 (0, 0)).2 - (B.getD 0 (0, 0)).1).toNat) DEN
      (by norm_num [DEN])
    have e : ((((B.getD 0 (0, 0)).2 - (B.getD 0 (0, 0)).1).toNat : ℕ) : ℝ) =
        ((B.getD 0 (0, 0)).2 : ℝ) - (B.getD 0 (0, 0)).1 := by
      have h' : ((((B.getD 0 (0, 0)).2 - (B.getD 0 (0, 0)).1).toNat : ℕ) : ℝ) =
          (((B.getD 0 (0, 0)).2 - (B.getD 0 (0, 0)).1 : ℤ) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (by omega)
      rw [h']
      push_cast
      ring
    rw [Nat.cast_mul, e] at h1
    rw [le_div_iff₀ hS]
    calc (((B.getD 0 (0, 0)).2 : ℝ) - (B.getD 0 (0, 0)).1) / DEN * SC =
        SC * (((B.getD 0 (0, 0)).2 : ℝ) - (B.getD 0 (0, 0)).1) / DEN := by ring
      _ ≤ W := h1
  have hfit' : ∀ L ∈ items, L.c.length ≤ B.length := fun L hL => (hD.fit L hL).trans hlen.ge
  have key : ∃ X : ℝ, 0 ≤ X ∧ X ≤ (Fs.map fun f : ℕ => (f : ℝ) / SC).prod ∧
      OK (21 / 40) ρ 1 (fun x y => ((⟨k, 2, s, conds⟩ : Node).count x y : ℝ))
        (Ωc * Ωg * ((((B.getD 0 (0, 0)).2 : ℝ) - (B.getD 0 (0, 0)).1) / DEN) * X) := by
    rcases hct : (if chain then chainTwo E Γ B items k (s g.rev) (s g) (S.chain 0) (S.chain 1) else none) with
      _ | ⟨D₁, D₂⟩
    · -- each prime's factor
      have hFs' : Fs = (List.range k).map (twoFactor items B E (s g.rev) (s g)) := by
        rw [hFs, twoParts, hct]
      have hfac : ∀ j : Fin k, (if j ∈ ({s g.rev, s g} : Finset (Fin k)) then (DEN : ℝ) / loF items B E j -
          DEN / hiF items B E j else trB (loF items B E j) (hiF items B E j)) ≤
            (twoFactor items B E (s g.rev) (s g) j : ℝ) / SC := by
        intro j
        unfold twoFactor
        by_cases hj : j ∈ ({s g.rev, s g} : Finset (Fin k))
        · have hj' : (j : ℕ) = s g.rev ∨ (j : ℕ) = s g := by
            simp only [mem_insert, mem_singleton] at hj
            rcases hj with rfl | rfl <;> simp
          rw [ite_eq_left hj, ite_eq_left hj']
          exact inv_le_invF (hlo j) (hlohi j)
        · have hj' : ¬((j : ℕ) = s g.rev ∨ (j : ℕ) = s g) := fun h' => hj (by
            simp only [mem_insert, mem_singleton]
            rcases h' with h' | h'
            · exact Or.inl (Fin.ext h')
            · exact Or.inr (Fin.ext h'))
          rw [ite_eq_right hj, ite_eq_right hj']
          exact trB_le_trF (hlo j) (hlohi j)
      have hfac0 : ∀ j : Fin k, 0 ≤ (if j ∈ ({s g.rev, s g} : Finset (Fin k)) then (DEN : ℝ) / loF items B E j -
          DEN / hiF items B E j else trB (loF items B E j) (hiF items B E j)) := by
        intro j
        have h1' : (0 : ℝ) < loF items B E j := by exact_mod_cast hlo j
        have h2' : (loF items B E j : ℝ) ≤ hiF items B E j := by exact_mod_cast hlohi j
        split_ifs
        · have := div_le_div_of_nonneg_left hD0.le h1' h2'
          linarith
        · unfold trB
          have h3 : (0 : ℝ) ≤ (hiF items B E j : ℝ) - loF items B E j := by linarith
          have h4 : (0 : ℝ) ≤ (hiF items B E j : ℝ) + loF items B E j := by linarith
          have h5 : (0 : ℝ) < 2 * (loF items B E j : ℝ) * hiF items B E j :=
            mul_pos (mul_pos two_pos h1') (by linarith)
          exact div_nonneg (mul_nonneg h3 h4) h5.le
      refine ⟨_, prod_nonneg fun j _ => hfac0 j, ?_, h.OK_of_drop2 hD.itemsOK hE hinv hfit' hB0 hsg' hA0 hAg' hAc'
        hlo hlohi hNU hlo0 hlohi0 ha1 ha2 hn0 hΩc0 hΩg0 hωc hωg (θ := 21 / 40) hρ hρ20⟩
      refine le_trans (Finset.prod_le_prod₀ (fun j _ => hfac0 j) fun j _ => hfac j) (le_of_eq ?_)
      rw [hFs', List.map_map, list_prod_map_range]
      exact Fin.prod_univ_eq_prod_range (fun j => (twoFactor items B E (s g.rev) (s g) j : ℝ) / SC) k
    · -- the chain bounds
      have hFs' : Fs = [D₁, D₂] := by rw [hFs, twoParts, hct]
      have hct' : chainTwo E Γ B items k (s g.rev) (s g) (S.chain 0) (S.chain 1) = some (D₁, D₂) := by
        cases chain
        · simp at hct
        · simpa using hct
      obtain ⟨hnd, hcov, hc1, hc2, e₁, e₂, he1, he2, hP1, hP2⟩ := chainTwo_sound hct'
      refine ⟨(D₁ : ℝ) / SC * ((D₂ : ℝ) / SC), by positivity, by rw [hFs']; simp, ?_⟩
      exact h.OK_of_drop2C hD.itemsOK hE hinv hfit' hB0 hsg' hA0 hAg' hAc' hlo hlohi hNU hlo0 hlohi0 ha1 ha2 hn0
        hΩc0 hΩg0 hωc hωg hnd hcov hc1 hc2 he1 he2 (by positivity) (by positivity) hP1 hP2 (θ := 21 / 40) hρ hρ20
  obtain ⟨X, hX0, hXP, hdrop⟩ := key
  refine OK_mono ?_ hdrop
  have hprod : (((B.getD 0 (0, 0)).2 : ℝ) - (B.getD 0 (0, 0)).1) / DEN * X ≤ (P : ℝ) / SC := by
    have h2 := prod_le_prodSC (W :: Fs)
    rw [List.map_cons, List.prod_cons] at h2
    calc _ ≤ (W : ℝ) / SC * (Fs.map fun f : ℕ => (f : ℝ) / SC).prod := mul_le_mul hWb hXP hX0 (by positivity)
      _ ≤ _ := h2
  have hc := SieveOmegaB.div_le_cdiv (omUpK (Nc.minD B E (actsOf Γ acts)).toNat hc.toNat
      (Nc.maxD B E (actsOf Γ acts)).toNat lc.toNat *
    omUpK (max 0 ((B.getD 0 (0, 0)).1 - ∑ a ∈ J, hiF items B E a)).toNat hg'.toNat
      (max 0 ((B.getD 0 (0, 0)).2 - ∑ a ∈ J, loF items B E a)).toNat lg.toNat * P) (SieveCert.K * SieveCert.K)
    (by norm_num [SieveCert.K])
  push_cast at hc
  calc Ωc * Ωg * ((((B.getD 0 (0, 0)).2 : ℝ) - (B.getD 0 (0, 0)).1) / DEN) * X
      = Ωc * Ωg * ((((B.getD 0 (0, 0)).2 : ℝ) - (B.getD 0 (0, 0)).1) / DEN * X) := by ring
    _ ≤ Ωc * Ωg * ((P : ℝ) / SC) := mul_le_mul_of_nonneg_left hprod (mul_nonneg hΩc0 hΩg0)
    _ = _ / SC := by rw [hΩc, hΩg]; ring
    _ ≤ _ := div_le_div_of_nonneg_right hc hS.le

/-- The analytic hypotheses of the checker: Li's lemmas, and the exponents `c` (of the primes' lower end) and `ρ` (of
the comparison interval). -/
structure Hyps (ρ c : ℝ) : Prop where
  hc : 0 < c
  hc1 : c < 1 / 20
  hρ : 0 < ρ
  hρc : 12 * ρ < c
  li31 : ShortSieveLi.LiLemma31 (21 / 40) (1 / 10) ρ
  li32 : ShortSieveLi.LiLemma32 (21 / 40) (1 / 10) ρ
  li41 : ShortSieveLi.LiLemma41 (21 / 40) (1 / 10) ρ

/-- The decomposition of a node with two rough items, in the checker. -/
theorem run_dec_two (E : ℤ) (acts labels : List ℕ) (kind : ℕ) (t : Cert) {S : Shp} (hS : ∀ k, S ≠ .std k)
    (Γ : List Con) (B : Box) (b : Bool) :
    run E (.dec acts labels kind t) S Γ B b =
      if S.m = 2 ∧ actsOK Γ acts B.length = true ∧
          typeICheck S.items (S.k + 1) E B (actsOf Γ acts) labels kind = true then
        run E t (.last S) (geL (S.items.getD (S.k + 1) LF.zero) B.length ::
            (Γ ++ [ordL (S.items.getD (S.sN 1) LF.zero) B.length]))
          (B ++ [(NU0, (S.items.getD (S.sN 1) LF.zero).maxB B E)]) (!b)
      else none := by
  cases S with
  | std k => exact absurd rfl (hS k)
  | rev k => rfl
  | last S => rfl
  | swap S => rfl

/-- **The checker is sound.** If the checker gives the loss `L` for a node of shape `S`, sound with the constraints `Γ`
and the box `B`, whose conditions keep the invariants, then the node is `OK` for its sign with loss `L/SC`. -/
theorem run_sound {ρ c : ℝ} (H : Hyps ρ c) {E : ℤ} (hE : 0 < E) (t : Cert) :
    ∀ (S : Shp) {k m : ℕ} {s : Fin m → Fin k} {A : Rows k m} {items : List LF} {n : ℕ},
      Desc S k m s A items n → ∀ (conds : List (Cond k m)) (Γ : List Con) (B : Box) (b : Bool) (L : ℕ),
      Sound ⟨k, m, s, conds⟩ A E Γ B → Inv ⟨k, m, s, conds⟩ → CondsOK conds → B.length = n →
      fits Γ n = true → run E t S Γ B b = some L →
      OK (21 / 40) ρ (if b then 1 else -1) (fun x y => ((⟨k, m, s, conds⟩ : Node).count x y : ℝ)) (L / SC) := by
  have hθρ : (21 / 40 : ℝ) ≤ 1 - ρ := by have := H.hρc; have := H.hc1; linarith
  have hσ : ∀ b : Bool, |(if b then (1 : ℝ) else -1)| ≤ 1 := fun b => by cases b <;> simp
  have hneg : ∀ b : Bool, (if !b then (1 : ℝ) else -1) = -(if b then 1 else -1) := fun b => by cases b <;> simp
  induction t with
  | out =>
    intro S k m s A items n hD conds Γ B b L h hinv hcond hlen hf hrun
    simp only [run] at hrun
    split_ifs at hrun with hout
    obtain rfl := (Option.some.inj hrun).symm
    simpa using h.OK_of_out hE hout H.hρ hθρ
  | outC i =>
    intro S k m s A items n hD conds Γ B b L h hinv hcond hlen hf hrun
    simp only [run] at hrun
    split_ifs at hrun with hcheck
    obtain rfl := (Option.some.inj hrun).symm
    have hC : Γ.getD i ⟨LF.zero, false⟩ ∈ Γ := by
      rw [List.getD_eq_getElem _ _ hcheck.1]; exact List.getElem_mem _
    simpa using h.OK_of_noPt hE (noPt_of_fails hC hcheck.2) H.hρ hθρ
  | outE j =>
    intro S k m s A items n hD conds Γ B b L h hinv hcond hlen hf hrun
    simp only [run] at hrun
    split_ifs at hrun with hcheck
    obtain rfl := (Option.some.inj hrun).symm
    simpa using h.OK_of_noPt hE (noPt_of_empty hcheck.1 hcheck.2) H.hρ hθρ
  | comb i j c t ih =>
    intro S k m s A items n hD conds Γ B b L h hinv hcond hlen hf hrun
    simp only [run] at hrun
    split_ifs at hrun with hcheck
    have hCi : Γ.getD i ⟨LF.zero, false⟩ ∈ Γ := by
      rw [List.getD_eq_getElem _ _ hcheck.1]; exact List.getElem_mem _
    have hCj : Γ.getD j ⟨LF.zero, false⟩ ∈ Γ := by
      rw [List.getD_eq_getElem _ _ hcheck.2]; exact List.getElem_mem _
    have hf' : fits (combCon (Γ.getD i ⟨LF.zero, false⟩) (Γ.getD j ⟨LF.zero, false⟩) c :: Γ) n = true := by
      rw [fits_iff] at hf ⊢
      intro C hC
      rcases List.mem_cons.1 hC with rfl | hC
      · simp only [combCon, LF.add, LF.smul, length_addC, List.length_map]
        exact max_le (hf _ hCi) (hf _ hCj)
      · exact hf C hC
    exact ih S hD conds _ B b L (h.comb hCi hCj c) hinv hcond hlen hf' hrun
  | tighten t ih =>
    intro S k m s A items n hD conds Γ B b L h hinv hcond hlen hf hrun
    simp only [run] at hrun
    exact ih S hD conds Γ _ b L (h.tighten (hlen ▸ hf) Γ fun c hc => hc) hinv hcond
      ((length_tightenList E Γ B).trans hlen) hf hrun
  | up j lower i v t ih =>
    intro S k m s A items n hD conds Γ B b L h hinv hcond hlen hf hrun
    simp only [run] at hrun
    split_ifs at hrun with hcheck
    have hC : Γ.getD i ⟨LF.zero, false⟩ ∈ Γ := by
      rw [List.getD_eq_getElem _ _ hcheck.1]; exact List.getElem_mem _
    have hCl : (Γ.getD i ⟨LF.zero, false⟩).L.c.length ≤ B.length := hlen ▸ fits_iff.1 hf _ hC
    exact ih S hD conds Γ _ b L (h.up hC hCl hcheck.2) hinv hcond ((length_cutAt B j lower v).trans hlen) hf hrun
  | split C u w t₁ t₂ ih₁ ih₂ =>
    intro S k m s A items n hD conds Γ B b L h hinv hcond hlen hf hrun
    simp only [run] at hrun
    split_ifs at hrun with hcheck
    obtain ⟨hfC, hu, hw, hne⟩ := hcheck
    obtain ⟨hk, hm, hn, -, -, -⟩ := hD.data
    rw [hk, hm] at hu hw
    rw [hn] at hfC
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨L₁, h₁, h₂⟩ := hrun
    rw [Option.map_eq_some_iff] at h₂
    obtain ⟨L₂, h₂, rfl⟩ := h₂
    have huw : wt A C.L (decanon u hu) ≠ wt A C.L (decanon w hw) := by
      rw [hD.wt_eq, hD.wt_eq, canon_decanon, canon_decanon]
      exact_mod_cast hne
    obtain ⟨hc₁, hc₂⟩ := condsOK_cons hcond huw
    obtain ⟨hf₁, hf₂⟩ := fits_cons hf hfC
    have o₁ := ih₁ S hD _ (C :: Γ) B b L₁ (h.split C) (hinv.cons _) hc₁ hlen hf₁ h₁
    have o₂ := ih₂ S hD _ (C.neg :: Γ) B b L₂ (h.split_neg C) (hinv.cons _) hc₂ hlen hf₂ h₂
    have e : ((L₁ + L₂ : ℕ) : ℝ) / SC = (L₁ : ℝ) / SC + (L₂ : ℝ) / SC := by push_cast; ring
    rw [e]
    refine OK_congr (Filter.Eventually.of_forall fun x y _ _ => ?_) hθρ (OK_add o₁ o₂)
    rw [count_split ⟨k, m, s, conds⟩ (toCond A C) x y]
    push_cast
    rfl
  | cut j p u w t₁ t₂ ih₁ ih₂ =>
    intro S k m s A items n hD conds Γ B b L h hinv hcond hlen hf hrun
    simp only [run] at hrun
    split_ifs at hrun with hcheck
    obtain ⟨hu, hw, hne⟩ := hcheck
    obtain ⟨hk, hm, -, -, -, -⟩ := hD.data
    rw [hk, hm] at hu hw
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨L₁, h₁, h₂⟩ := hrun
    rw [Option.map_eq_some_iff] at h₂
    obtain ⟨L₂, h₂, rfl⟩ := h₂
    have huw : wt A (ltCon j p).L (decanon u hu) ≠ wt A (ltCon j p).L (decanon w hw) := by
      rw [hD.wt_eq, hD.wt_eq, canon_decanon, canon_decanon]
      exact_mod_cast hne
    obtain ⟨hc₁, hc₂⟩ := condsOK_cons hcond huw
    have o₁ := ih₁ S hD _ Γ _ b L₁ (h.cut_lt j p) (hinv.cons _) hc₁ (by rw [List.length_modify, hlen]) hf h₁
    have o₂ := ih₂ S hD _ Γ _ b L₂ (h.cut_ge j p) (hinv.cons _) hc₂ (by rw [List.length_modify, hlen]) hf h₂
    have e : ((L₁ + L₂ : ℕ) : ℝ) / SC = (L₁ : ℝ) / SC + (L₂ : ℝ) / SC := by push_cast; ring
    rw [e]
    refine OK_congr (Filter.Eventually.of_forall fun x y _ _ => ?_) hθρ (OK_add o₁ o₂)
    rw [count_split ⟨k, m, s, conds⟩ (toCond A (ltCon j p)) x y]
    push_cast
    rfl
  | tii acts labels ng =>
    intro S k m s A items n hD conds Γ B b L h hinv hcond hlen hf hrun
    simp only [run] at hrun
    split_ifs at hrun with hcheck
    obtain rfl := (Option.some.inj hrun).symm
    obtain ⟨hacts, hlab, hlt, htii⟩ := hcheck
    obtain ⟨hk, hm, -, hit, -, -⟩ := hD.data
    obtain ⟨hk0, hm0⟩ := hD.k_pos
    rw [hk, hm] at hlab hlt
    rw [hit] at htii
    obtain ⟨ha1, ha2⟩ := acts_of_OK hacts
    have hlt' : ∀ t : Fin k ⊕ Fin m, labels.getD (canon t) 0 < ng := fun t => by
      simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hlt
      exact hlt _ (canon_lt t)
    have hAsym := Sound.asym_of_tii (N := ⟨k, m, s, conds⟩) hk0 hm0 hE h hD.itemsOK hlab hlt'
      (by norm_num [tiiP]) (by norm_num [tiiK]) (θ := 21 / 40) (κ := 1 / 2 ^ 20) (by norm_num [tiiP, DEN])
      (by norm_num [tiiK, DEN]) (actsOf Γ acts) ha1 htii (fun L hL => (hD.fit L hL).trans hlen.ge) ha2 H.hc
      (by linarith [H.hc1]) (by norm_num) H.hρ H.hρc (by linarith [H.hρc, H.hc1]) hcond (hinv.big H.hc1)
    simpa using OK_of_asym (hσ b) hAsym
  | g2 acts labels =>
    intro S k m s A items n hD conds Γ B b L h hinv hcond hlen hf hrun
    simp only [run] at hrun
    split_ifs at hrun with hcheck
    obtain rfl := (Option.some.inj hrun).symm
    obtain ⟨hacts, hlab, hlt, hg2⟩ := hcheck
    obtain ⟨hk, hm, -, hit, -, -⟩ := hD.data
    obtain ⟨hk0, hm0⟩ := hD.k_pos
    rw [hk, hm] at hlab hlt
    rw [hit] at hg2
    obtain ⟨ha1, ha2⟩ := acts_of_OK hacts
    have hlt' : ∀ t : Fin k ⊕ Fin m, labels.getD (canon t) 0 < 3 := fun t => by
      simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hlt
      exact hlt _ (canon_lt t)
    have hAsym := Sound.asym_of_g2 (N := ⟨k, m, s, conds⟩) hk0 hm0 hE h hD.itemsOK hlab hlt'
      (θ := 21 / 40) (γ := 1 / 10) (by norm_num [g2D1, DEN]) (by norm_num [g2D2, DEN]) (actsOf Γ acts) ha1 hg2
      (fun L hL => (hD.fit L hL).trans hlen.ge) ha2 H.hc (by linarith [H.hc1]) H.hρ H.hρc H.li41 hcond
      (hinv.big H.hc1)
    simpa using OK_of_asym (hσ b) hAsym
  | dec acts labels kind t ih =>
    intro S k m s A items n hD conds Γ B b L h hinv hcond hlen hf hrun
    by_cases hS : ∃ k', S = .std k'
    · obtain ⟨k', rfl⟩ := hS
      cases hD
      simp only [run] at hrun
      split_ifs at hrun with hcheck
      obtain ⟨hacts, htI⟩ := hcheck
      obtain ⟨ha1, ha2⟩ := acts_of_OK hacts
      have hinv' : StdInv k' conds := hinv.std
      have hG := ih (.std (k' + 1)) (Desc.std (k' + 1)) (stdChild k' conds) _ _ (!b) L
        (h.std_child hlen (hlen ▸ hf)) hinv'.child.inv hcond.child (by simp [hlen]) (fits_std_child hf) hrun
      rw [hneg] at hG
      exact h.OK_of_dec hE hinv' hcond hlen.ge ha1 ha2 htI H.hc H.hc1 H.hρ H.hρc (hσ b) H.li31 H.li32 hG
    · push Not at hS
      rw [run_dec_two E acts labels kind t hS] at hrun
      split_ifs at hrun with hcheck
      obtain ⟨hm2, hacts, htI⟩ := hcheck
      obtain ⟨hk, hm, hn, hit, hs, -⟩ := hD.data
      rw [hm] at hm2
      subst hm2
      obtain ⟨hk0, -⟩ := hD.k_pos
      rw [hk, hit] at htI
      obtain ⟨ha1, ha2⟩ := acts_of_OK hacts
      have e1 : S.items.getD (S.k + 1) LF.zero = items.getD (k + 1) LF.zero := by rw [hit, hk]
      have e2 : S.items.getD (S.sN 1) LF.zero = items.getD (s (Fin.last 1)) LF.zero := by
        rw [hit, show S.sN 1 = S.sN ((1 : Fin 2) : ℕ) from rfl, hs 1]
        rfl
      rw [e1, e2] at hrun
      have hfit : ∀ L ∈ items, L.c.length ≤ B.length := fun L hL => (hD.fit L hL).trans hlen.ge
      have hSnd := h.last_child hD.itemsOK (hlen ▸ hf) hfit
      rw [hlen] at hSnd hrun
      have hG := ih (.last S) (Desc.last hD) _ _ _ (!b) L hSnd hinv.last hcond.last (by simp [hlen])
        (fits_last_child hf (length_getD_le hD.fit _) (length_getD_le hD.fit _)) hrun
      rw [hneg] at hG
      exact h.OK_of_decL (m := 1) hD.itemsOK hE hk0 hinv hcond hfit ha1 ha2 htI H.hc H.hc1 H.hρ H.hρc (hσ b)
        H.li31 H.li32 hG
  | rev acts labels kind t ih =>
    intro S k m s A items n hD conds Γ B b L h hinv hcond hlen hf hrun
    cases S with
    | std k' =>
      cases k' with
      | zero => simp [run] at hrun
      | succ k' =>
        cases hD
        simp only [run] at hrun
        split_ifs at hrun with hcheck
        obtain ⟨hacts, htI⟩ := hcheck
        obtain ⟨ha1, ha2⟩ := acts_of_OK hacts
        have hinv' : StdInv (k' + 1) conds := hinv.std
        have hG := ih (.rev k') (Desc.rev k') (revConds (k' + 1) conds) _ _ (!b) L
          (h.rev_child hlen (hlen ▸ hf)) hinv'.rev.inv hcond.rev (by simp [hlen]) (fits_rev_child hf) hrun
        rw [hneg] at hG
        exact h.OK_of_rev hE hinv' hcond hlen.ge ha1 ha2 htI H.hc H.hc1 H.hρ H.hρc (hσ b) H.li31 H.li32 hG
    | rev _ => simp [run] at hrun
    | last _ => simp [run] at hrun
    | swap _ => simp [run] at hrun
  | swap t ih =>
    intro S k m s A items n hD conds Γ B b L h hinv hcond hlen hf hrun
    simp only [run] at hrun
    split_ifs at hrun with hm2
    obtain ⟨-, hm, -, -, -, -⟩ := hD.data
    rw [hm] at hm2
    subst hm2
    have o := ih (.swap S) (Desc.swap hD) (conds.map Cond.swap2) Γ B b L h.swap hinv.swap hcond.swap hlen hf hrun
    refine OK_congr (Filter.Eventually.of_forall fun x y _ _ => ?_) hθρ o
    rw [count_swap]
  | drop acts c =>
    intro S k m s A items n hD conds Γ B b L h hinv hcond hlen hf hrun
    cases b
    · cases S <;> simp [run] at hrun
    · by_cases hS : ∃ k', S = .std k'
      · obtain ⟨k', rfl⟩ := hS
        cases hD
        simp only [run] at hrun
        simpa using dropStd_sound H.hρ (by linarith [H.hρc, H.hc1]) hE h hinv.std hrun
      · push Not at hS
        have hrun' : (if S.m = 2 then dropTwo E S Γ B acts c else none) = some L := by
          cases S with
          | std k' => exact absurd rfl (hS k')
          | rev _ => exact hrun
          | last _ => exact hrun
          | swap _ => exact hrun
        split_ifs at hrun' with hm2
        obtain ⟨-, hm, -, -, -, -⟩ := hD.data
        rw [hm] at hm2
        subst hm2
        simpa using dropTwo_sound H.hρ (by linarith [H.hρc, H.hc1]) hE hD h hinv hlen hrun'

/-! ### The root cells and the primes -/

theorem fits_cellCons (k : ℕ) (r : Bool) : fits (cellCons k r) 2 = true := by
  rw [fits_iff]
  intro C hC
  simp only [cellCons, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl
  · simp
  · simp [geCon]
  · unfold levelCon; split_ifs <;> simp
  · cases r <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> unfold regionCon <;> split_ifs <;> simp [Con.neg]

/-- **A root cell from the checker.** If the checker gives the loss `L` for the root cell `(k, j)` of region `r`
(`2 ≤ k`, `2 ≤ j`), the cell is `OK` for `σ = 1` with loss `L/SC`. -/
theorem cell_OK {ρ c : ℝ} (H : Hyps ρ c) {E : ℤ} (hE : 0 < E) (t : Cert) {k j : ℕ} (r : Bool) (hk : 2 ≤ k)
    (hj : 2 ≤ j) {L : ℕ} (hrun : run E t (.std 1) (cellCons k r) (cellBox k j) true = some L) :
    OK (21 / 40) ρ 1 (fun x y => ((ShortSieveThree.cell k j r).count x y : ℝ)) (L / SC) := by
  have := run_sound H hE t (.std 1) (Desc.std 1) (ShortSieveThree.cellConds k j r) (cellCons k r) (cellBox k j)
    true L
    (Sound.cell r E) (StdInv.cell r hj hk).inv (CondsOK.cell k j r) rfl (fits_cellCons k r) hrun
  exact this

/-- **Primes in short intervals from the certificates.** At `θ = 21/40`, given Li's Lemmas 3.1, 3.2 and 4.1 and a
certificate for every root cell that the checker passes with the loss `L r c` (units `1/SC`):
`π(x) − π(x − y) ≥ (1 − Σ L/SC − ε) y/log x` for `x^{21/40} ≤ y ≤ x^{1−ρ}`. -/
theorem primes_of_certs {ρ c : ℝ} (H : Hyps ρ c) {E : ℤ} (hE : 0 < E) (cert : Bool → ℕ × ℕ → Cert)
    (L : Bool → ℕ × ℕ → ℕ)
    (hrun : ∀ r, ∀ c ∈ ShortSieveThree.cells r,
      run E (cert r c) (.std 1) (cellCons c.1 r) (cellBox c.1 c.2) true = some (L r c)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ^ (21 / 40 : ℝ) ≤ y → y ≤ x ^ (1 - ρ) →
      (1 - (∑ c ∈ ShortSieveThree.cells true, (L true c : ℝ) / SC +
        ∑ c ∈ ShortSieveThree.cells false, (L false c : ℝ) / SC) - ε) * y / Real.log x ≤
        ((Ioc ⌊x - y⌋₊ ⌊x⌋₊).filter Nat.Prime).card := by
  refine ShortSieveThree.primes_of_cells H.li31 H.hρ (by linarith [H.hρc, H.hc1]) (fun r c => (L r c : ℝ) / SC)
    fun r c hc => ?_
  have hk : 2 ≤ c.1 ∧ 2 ≤ c.2 := by
    cases r <;> simp only [ShortSieveThree.cells, Bool.false_eq_true, ↓reduceIte, mem_product, mem_Icc] at hc <;>
      omega
  exact cell_OK H hE (cert r c) r hk.1 hk.2 (hrun r c hc)

end ShortSieveCert

#print axioms ShortSieveCert.run_sound
#print axioms ShortSieveCert.primes_of_certs
