import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.List.Basic
import Mathlib.Computability.Encoding
import Mathlib.Logic.Encodable.Pi

-- Rewrite theorems in Lean4 and Mathlib avoiding the axiom of choice.
set_option linter.unusedDecidableInType false

open Std in
local instance Lx1 {α : Type*} [LE α] [DecidableLE α] [Max α]
    [LawfulOrderLeftLeaningMax α] : MaxEqOr α where
  max_eq_or a b := by
    suffices min_eq : max a b = if b ≤ a then a else b by
      rw [min_eq]
      split <;> simp
    split <;> simp [*, LawfulOrderLeftLeaningMax.max_eq_left,
      LawfulOrderLeftLeaningMax.max_eq_right]

namespace List
variable {α : Type u}

theorem max?_eq_some_iff'' {a : α} [Max α] [LE α] [DecidableLE α]
    {xs : List α} [Std.IsLinearOrder (α)] [Std.LawfulOrderMax α] :
    xs.max? = some a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → b ≤ a := by
  constructor
  · intro h; exact ⟨max?_mem h, (max?_le_iff h).1 (Std.le_refl _)⟩
  · intro ⟨h₁, h₂⟩
    cases xs with
    | nil => simp at h₁
    | cons x xs =>
      rw [List.max?]
      exact congrArg some <| Std.le_antisymm
        (h₂ _ (max?_mem (xs := x :: xs) rfl))
        ((max?_le_iff (xs := x :: xs) rfl).1 (Std.le_refl _) _ h₁)

theorem eq_nil_iff_forall_not_mem' {l : List α} : l = [] ↔ ∀ a, a ∉ l := by
  cases l <;> simp only [List.not_mem_nil, not_false_eq_true, implies_true, reduceCtorEq,
    List.mem_cons, forall_eq_or_imp, imp_false, false_and]

open List in
theorem mem_dedup' [DecidableEq α] {a : α} {l : List α} : a ∈ dedup l ↔ a ∈ l := by
  have := not_congr (@forall_mem_pwFilter α (· ≠ ·) _ ?_ a l)
  · simpa only [dedup, forall_mem_ne, Decidable.not_not] using this
  · intro x y z xz
    exact Decidable.not_and_iff_not_or_not.1 <| mt (fun h ↦ h.1.trans h.2) xz
end List

namespace Set
variable {α β : Type*} {s t u : Set α}

theorem diff_subset' : s \ t ⊆ s := by
  rw [Set.subset_def]; intro x h; rw [Set.mem_diff] at h; exact h.1

theorem insert_subset_iff' {a : α} : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t := by
  simp only [subset_def, mem_insert_iff, forall_eq_or_imp]

theorem insert_comm' (a b : α) (s : Set α) : insert a (insert b s) = insert b (insert a s) := by
  repeat rw [Set.insert_eq]
  conv =>
    lhs; rw [←Set.union_assoc]
    conv => lhs; rw [Set.union_comm]
    rw [Set.union_assoc]

theorem union_insert' {a} : s ∪ insert a t = insert a (s ∪ t) := by
  ext x; simp only [mem_union, mem_insert_iff]; conv =>
    lhs; rw [←or_assoc]
    conv => lhs; rw [or_comm]
    rw [or_assoc]

theorem diff_diff' : (s \ t) \ u = s \ (t ∪ u) := by
  ext x; simp only [mem_diff, mem_union, not_or]; exact and_assoc

theorem diff_subset_iff' [DecidablePred t] : s \ t ⊆ u ↔ s ⊆ t ∪ u := by
  simp only [subset_def, mem_diff, and_imp, mem_union]
  constructor
  · intro h x h'
    rcases (Decidable.em (t x)) with h1 | h2
    · left; exact h1
    · right; exact h x h' h2
  · intro h x h1 h2
    exact Or.resolve_left (h x h1) h2

theorem diff_diff_comm' : (s \ t) \ u = (s \ u) \ t := by
  ext x; constructor <;> simp only [mem_diff, and_imp] <;> intro h1 h2 h3 <;> exact ⟨⟨h1, h3⟩, h2⟩

theorem diff_singleton_eq_self' {a : α} (h : a ∉ s) : s \ {a} = s := by
  ext x; constructor <;> simp only [mem_diff, mem_singleton_iff, and_imp]
  · intro h' _; exact h'
  · intro h'; refine ⟨h', ?_⟩; by_contra hx
    rw [hx] at h'; exact h h'

theorem diff_union_self' [DecidablePred t] : s \ t ∪ t = s ∪ t := by
  ext x; constructor <;> simp only [Set.mem_union, Set.mem_diff]
  · intro h'
    rcases h' with ⟨h1, _⟩ | h2
    · left; exact h1
    · right; exact h2
  · intro h'
    rcases h' with h1 | h2
    · rcases Decidable.em (t x) with h3 | h4
      · right; exact h3
      · left; exact ⟨h1, h4⟩
    · right; exact h2

theorem union_diff_distrib' : (s ∪ t) \ u = s \ u ∪ t \ u := by
  ext x; simp only [mem_diff, mem_union]; exact or_and_right

theorem diff_subset_diff_left' {s₁ s₂ t : Set α} (h : s₁ ⊆ s₂) : s₁ \ t ⊆ s₂ \ t := by
  rw [Set.subset_def] at h ⊢; simp only [mem_diff, and_imp] at h ⊢
  intro x h1 h2; exact ⟨h x h1, h2⟩

theorem subset_iUnion_of_subset' {ι : Type*} {t : ι → Set α} (i : ι) (h : s ⊆ t i) :
    s ⊆ ⋃ i, t i := by
  simp only [Set.subset_def, mem_iUnion] at h ⊢
  intro x h'; use i; exact h x h'

theorem iUnion_subset_iff' {ι : Type*} {s : ι → Set α} : ⋃ i, s i ⊆ t ↔ ∀ i, s i ⊆ t := by
  simp only [subset_def, mem_iUnion, forall_exists_index]
  constructor <;> intro h i x h' <;> exact h x i h'

theorem image_empty' (f : α → β) : f '' ∅ = ∅ := by
  ext x; constructor <;>
  simp only [Set.mem_empty_iff_false, Set.mem_image, false_and, exists_false, imp_self]

theorem image_singleton' {f : α → β} {a : α} : f '' {a} = {f a} := by
  ext x; constructor <;> rw [Set.mem_singleton_iff, Set.mem_image] <;>
  simp only [Set.mem_singleton_iff, exists_eq_left] <;> intro h <;> symm <;> exact h

theorem image_union' (f : α → β) (s t : Set α) : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor <;>
  simp only [Set.mem_image, Set.mem_union, forall_exists_index, and_imp]
  · intro x h1 h2
    rcases h1 with h3 | h4
    · left; use x
    · right; use x
  · intro h
    rcases h with ⟨x, h1, h2⟩ | ⟨x, h1, h2⟩
    · use x; exact ⟨.inl h1, h2⟩
    · use x; exact ⟨.inr h1, h2⟩

theorem image_insert_eq' {f : α → β} {a : α} :
    f '' insert a s = insert (f a) (f '' s) := by
  ext x; simp only [mem_image, mem_insert_iff, exists_eq_or_imp]
  constructor
  · intro h
    rcases h with h1 | h2
    · left; symm; exact h1
    · right; exact h2
  · intro h
    rcases h with h1 | h2
    · left; symm; exact h1
    · right; exact h2

end Set

namespace Nat
theorem add_eq_left' {a b : Nat} : a + b = a ↔ b = 0 := by
  constructor
  · intro h
    induction a with
    | zero => rwa [Nat.zero_add] at h
    | succ n ha =>
      conv at h =>
        lhs; rw [Nat.add_assoc]
        conv => rhs; rw [Nat.add_comm]
        rw [←Nat.add_assoc]
      exact ha (Nat.add_right_cancel h)
  · intro h; rw [h]; apply Nat.add_zero

lemma bodd_add_div2' : ∀ n, (bodd n).toNat + 2 * div2 n = n
  | 0 => rfl
  | succ n => by
    simp only [bodd_succ, div2_succ, Nat.mul_comm]
    refine Eq.trans ?_ (congr_arg succ (bodd_add_div2' n))
    cases bodd n
    · simp only [Bool.not_false, Bool.toNat_true, succ_eq_add_one,
        cond_false, Bool.toNat_false, zero_add]
      rw [add_comm, mul_comm]
    · simp only [Bool.not_true, Bool.toNat_false, succ_eq_add_one,
        cond_true, zero_add, Bool.toNat_true]
      omega

lemma div2_val' (n) : div2 n = n / 2 := by
  refine Nat.eq_of_mul_eq_mul_left (by decide)
    (Nat.add_left_cancel (Eq.trans ?_ (Nat.mod_add_div n 2).symm))
  rw [mod_two_of_bodd, bodd_add_div2']

private def IsSqrt (n q : ℕ) : Prop :=
  q * q ≤ n ∧ n < (q + 1) * (q + 1)

private lemma AM_GM : {a b : ℕ} → (4 * a * b ≤ (a + b) * (a + b))
  | 0, _ => by rw [Nat.mul_zero, Nat.zero_mul]; exact zero_le _
  | _, 0 => by rw [Nat.mul_zero]; exact zero_le _
  | a + 1, b + 1 => by
    simpa only [Nat.mul_add, Nat.add_mul, show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, Nat.one_mul,
      Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_le_add_iff_left]
      using Nat.add_le_add_right (@AM_GM a b) 4

lemma sqrt.iter_sq_le' (n guess : ℕ) : sqrt.iter n guess * sqrt.iter n guess ≤ n := by
  unfold sqrt.iter
  let next := (guess + n / guess) / 2
  if h : next < guess then
    simpa only [next, dif_pos h] using sqrt.iter_sq_le' n next
  else
    apply Nat.mul_le_of_le_div
    simp only [dite_eq_ite]
    split_ifs with h1 <;> omega

protected theorem lt_of_mul_lt_mul_left' {a b c : Nat} (h : a * b < a * c) : b < c := by
  induction a with
  | zero => simp at h
  | succ n h' =>
    rw [←Nat.sub_pos_iff_lt, ←Nat.mul_sub, ←Nat.ne_zero_iff_zero_lt,
      Nat.mul_ne_zero_iff, Nat.sub_ne_zero_iff_lt] at h
    exact h.2

lemma sqrt.lt_iter_succ_sq' (n guess : ℕ) (hn : n < (guess + 1) * (guess + 1)) :
    n < (sqrt.iter n guess + 1) * (sqrt.iter n guess + 1) := by
  unfold sqrt.iter
  -- m was `next`
  let m := (guess + n / guess) / 2
  dsimp
  split_ifs with h
  · suffices n < (m + 1) * (m + 1) by
      simpa only [dif_pos h] using sqrt.lt_iter_succ_sq' n m this
    refine Nat.lt_of_mul_lt_mul_left' ?_ (a := 4 * (guess * guess))
    apply Nat.lt_of_le_of_lt AM_GM
    rw [show (4 : ℕ) = 2 * 2 from rfl]
    rw [Nat.mul_mul_mul_comm 2, Nat.mul_mul_mul_comm (2 * guess)]
    refine Nat.mul_self_lt_mul_self (?_ : _ < _ * ((_ / 2) + 1))
    rw [← add_div_right _ (by decide), Nat.mul_comm 2, Nat.mul_assoc,
      show guess + n / guess + 2 = (guess + n / guess + 1) + 1 from rfl]
    have aux_lemma {a : ℕ} : a ≤ 2 * ((a + 1) / 2) := by omega
    refine lt_of_lt_of_le ?_ (Nat.mul_le_mul_left _ aux_lemma)
    rw [Nat.add_assoc, Nat.mul_add]
    exact Nat.add_lt_add_left (lt_mul_div_succ _ (lt_of_le_of_lt (Nat.zero_le m) h)) _
  · exact hn

protected theorem pow_le_pow_iff_right' {a n m : Nat} (h : 1 < a) :
    a ^ n ≤ a ^ m ↔ n ≤ m := by
  constructor
  · apply Decidable.by_contra
    intro w
    simp only [Decidable.not_imp_iff_and_not, not_le] at w
    apply Nat.lt_irrefl (a ^ n)
    exact Nat.lt_of_le_of_lt w.1 (Nat.pow_lt_pow_of_lt h w.2)
  · intro w
    cases Nat.eq_or_lt_of_le w
    case inl eq => subst eq; apply Nat.le_refl
    case inr lt => exact Nat.le_of_lt (Nat.pow_lt_pow_of_lt h lt)

private lemma sqrt_isSqrt (n : ℕ) : IsSqrt n (sqrt n) := by
  match n with
  | 0 => simp only [IsSqrt, sqrt, _root_.zero_le, ↓reduceIte, mul_zero,
    Std.le_refl, zero_add, mul_one, zero_lt_one, and_self]
  | 1 => simp only [IsSqrt, sqrt, Std.le_refl, ↓reduceIte, mul_one, true_and]; decide
  | n + 2 =>
    have h : ¬ (n + 2) ≤ 1 := by simp only [reduceLeDiff, not_false_eq_true]
    simp only [IsSqrt, sqrt, h, ite_false]
    refine ⟨sqrt.iter_sq_le' _ _, sqrt.lt_iter_succ_sq' _ _ ?_⟩
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one, ← Nat.add_assoc]
    rw [Nat.lt_add_one_iff, Nat.add_assoc, ← Nat.mul_two]
    refine le_trans (Nat.le_of_eq (div_add_mod' (n + 2) 2).symm) ?_
    rw [show (n + 2) / 2 * 2 + (n + 2) % 2 = n + 2 by omega]
    simp only [shiftLeft_eq, Nat.one_mul]
    refine Nat.le_of_lt (Nat.le_trans lt_log2_self (le_add_right_of_le ?_))
    rw [←Nat.pow_add, Nat.pow_le_pow_iff_right' (by decide)]
    conv =>
      rhs; rw [add_assoc]
      conv => rhs; rw [←add_assoc, add_comm, ←add_assoc, add_comm]
      repeat rw [←add_assoc]
    rw [Nat.add_le_add_iff_right]
    omega

lemma lt_succ_sqrt'' (n : ℕ) : n < succ (sqrt n) * succ (sqrt n) := (sqrt_isSqrt n).right
lemma sqrt_le'' (n : ℕ) : sqrt n * sqrt n ≤ n := (sqrt_isSqrt n).left

lemma sqrt_le_add' (n : ℕ) : n ≤ sqrt n * sqrt n + sqrt n + sqrt n := by
  rw [←succ_mul]; exact le_of_lt_succ (lt_succ_sqrt'' n)

theorem pair_unpair' (n : ℕ) : pair (unpair n).1 (unpair n).2 = n := by
  dsimp only [unpair]; let s := sqrt n
  have sm : s * s + (n - s * s) = n := Nat.add_sub_cancel' (sqrt_le'' _)
  split_ifs with h
  · simp [s, pair, h, sm]
  · have hl : n - s * s - s ≤ s := Nat.sub_le_iff_le_add.2
      (Nat.sub_le_iff_le_add'.2 <| by rw [← Nat.add_assoc]; apply sqrt_le_add')
    simp [s, pair, hl.not_gt, Nat.add_assoc, Nat.add_sub_cancel' (le_of_not_gt h), sm]

lemma le_sqrt'' {m n} : m ≤ sqrt n ↔ m * m ≤ n :=
  ⟨fun h ↦ le_trans (mul_self_le_mul_self h) (sqrt_le'' n),
    fun h ↦ le_of_lt_succ <| Nat.mul_self_lt_mul_self_iff.1 <| lt_of_le_of_lt h (lt_succ_sqrt'' n)⟩
lemma sqrt_lt'' {m n} : sqrt m < n ↔ m < n * n := by simp only [← not_le, le_sqrt'']

lemma sqrt_add_eq'' {a : Nat} (n : ℕ) (h : a ≤ n + n) : sqrt (n * n + a) = n :=
  le_antisymm
    (le_of_lt_succ <| sqrt_lt''.2 <| by
      rw [mul_succ, succ_mul, add_assoc, Nat.add_lt_add_iff_left, add_succ, Nat.lt_succ_iff]
      exact h)
    (le_sqrt''.2 <| Nat.le_add_right ..)

theorem unpair_pair' (a b : ℕ) : unpair (pair a b) = (a, b) := by
  dsimp only [pair]; split_ifs with h
  · show unpair (b * b + a) = (a, b)
    have be : sqrt (b * b + a) = b := sqrt_add_eq'' _ (le_trans (le_of_lt h) (Nat.le_add_left _ _))
    simp only [unpair, be]
    split_ifs with h1
    · congr; omega
    · congr
      · omega
      · omega
  · show unpair (a * a + a + b) = (a, b)
    have ae : sqrt (a * a + (a + b)) = a := by
      rw [sqrt_add_eq'']
      exact Nat.add_le_add_left (le_of_not_gt h) _
    simp only [unpair, Nat.add_assoc, ae]
    split_ifs with h1
    · congr
      · omega
      · omega
    · congr; omega

theorem unpair_right_le' (n : ℕ) : (unpair n).2 ≤ n := by
  simpa only [pair_unpair'] using right_le_pair n.unpair.1 n.unpair.2

end Nat

namespace Encodable
variable {α : Type u} [Encodable α]

instance Sum.encodable' {β} [Encodable β] : Encodable (α ⊕ β) :=
  ⟨encodeSum, decodeSum, fun s => by cases s <;>
  simp [encodeSum, Nat.div2_val', decodeSum, encodek]⟩

open Nat in
def decodeList' : ℕ → Option (List α)
  | 0 => some []
  | succ v =>
    match unpair v, unpair_right_le' v with
    | (v₁, v₂), h =>
      have : v₂ < succ v := lt_succ_of_le h
      (· :: ·) <$> decode (α := α) v₁ <*> decodeList' v₂

theorem decodeList_encodeList_eq_self' (l : List α) : decodeList' (encodeList l) = some l := by
  induction l <;> simp only [encodeList, Nat.succ_eq_add_one, decodeList', Nat.unpair_pair',
    encodek, Option.map_eq_map, Option.map_some, Option.seq_some, *]

instance List.encodable' : Encodable (List α) :=
  ⟨encodeList, decodeList', decodeList_encodeList_eq_self'⟩

instance Sigma.encodable' {γ} [(a : α) → Encodable (γ a)] : Encodable (Sigma γ) :=
  ⟨encodeSigma, decodeSigma, fun ⟨a, b⟩ => by
    simp only [decodeSigma, encodeSigma, Nat.unpair_pair',
      encodek, Option.bind_some, Option.map_some]⟩

instance List.Vector.encodable' [Encodable α] {n} : Encodable (List.Vector α n) :=
  inferInstanceAs <| Encodable (Subtype _)

instance finArrow' [Encodable α] {n} : Encodable (Fin n → α) :=
  ofEquiv _ (Equiv.vectorEquivFin _ _).symm

instance finPi' (n) (π : Fin n → Type*) [∀ i, Encodable (π i)] : Encodable (∀ i, π i) :=
  ofEquiv _ (Equiv.piEquivSubtypeSigma (Fin n) π)

instance Bool.encodable' : Encodable Bool :=
  ofEquiv (Unit ⊕ Unit) Equiv.boolEquivPUnitSumPUnit
end Encodable
