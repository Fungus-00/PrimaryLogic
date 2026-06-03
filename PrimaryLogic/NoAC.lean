import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.List.Basic

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

open List in
theorem List.max?_eq_some_iff'' {α a} [Max α] [LE α] [DecidableLE α]
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

theorem List.eq_nil_iff_forall_not_mem' {α} {l : List α} : l = [] ↔ ∀ a, a ∉ l := by
  cases l <;> simp only [List.not_mem_nil, not_false_eq_true, implies_true, reduceCtorEq,
    List.mem_cons, forall_eq_or_imp, imp_false, false_and]

theorem Nat.add_eq_left' {a b : Nat} : a + b = a ↔ b = 0 := by
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

open List in
theorem List.mem_dedup' {α : Type*} [DecidableEq α] {a : α} {l : List α} : a ∈ dedup l ↔ a ∈ l := by
  have := not_congr (@forall_mem_pwFilter α (· ≠ ·) _ ?_ a l)
  · simpa only [dedup, forall_mem_ne, Decidable.not_not] using this
  · intro x y z xz
    exact Decidable.not_and_iff_not_or_not.1 <| mt (fun h ↦ h.1.trans h.2) xz

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
