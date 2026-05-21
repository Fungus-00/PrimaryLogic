import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Find

namespace PrimaryLogic

section forall_in

def forallInRange (m n : Nat) (p : Nat → Bool) : Bool :=
  if h : m < n then
    p m && forallInRange (m + 1) n p
  else true
termination_by n - m

def forallInFin (n : Nat) (p : Fin n → Bool) (m : Nat := 0) : Bool :=
  if h : m < n then
    p ⟨m, h⟩ && forallInFin n p (m + 1)
  else true
termination_by n - m

lemma forall_range_eq_fin (m n : Nat) (p : Nat → Bool) (q : Fin n → Bool) :
    (∀ i : Nat, (h : i < n) → i ≥ m → p i = q ⟨i, h⟩) →
    forallInRange m n p = forallInFin n q m := by
  intro h
  induction h0 : n - m generalizing m with
  | zero =>
    unfold forallInRange forallInFin
    split_ifs
    · have := Nat.not_lt_of_ge (Nat.sub_eq_zero_iff_le.mp h0)
      contradiction
    · eq_refl
  | succ d hd =>
    unfold forallInRange forallInFin
    split_ifs with h1
    · have h2 (i : Nat) (hm : i ≥ m + 1) := Nat.le_trans (Nat.le_add_right m 1) hm
      rw [hd (m + 1) (fun i hi hm => h i hi (h2 i hm)) (by omega)]
      rw [h m h1 (Nat.le_refl m)]
    · eq_refl

theorem forallInRange_eq (i n : Nat) (p : Nat → Bool) :
    forallInRange i n p = true ↔ ∀ j : Nat, j < n → j ≥ i → p j := by
  constructor
  · intro h j hn hi
    revert h p
    induction h0 : n - i generalizing i with
    | zero =>
      have := Nat.not_lt_of_ge (Nat.sub_eq_zero_iff_le.mp h0)
      have := Nat.lt_of_le_of_lt (ge_iff_le.mp hi) hn
      contradiction
    | succ d hd =>
      intros p h
      by_cases h1 : j = i
      · rw [h1]
        have h2 : i < n := by omega
        unfold forallInRange at h
        split_ifs at h
        exact Bool.and_elim_left h
      · apply hd (i + 1) (by omega) (by omega) p
        unfold forallInRange at h
        split_ifs at h with h2
        · exact Bool.and_elim_right h
        · have : i < n := by omega
          contradiction
  · intro h
    induction h0 : n - i generalizing i with
    | zero =>
      unfold forallInRange
      split_ifs with h1
      · have := Nat.not_lt_of_ge (Nat.sub_eq_zero_iff_le.mp h0)
        contradiction
      · eq_refl
    | succ d hd =>
      have h1 : i < n := by omega
      unfold forallInRange
      split_ifs
      rw [Bool.and_eq_true_iff]
      constructor
      · exact h i h1 (Nat.le_refl i)
      · apply hd (i + 1)
        · intro j hj hi
          exact h j hj (by omega)
        · omega

theorem forallInFin_eq (n : Nat) (p : Fin n → Bool) :
    forallInFin n p = true ↔ ∀ i : Fin n, p i := by
  let s (i : Nat) := if h : i < n then p ⟨i, h⟩ else true
  have h1 := forallInRange_eq 0 n s
  have h2 : ∀ (i : ℕ) (h : i < n), i ≥ 0 → s i = p ⟨i, h⟩ := by
    intros; unfold s; split_ifs; eq_refl
  have h3 := forall_range_eq_fin 0 n s p h2
  rw [←h3, h1]
  constructor
  · intro h i
    have h4 := h i.val i.isLt (Nat.zero_le i)
    unfold s at h4
    split_ifs at h4 with h5
    · exact h4
    · exfalso; exact h5 i.isLt
  · intro h i h4 _
    unfold s
    split_ifs
    exact h ⟨i, h4⟩

end forall_in

abbrev Idx := Nat -- Planed to be replaced with type argument.

section assignment

abbrev Assignment (α : Type*) := Idx -> α

variable {α : Type u} (s : Assignment α)

abbrev replace (i : Idx) (a : α) :=
  fun k => if k = i then a else s k

lemma replace_absorb (i : Idx) : replace s i (s i) = s := by grind

lemma replace_comm (i j : Idx) (h : i ≠ j) (a b : α) :
    replace (replace s i a) j b = replace (replace s j b) i a := by grind

lemma replace_idempotent (i : Idx) (a b : α) :
    replace (replace s i a) i b = replace s i b := by grind

end assignment

section freshable
class Freshable (α : Type*) [DecidableEq α] where
  fresh : Finset α → α
  fresh_is_new : ∀ s : Finset α, fresh s ∉ s

/-- `fresh` algorithm was originally implemented by `Finset.max` function,
    without optimal utilization of space, then `Nat.find` was selected instead.
  Not sure the time efficiency of the latter though.
  Yet both the time and space optimal algorithm will be explored in another file. -/
instance : Freshable Idx where
  fresh := fun s => Nat.find (p := (· ∉ s)) (by
    cases h : s.max with
    | bot => simp [Finset.max_eq_bot.mp h]
    | coe m =>
      use m + 1
      exact Finset.notMem_of_max_lt (a := m+1) (b := m) (by simp) h
  )
  fresh_is_new s := Nat.find_spec (p := fun i => i ∉ s) _
end freshable
end PrimaryLogic
