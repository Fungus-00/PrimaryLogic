import PrimaryLogic.Encoding
import PrimaryLogic.FirstOrder.Theorem
import PrimaryLogic.FirstOrder.Soundness

namespace PrimaryLogic
variable {LF LP : Type} {L : Lang LF LP} (Γ : Set (Formula L))

private abbrev InCon : Prop := Inconsistent (Γ ∪ FOLTheory)
private abbrev Con : Prop := Consistent (Γ ∪ FOLTheory)

def MaximalConsistent : Prop := Con Γ ∧ (∀ φ, φ ∈ Γ ∨ (¬φ) ∈ Γ)

theorem maxConSet_iff (Γ : Set (Formula L)) (φ : Formula L) :
    MaximalConsistent Γ -> (φ ∈ Γ ↔ (Γ ⊢ φ)) := by
  intro m
  open Proof in
  constructor
  · intro h
    exact FOL.AS h
  · intro h
    have h' : (¬φ) ∉ Γ := by
      by_contra
      have p1 := FOL.AS this
      have p2 := mp p1 h
      exact m.left p2
    rcases m.right φ with h1 | h2
    · exact h1
    · exfalso; exact h' h2
/-
lemma con_empty : Con (L := L) ∅ := by
  unfold Con Consistent Inconsistent
  by_contra
  have h1 := soundness _ _ this
  have h2 := h1 Unit ⟨fun _ _ => .unit, fun _ _ => False⟩ (fun _ => .unit)
    fun x h => False.elim <| Set.notMem_empty x h
  unfold Formula.interpret at h2
  exact h2
-/
variable [Encodable LF] [Encodable LP] [DecidablePred (InCon (L := L))]

def tryAdd (n : Nat) : Set (Formula L) :=
  match Encodable.decode (α := Formula L) n with
  | none => Γ
  | some φ => if InCon (Γ.insert φ)
    then Γ.insert (¬φ) else Γ.insert φ

def expand (Γ : Set (Formula L)) : Nat -> Set (Formula L)
  | .zero => Γ
  | .succ n => tryAdd (expand Γ n) n

lemma tryAdd_con_valid (n : Nat) : Con Γ -> Con (tryAdd Γ n) := by
  intro h
  cases h1 : Encodable.decode (α := Formula L) n with
  | none => simp only [tryAdd, h1]; exact h
  | some φ =>
    simp only [tryAdd, h1]
    unfold Con Consistent Inconsistent at h
    split_ifs with h2
    · unfold Con Consistent
      rw [←Proof.raa]
      unfold InCon Inconsistent at h2
      have h3 := (Proof.deduction Γ φ .falsum).mp h2
      by_contra
      have := Proof.mp h3 this
      contradiction
    · exact h2

lemma expandAdd_con_valid (n : Nat) : Con Γ -> Con (expand Γ n) := by
  intro h
  induction n with
  | zero => unfold expand; exact h
  | succ n hn => unfold expand; exact tryAdd_con_valid _ n hn

lemma expandAdd_monotone (m n : Nat) : m ≤ n -> expand Γ m ⊆ expand Γ n := by
  intro hm
  induction n with
  | zero => rw [Nat.le_zero.mp hm]
  | succ n h =>
    by_cases hn : m = n + 1
    · rw [hn]
    · have : m ≤ n := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hm hn)
      apply Set.Subset.trans (h this)
      simp only [expand]
      have tryAdd_monotone (Δ : Set (Formula L)): Δ ⊆ tryAdd Δ n := by
        cases h' : Encodable.decode (α := Formula L) n with
        | none => simp only [tryAdd, h', Set.Subset.refl]
        | some φ => simp only [tryAdd, h']; split_ifs <;> exact Set.subset_insert _ Δ;
      exact tryAdd_monotone _

private abbrev maxExpand := ⋃ n : Nat, expand Γ n
lemma maximalSet_compact (φ : Formula L) : (maxExpand Γ ⊢ φ) -> ∃ n : Nat, expand Γ n ⊢ φ := by
  intro p
  induction p with
  | asp ψ hg =>
    rw [Set.mem_union, Set.mem_iUnion] at hg
    rcases hg with ⟨n, h⟩ | h
    · use n
      apply Proof.asp ψ
      rw [Set.mem_union]
      left; exact h
    · use 0
      exact FOL.axiom_proof h
  | @mp ψ χ p q hp hq =>
    obtain ⟨m, hm⟩ := hp
    obtain ⟨n, hn⟩ := hq
    use max m n
    have := expandAdd_monotone Γ m (max m n) (Nat.le_max_left m n)
    have h1 := FOL.mono this hm
    have := expandAdd_monotone Γ n (max m n) (Nat.le_max_right m n)
    have h2 := FOL.mono this hn
    exact Proof.mp h1 h2

theorem Lindenbaum : Con Γ -> MaximalConsistent (maxExpand Γ) := by
  intro h
  unfold MaximalConsistent
  constructor
  · by_contra
    unfold Inconsistent at this
    obtain ⟨n, p⟩ := maximalSet_compact Γ ⊥ this
    have := expandAdd_con_valid Γ n h
    contradiction
  · intro φ
    rcases lem (φ ∈ maxExpand Γ) with h1 | h1
    · left; exact h1
    · right
      rw [Set.mem_iUnion, not_exists] at h1
      let n := Encodable.encode (α := Formula L) φ
      refine Set.mem_iUnion.mpr ⟨n.succ, ?_⟩
      have h2 : Encodable.decode n = some φ := Encodable.encodek φ
      simp only [expand, tryAdd, h2]
      by_cases h4 : InCon (Set.insert φ (expand Γ n))
      · simp only [h4]; apply Set.mem_insert
      · have h3 := h1 n.succ
        simp only [expand, tryAdd, h2, h4] at h3
        have := Set.mem_insert φ (expand Γ n)
        contradiction
end PrimaryLogic
