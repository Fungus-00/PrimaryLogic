import PrimaryLogic.Model
import PrimaryLogic.FirstOrder.MaximalConsistent

namespace PrimaryLogic
variable {LF LP : Type} {L : Lang LF LP}

set_option linter.unusedDecidableInType false in
lemma complete_iff_satisfiable [DecidablePred (Inconsistent (L := L))] :
    (∀ Γ : Set (Formula L), Con Γ -> Satisfiable (Γ ∪ FOLTheory)) <->
    (∀ Γ : Set (Formula L), ∀ φ : Formula L, (Γ ⊨ φ) -> (Γ ⊢ φ)) := by
  unfold Con Consistent Satisfiable SemanticConsequence Structure.satisfies
  constructor
  · intro h1 Γ φ h2
    rw [Proof.raa]
    rcases lem <| Inconsistent (Set.insert (¬φ) Γ ∪ FOLTheory) with h5 | h5
    · exact h5
    · have ⟨α, M, s, h3⟩ := h1 (Γ.insert (¬φ)) h5
      simp only [Set.mem_union, Set.insert, Set.mem_setOf_eq] at h3
      replace h4 := h3 (¬φ)
      simp only [true_or, FOL.mem_theory_iff, forall_const, Formula.not, Formula.interpret] at h4
      exfalso
      refine h4 <| h2 α M s ?_
      intro g hg
      exact h3 g (.inl (.inr hg))
  · intro h1 Γ h2
    rcases lem <| ∃ α M s, ∀ g ∈ Γ ∪ FOLTheory, Formula.interpret M s g with h' | h'
    · exact h'
    · simp only [not_exists, PrimaryLogic.not_forall, Set.mem_union] at h'
      exfalso
      apply h2
      apply h1 Γ ⊥
      intro α M s h
      have ⟨x, h3, h4⟩ := h' α M s
      exfalso; apply h4
      rcases h3 with h3 | h3
      · exact h x h3
      · rw [FOL.mem_theory_iff] at h3
        obtain ⟨a, h4⟩ := h3
        exact h4 ▸ soundness_axiom M s a

end PrimaryLogic
