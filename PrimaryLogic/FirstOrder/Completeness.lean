import PrimaryLogic.Model
import PrimaryLogic.FirstOrder.Theorem

namespace PrimaryLogic
variable {LF LP : Type} {L : Lang LF LP}

lemma complete_iff_satisfiable :
    (∀ Γ : Set (Formula L), Consistent (FOLAxioms L) Γ -> Satisfiable Γ) <->
    (∀ Γ : Set (Formula L), ∀ φ : Formula L, (Γ ⊨ φ) -> (Γ ⊢ φ)) := by
  unfold Consistent Satisfiable SemanticConsequence Structure.satisfies
  constructor
  · intro h1 Γ φ h2
    rw [Proof.raa]
    by_contra
    have ⟨α, c, M, s, h3⟩ := h1 (Γ.insert (¬φ)) this
    simp only [Set.insert, Set.mem_setOf_eq, forall_eq_or_imp] at h3
    apply h3.left
    exact h2 α M s h3.right
  · intro h1 Γ h2
    by_contra
    apply h2
    apply h1 Γ .falsum
    simp only [not_exists] at this
    intro α c M s h3
    have := this α c M s
    contradiction

end PrimaryLogic
