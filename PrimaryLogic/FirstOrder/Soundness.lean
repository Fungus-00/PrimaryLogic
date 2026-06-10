import PrimaryLogic.Model
import PrimaryLogic.FirstOrder.Axiom

namespace PrimaryLogic
variable {LF LP : Type} {L : Lang LF LP} {α : Type u}

lemma soundness_axiom (M : Structure L α) (s : Assignment α) (ax : FOLAxioms L) :
    ax.toFormula.interpret M s :=
  match ax with
  | .h1 x y => fun h _ => h
  | .h2 x y z => fun ha hb hc => ha hc (hb hc)
  | .h3 x => fun h => dne h
  | .q1 i x y => fun ha hb a => ha a (hb a)
  | .q2 i t x g => fun h =>  (Formula.interpret_subst M s g).mpr (h _)
  | .q3 i x g => fun h a => (Formula.interpret_replace_invariance M s a g).mpr h
  | .gen i ax => (Structure.satisfies_gen_intro M ∅ (FOLAxioms.toFormula ax) i (by simp)
    fun s' _ => soundness_axiom M s' ax) s (by simp)

/-- Classical needed, from `.q3` -/
theorem soundness (Γ) (φ : Formula L) : (Γ ⊢ φ) -> (Γ ∪ FOLTheory ⊨ φ) :=
  fun p α M s h => match p with
  | .asp ψ g => h ψ g
  | .mp (φ := φ) (ψ := ψ) p q =>
    (soundness Γ (φ → ψ) p α M s h) (soundness Γ φ q α M s h)

end PrimaryLogic
