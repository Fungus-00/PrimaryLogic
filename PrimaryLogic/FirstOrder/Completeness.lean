import PrimaryLogic.Model
import PrimaryLogic.FirstOrder.Henkin

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

lemma Satisfiable_expand {Γ : Set (Formula L)} : Satisfiable Γ → Satisfiable (Γ ∪ FOLTheory) :=
  fun ⟨α, M, s, h⟩ => ⟨α, M, s, fun g h' => Or.elim h' (h g) fun hg =>
    Exists.elim ((FOL.mem_theory_iff g).mp hg) fun a he => he ▸ soundness_axiom M s a⟩

section TermModel

def TermModel (Δ : Set (Formula L)) : Structure L (Term L) where
  funMap n f := .app n f
  relMap n p := .atom n p ∈ Δ

variable {Δ : Set (Formula L)}

theorem Term.interpret_termModel (t : Term L) : interpret (TermModel Δ) .var t = t := by
  induction t with
  | var i => unfold interpret; rfl
  | app f s h =>
    unfold interpret Structure.funMap
    conv => lhs; arg 0; dsimp only [TermModel]
    congr; funext k; exact h k

instance {α : Type*} (s : Set α) [inst : DecidablePred s] : DecidablePred (· ∈ s) := inst

variable {θ : Idx -> Formula L -> Term L}
set_option linter.unusedDecidableInType false in
theorem Formula.truth_lemma [DecidablePred Δ] [hk : Henkin Δ θ] (φ : Formula L) :
    interpret (TermModel Δ) .var φ ↔ φ ∈ Δ := by
  induction hd : φ.depth using Nat.strongRec generalizing φ with
  | ind d h => cases φ with
  | atom n s =>
    unfold interpret Structure.relMap
    conv =>
      lhs
      conv => arg 0; dsimp only [TermModel]
      conv => arg 2; arg 2; intro i; rw [Term.interpret_termModel (s i)]
  | falsum =>
    unfold interpret
    rw [false_iff]
    by_contra
    apply hk.mc.left
    exact FOL.AS this
  | impl x y =>
    unfold interpret
    unfold depth at hd
    rw [h x.depth (by omega) x rfl, h y.depth (by omega) y rfl,
      maxConSet_iff Δ y hk.mc, maxConSet_iff Δ (x → y) hk.mc]
    constructor
    · intro p
      by_cases h : x ∈ Δ
      · have p' := FOL.AX Δ (.h1 y x)
        exact .mp p' (p h)
      · have p1 := (hk.mc.right x).resolve_left h
        rw [maxConSet_iff Δ _ hk.mc] at p1
        exact Proof.neg_impl p1
    · intro h g
      rw [maxConSet_iff Δ x hk.mc] at g
      exact .mp h g
  | fall i ψ =>
    have m (x : Formula L) := maxConSet_iff Δ x hk.mc
    unfold interpret; constructor
    · intro h1
      unfold depth at hd
      have h2 := h1 (θ i ψ)
      have h3 := hk.pt i ψ
      rw [←Term.interpret_termModel (Δ := Δ) (θ i ψ), ←interpret_subst _ _ h3,
        h ψ.depth (by omega) _ (subst_depth_eq ..), m] at h2
      have h4 : ¬ (Δ ⊢ (¬ (subst i (θ i ψ) ψ h3))) :=
        fun h' => hk.mc.left <| .mp h' h2
      have p := hk.ax i ψ
      rw [m] at p
      unfold henkinForm at p
      by_contra
      have h6 : (¬∀i# ψ) ∈ Δ := by
        rcases hk.mc.right (fall i ψ) with hl | hr
        · exfalso; exact this hl
        · exact hr
      rw [m] at h6
      exact h4 <| .mp p h6
    · intro p t
      rw [m] at p
      have ⟨q, r⟩ := Proof.loose_equiv i t ψ
      replace r := Proof.impl_all_intro i r
      conv at r => rw [Set.singleton_def]; dsimp [insert]; rw [Proof.deduction]
      replace r := FOL.mono (Set.empty_subset Δ) r
      replace p := Proof.mp r p
      have p' := FOL.AX (Γ := Δ) <| FOLAxioms.q2 i t (loose t i ψ) (loose_FreeFor ..)
      replace p := Proof.mp p' p
      replace p := (m _).mpr p
      unfold depth at hd
      rw [←h ψ.depth (by omega) _ <| Eq.trans (subst_depth_eq ..) (loose_depth_eq ..),
        interpret_subst, Term.interpret_termModel] at p
      apply soundness _ _ q _ (TermModel Δ) (replace Term.var i t)
      intro g hg
      rw [Set.mem_union, Set.mem_singleton_iff] at hg
      rcases hg with h' | h'
      · rw [h']
        exact p
      · rw [FOL.mem_theory_iff] at h'
        obtain ⟨a, ha⟩ := h'
        replace h' := soundness_axiom (TermModel Δ) (replace Term.var i t) a
        rwa [ha] at h'
end TermModel

section completeness
set_option linter.unusedDecidableInType false in
lemma complete_iff_satisfiable :
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

variable [Encodable LF] [Encodable LP]



end completeness
end PrimaryLogic
