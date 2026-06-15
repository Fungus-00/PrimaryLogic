import PrimaryLogic.FirstOrder.MaximalConsistent
import PrimaryLogic.FirstOrder.Soundness

namespace PrimaryLogic
variable {LF LP : Type} {L : Lang LF LP}

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

class Henkin (Δ : Set (Formula L)) (θ : Idx -> Formula L -> Term L) : Prop where
  mc : MaximalConsistent Δ
  pt : ∀ i : Idx, ∀ φ : Formula L, Formula.FreeFor i (θ i φ) φ
  ax : ∀ i : Idx, ∀ φ : Formula L, Formula.henkin i (θ i φ) φ (pt i φ) ∈ Δ

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
      unfold henkin at p
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
end PrimaryLogic
