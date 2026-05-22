import PrimaryLogic.FirstOrder.MaximalConsistent

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

def Formula.henkin (i : Idx) (φ : Formula L) (t : Term L) (h : t.isConst) : Formula L :=
  (¬∀i# φ) → ¬(subst i t φ <| const_FreeFor i φ t h)

class Henkin (Δ : Set (Formula L)) (θ : Formula L -> Term L) : Prop where
  mc : MaximalConsistent Δ
  pt : ∀ φ : Formula L, Term.isConst (θ φ)
  ax : ∀ i : Idx, ∀ φ : Formula L, Formula.henkin i φ (θ φ) (pt φ) ∈ Δ

variable {θ : Formula L -> Term L} [hk : Henkin Δ θ]
theorem Formula.interpret_termModel [hk : Henkin Δ θ] (φ : Formula L) :
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
    rw [false_iff ..]
    by_contra
    apply hk.mc.left
    exact .asp (α := FOLAxioms L) .falsum this
  | impl x y =>
    unfold interpret
    unfold depth at hd
    rw [h x.depth (by omega) x rfl, h y.depth (by omega) y rfl,
      maxConSet_iff Δ y hk.mc, maxConSet_iff Δ (x → y) hk.mc]
    constructor
    · intro p
      by_cases h : x ∈ Δ
      · have p' := Proof.axm (α := FOLAxioms L) (Γ := Δ) (.h1 y x)
        exact .mp p' (p h)
      · have p1 := (hk.mc.right x).resolve_left h
        rw [maxConSet_iff Δ _ hk.mc] at p1
        exact Proof.neg_impl _ _ p1
    · intro h g
      rw [maxConSet_iff Δ x hk.mc] at g
      exact .mp h g
  | fall i ψ =>
    unfold interpret; constructor
    · intro h1
      unfold depth at hd
      have h2 := h1 (θ ψ)
      have h3 := const_FreeFor i ψ (θ ψ) (hk.pt ψ)
      rw [←Term.interpret_termModel (Δ := Δ) (θ ψ), ←interpret_subst _ _ h3,
        h ψ.depth (by omega) _ (subst_depth_invariance ..), maxConSet_iff _ _ hk.mc] at h2
      have h4 : ¬ (Δ ⊢ (¬ (subst i (θ ψ) ψ h3))) := by
        by_contra; exact hk.mc.left <| .mp this h2
      have p := hk.ax i ψ
      rw [maxConSet_iff _ _ hk.mc] at p
      unfold henkin at p
      by_contra
      have h6 : (¬∀i# ψ) ∈ Δ := by
        rcases hk.mc.right (fall i ψ) with hl | hr
        · exfalso; exact this hl
        · exact hr
      rw [maxConSet_iff _ _ hk.mc] at h6
      exact h4 <| .mp p h6
    · intro h1 t
      let χ := ψ.loose t i
      sorry

end PrimaryLogic
