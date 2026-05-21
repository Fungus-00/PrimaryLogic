import PrimaryLogic.FirstOrder.Axiom

namespace PrimaryLogic
namespace Proof
variable {LF LP : Type} {L : Lang LF LP} {Γ : Set (Formula L)}

private abbrev AX (Δ : Set (Formula L)) := Proof.axm (α := FOLAxioms L) (Γ := Δ)

section propositional
lemma refl_impl (x : Formula L) : Γ ⊢ x → x :=
  let p1 := AX Γ <| .h2 x (x → x) x
  let p2 := AX Γ <| .h1 x (x → x)
  let p3 := p1.mp p2
  let p4 := AX Γ <| .h1 x x
  p3.mp p4

theorem deduction (Γ) (φ ψ : Formula L) :
    (Γ.insert φ ⊢ ψ) <-> (Γ ⊢ φ → ψ) := by
  constructor
  · intro p
    induction p with
    | asp x h =>
      rcases h with (rfl | hi)
      · exact refl_impl x
      · exact (AX Γ (.h1 x φ)).mp (asp x hi)
    | axm a => exact (AX Γ (.h1 (AxiomSchema.toFormula a) φ)).mp (AX Γ a)
    | @mp x y _ _ h1 h2 => exact ((AX Γ (.h2 φ x y)).mp h1).mp h2
  · intro p
    have : FOLProof (Γ.insert φ) (φ → ψ) :=
      monotone (FOLAxioms L) (Set.subset_insert φ Γ) p
    exact this.mp (asp φ (Set.mem_insert φ Γ))

lemma impl_trans (x y z : Formula L) :
    (Γ ⊢ x → y) -> (Γ ⊢ y → z) -> (Γ ⊢ x → z) := fun h g =>
  have h0 : (Γ.insert _).insert _ = (Γ.insert _).insert _ := Set.insert_comm x (x → y → z) Γ
  let p1 := AX Γ (.h2 x y z)
  let p2 := (deduction Γ (x → y → z) ((x → y) → (x → z))).mpr p1
  let p3 := monotone (FOLAxioms L) (Set.subset_insert (x → y → z) Γ) h
  let p4 := mp p2 p3
  let p5 := (deduction _ x z).mpr p4
  let p6 := cast (by rw [h0]) p5
  let p7 := (deduction _ (x → y → z) z).mp p6
  let p8 := AX (Γ.insert x) (.h1 (y → z) x)
  let p9 := monotone (FOLAxioms L) (Set.subset_insert x Γ) g
  let p10 := mp p8 p9
  let p11 := mp p7 p10
  (deduction Γ x z).mp p11

lemma exfalso (x : Formula L) : Γ ⊢ ⊥ → x :=
  let p1 := AX Γ <| .h1 ⊥ (x → ⊥)
  let p2 := AX (Γ.insert ⊥) (.h3 x)
  let p3 := (deduction Γ ⊥ ((x → ⊥) → ⊥)).mpr p1
  let p4 := p2.mp p3
  (deduction Γ ⊥ x).mp p4

lemma neg_impl (x y : Formula L) : (Γ ⊢ ¬x) -> (Γ ⊢ x → y) := fun h =>
  let p1 := AX Γ <| .h2 x ⊥ y
  let p2 := exfalso (Γ := Γ) y
  let p3 := AX Γ <| .h1 (⊥ → y) x
  let p4 := mp p3 p2
  let p5 := mp p1 p4
  mp p5 h

lemma intro_double_neg (x : Formula L) : Γ ⊢ x → ¬¬x :=
  let Δ := (Γ.insert x).insert (x → ⊥)
  let as := asp (α := FOLAxioms L) (Γ := Δ)
  let p1 := as (x → ⊥) <| by simp [Δ, Set.insert]
  let p2 := as x <| by simp [Δ, Set.insert]
  let p3 := p1.mp p2
  let p4 := deduction (Γ.insert x) (x → ⊥) ⊥
  let p5 := p4.mp p3
  (deduction Γ x ((x → ⊥) → ⊥)).mp p5

lemma contrapositive (x y : Formula L) : Γ ⊢ (¬x → ¬y) → (y → x) :=
  let Δ := (Γ.insert ((x → ⊥) → (y → ⊥))).insert y
  let as := asp (α := FOLAxioms L) (Γ := Δ.insert (x → ⊥))
  let p1 := as ((x → ⊥) → (y → ⊥)) <| by simp [Δ, Set.insert]
  let p2 := as y <| by simp [Δ, Set.insert]
  let p3 := as (x → ⊥) <| by simp [Set.insert]
  let p4 := p1.mp p3
  let p5 := p4.mp p2
  let p6 := (deduction Δ (x → ⊥) ⊥).mp p5
  let p7 := Proof.axm (α := FOLAxioms L) (Γ := Δ) (.h3 x)
  let p8 := p7.mp p6
  let p9 := (deduction (Γ.insert ((x → ⊥) → (y → ⊥))) y x).mp p8
  (deduction Γ ((x → ⊥) → (y → ⊥)) (y → x)).mp p9

lemma raa (x : Formula L) : (Γ ⊢ x) <-> Inconsistent (FOLAxioms L) (Γ.insert (¬x)) := by
  unfold Inconsistent
  constructor
  · intro p
    apply (deduction Γ (¬x) .falsum).mpr
    exact (intro_double_neg x).mp p
  · intro p
    apply (AX Γ (.h3 x)).mp
    exact (deduction Γ (¬x) .falsum).mp p
end propositional

variable (Γ : Set (Formula L))

section quantifier
theorem gen_rule (φ : Formula L) (i : Idx) :
    (∀ g ∈ Γ, i ∉ g.fVars) -> (Γ ⊢ φ) -> (Γ ⊢ ∀i# φ) := by
  intro hg p
  induction p with
  | asp ψ h => exact (AX Γ (.q3 i ψ (hg ψ h))).mp (asp ψ h)
  | axm a => exact AX Γ (.gen i a)
  | @mp x y _ _ p1 p2 => exact ((AX Γ (.q1 i x y)).mp p1).mp p2

lemma all_elim (φ : Formula L) (i : Idx) : Γ ⊢ (∀i# φ) → φ :=
  let h := Formula.fVar_refl i φ
  let p : FOLProof Γ ((∀i# φ) → (φ.safeSub i (.var i) h)) :=
    AX Γ (.q2 i (.var i) φ h)
  cast (congrArg (Γ ⊢ (∀i# φ) → ·) <| Formula.subst_self i φ h) p

lemma all_comm (φ : Formula L) (i j : Idx) :
    Γ.insert (∀i#∀j# φ) ⊢ ∀j#∀i# φ :=
  let p1 := all_elim ∅ φ j
  let p2 := all_elim ∅ (∀j# φ) i
  let p3 := impl_trans (∀i#∀j# φ) (∀j# φ) φ p2 p1
  let p4 := (deduction ∅ ..).mpr p3
  have hi : ∀ g ∈ Set.insert (∀i#∀j# φ) ∅, i ∉ g.fVars := by
    intro g;
    simp only [Set.insert, Set.mem_empty_iff_false, or_false,
      Set.setOf_eq_eq_singleton, Set.mem_singleton_iff]
    intro gh; rw[gh]
    simp [Formula.fVars]
  have hj : ∀ g ∈ Set.insert (∀i#∀j# φ) ∅, j ∉ g.fVars := by
    intro g;
    simp only [Set.insert, Set.mem_empty_iff_false, or_false,
      Set.setOf_eq_eq_singleton, Set.mem_singleton_iff]
    intro gh; rw[gh]
    simp [Formula.fVars]
  let p5 := gen_rule _ φ i hi p4
  let p6 := gen_rule _ (∀i# φ) j hj p5
  let p7 := (deduction ∅ _ _).mp p6
  let p8 := Proof.monotone (FOLAxioms L) (Set.empty_subset Γ) p7
  (deduction Γ ..).mpr p8
end quantifier

theorem Formula.loose_FreeFor (i : Idx) (t : Term L) (φ : Formula L) :
    ({φ.loose t i} ⊢ φ) ∧ ({φ} ⊢ φ.loose t i) := sorry

end Proof
end PrimaryLogic
