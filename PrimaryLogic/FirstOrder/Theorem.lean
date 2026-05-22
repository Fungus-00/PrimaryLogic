import PrimaryLogic.FirstOrder.Axiom

namespace PrimaryLogic
namespace Proof
variable {LF LP : Type} {L : Lang LF LP} {Γ : Set (Formula L)}

private abbrev AX (Δ : Set (Formula L)) := Proof.axm (α := FOLAxioms L) (Γ := Δ)

section propositional
lemma refl_impl (x : Formula L) : Γ ⊢ x → x :=
  have p1 := AX Γ <| .h2 x (x → x) x
  have p2 := AX Γ <| .h1 x (x → x)
  have p3 := p1.mp p2
  have p4 := AX Γ <| .h1 x x
  p3.mp p4

@[simp]
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

lemma impl_trans {x y z : Formula L} :
    (Γ ⊢ x → y) -> (Γ ⊢ y → z) -> (Γ ⊢ x → z) := fun h g =>
  have h0 : (Γ.insert _).insert _ = (Γ.insert _).insert _ := Set.insert_comm x (x → y → z) Γ
  have p1 := AX Γ (.h2 x y z)
  have p2 := (deduction Γ (x → y → z) ((x → y) → (x → z))).mpr p1
  have p3 := monotone (FOLAxioms L) (Set.subset_insert (x → y → z) Γ) h
  have p4 := mp p2 p3
  have p5 := (deduction _ x z).mpr p4
  have p6 := cast (by rw [h0]) p5
  have p7 := (deduction _ (x → y → z) z).mp p6
  have p8 := AX (Γ.insert x) (.h1 (y → z) x)
  have p9 := monotone (FOLAxioms L) (Set.subset_insert x Γ) g
  have p10 := mp p8 p9
  have p11 := mp p7 p10
  (deduction Γ x z).mp p11

lemma exfalso (x : Formula L) : Γ ⊢ ⊥ → x :=
  have p1 := AX Γ <| .h1 ⊥ (x → ⊥)
  have p2 := AX (Γ.insert ⊥) (.h3 x)
  have p3 := (deduction Γ ⊥ ((x → ⊥) → ⊥)).mpr p1
  have p4 := p2.mp p3
  (deduction Γ ⊥ x).mp p4

lemma neg_impl (x y : Formula L) : (Γ ⊢ ¬x) -> (Γ ⊢ x → y) := fun h =>
  have p1 := AX Γ <| .h2 x ⊥ y
  have p2 := exfalso (Γ := Γ) y
  have p3 := AX Γ <| .h1 (⊥ → y) x
  have p4 := mp p3 p2
  have p5 := mp p1 p4
  mp p5 h

lemma intro_double_neg (x : Formula L) : Γ ⊢ x → ¬¬x :=
  let Δ := (Γ.insert x).insert (x → ⊥)
  have as := asp (α := FOLAxioms L) (Γ := Δ)
  have p1 := as (x → ⊥) <| by simp [Δ, Set.insert]
  have p2 := as x <| by simp [Δ, Set.insert]
  have p3 := p1.mp p2
  have p4 := deduction (Γ.insert x) (x → ⊥) ⊥
  have p5 := p4.mp p3
  (deduction Γ x ((x → ⊥) → ⊥)).mp p5

lemma contrapositive (x y : Formula L) : Γ ⊢ (¬x → ¬y) → (y → x) :=
  let Δ := (Γ.insert ((x → ⊥) → (y → ⊥))).insert y
  have as := asp (α := FOLAxioms L) (Γ := Δ.insert (x → ⊥))
  have p1 := as ((x → ⊥) → (y → ⊥)) <| by simp [Δ, Set.insert]
  have p2 := as y <| by simp [Δ, Set.insert]
  have p3 := as (x → ⊥) <| by simp [Set.insert]
  have p4 := p1.mp p3
  have p5 := p4.mp p2
  have p6 := (deduction Δ (x → ⊥) ⊥).mp p5
  have p7 := Proof.axm (α := FOLAxioms L) (Γ := Δ) (.h3 x)
  have p8 := p7.mp p6
  have p9 := (deduction (Γ.insert ((x → ⊥) → (y → ⊥))) y x).mp p8
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
  have h := Formula.fVar_refl i φ
  have p : FOLProof Γ ((∀i# φ) → (φ.subst i (.var i) h)) :=
    AX Γ (.q2 i (.var i) φ h)
  cast (congrArg (Γ ⊢ (∀i# φ) → ·) <| Formula.subst_self i φ h) p

lemma all_comm (φ : Formula L) (i j : Idx) :
    Γ.insert (∀i#∀j# φ) ⊢ ∀j#∀i# φ :=
  have p1 := all_elim ∅ φ j
  have p2 := all_elim ∅ (∀j# φ) i
  have p3 := impl_trans p2 p1
  have p4 := (deduction ∅ ..).mpr p3
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
  have p5 := gen_rule _ φ i hi p4
  have p6 := gen_rule _ (∀i# φ) j hj p5
  have p7 := (deduction ∅ _ _).mp p6
  have p8 := Proof.monotone (FOLAxioms L) (Set.empty_subset Γ) p7
  (deduction Γ ..).mpr p8

lemma impl_all_intro (i : Idx) {φ ψ : Formula L} (p : {φ} ⊢ ψ) : {∀i#φ} ⊢ ∀i#ψ :=
  have p1 : ∅ ⊢ φ → ψ := by
    rw [Set.singleton_def] at p; dsimp [insert] at p; exact (deduction ..).mp p
  have p2 := gen_rule ∅ _ i (fun x h => False.elim (Set.notMem_empty x h)) p1
  have p3 := AX ∅ <| .q1 i φ ψ
  have p4 := mp p3 p2
  by rw [Set.singleton_def]; dsimp [insert]; rw [deduction]; exact p4

end quantifier

theorem loose_equiv (i : Idx) (t : Term L) (φ : Formula L) :
    ({φ.loose t i} ⊢ φ) ∧ ({φ} ⊢ φ.loose t i) := by
  open Formula Set in
  induction φ with
  | atom | falsum => unfold loose; split_ands <;> exact asp _ (mem_singleton _)
  | impl x y hx hy =>
    unfold loose;
    repeat rw [singleton_def, insert] at hx hy
    dsimp [instInsert] at hx hy
    repeat rw [deduction] at hx hy
    split_ands
    · let ψ := loose t i x → loose t i y
      have p1 := monotone _ (Δ := {ψ}) (empty_subset _) hx.right
      have p2 := asp (α := FOLAxioms L) (Γ := {ψ}) ψ (mem_singleton _)
      have p3 := monotone _ (Δ := {ψ}) (empty_subset _) hy.left
      exact impl_trans (impl_trans p1 p2) p3
    · let ψ := x → y
      have p1 := monotone _ (Δ := {ψ}) (empty_subset _) hx.left
      have p2 := asp (α := FOLAxioms L) (Γ := {ψ}) ψ (mem_singleton _)
      have p3 := monotone _ (Δ := {ψ}) (empty_subset _) hy.right
      exact impl_trans (impl_trans p1 p2) p3
  | fall j ψ h =>
    split_ands
    · sorry
    · let χ := ψ.loose t i
      let k := Freshable.fresh <| insert i (χ.vars ∪ t.vars)
      have hk : k ∉ χ.vars := Finset.not_mem_subset
        (subset_trans (Finset.subset_union_left ..) (Finset.subset_insert ..))
        (Freshable.fresh_is_new (insert i (χ.vars ∪ t.vars)))
      have p1 := impl_all_intro j h.right
      have h2 : FreeFor j (.var k) χ := by
        apply term_FreeFor
        unfold Term.vars
        simp only [hk, not_false_eq_true, Finset.singleton_inter_of_notMem]
      have p2 := Proof.AX ∅ (.q2 j (.var k) χ h2)
      have p3 := (deduction ..).mpr p2
      replace p3 := gen_rule _ _ k (by
        intro g hg
        dsimp [Set.insert] at hg
        rw [Or.resolve_right hg <| notMem_empty g]
        unfold fVars
        apply Finset.not_mem_subset (Finset.erase_subset ..)
        exact Finset.not_mem_subset (fVars_subset_vars ..) hk
        ) p3
      replace p3 := (deduction ..).mp p3
      replace p3 := monotone (Δ := {Formula.fall j ψ}) _ (empty_subset _) p3
      exact mp p3 p1

end Proof
end PrimaryLogic
