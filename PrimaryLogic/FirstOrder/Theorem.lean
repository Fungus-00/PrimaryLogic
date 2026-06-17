import PrimaryLogic.FirstOrder.Axiom

namespace PrimaryLogic
namespace Proof
variable {LF LP : Type} {L : Lang LF LP} {Γ : Set (Formula L)}
open FOL
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
      replace h : x ∈ insert φ Γ ∪ FOLTheory := h
      rw [Set.mem_union, Set.mem_insert_iff, or_assoc] at h
      rcases h with (rfl | hi)
      · exact refl_impl x
      · exact (AX Γ (.h1 x φ)).mp (asp x hi)
    | @mp x y _ _ h1 h2 => exact ((AX Γ (.h2 φ x y)).mp h1).mp h2
  · intro p
    have : FOLProof (Γ.insert φ) (φ → ψ) :=
      mono (Set.subset_insert φ Γ) p
    exact this.mp <| AS (Set.mem_insert φ Γ)

lemma impl_trans {x y z : Formula L} :
    (Γ ⊢ x → y) -> (Γ ⊢ y → z) -> (Γ ⊢ x → z) := fun h g =>
  have h0 : (Γ.insert _).insert _ = (Γ.insert _).insert _ := Set.insert_comm' x (x → y → z) Γ
  have p1 := AX Γ (.h2 x y z)
  have p2 := (deduction Γ (x → y → z) ((x → y) → (x → z))).mpr p1
  have p3 := mono (Set.subset_insert (x → y → z) Γ) h
  have p4 := mp p2 p3
  have p5 := (deduction _ x z).mpr p4
  have p6 := cast (by rw [h0]) p5
  have p7 := (deduction _ (x → y → z) z).mp p6
  have p8 := AX (Γ.insert x) (.h1 (y → z) x)
  have p9 := mono (Set.subset_insert x Γ) g
  have p10 := mp p8 p9
  have p11 := mp p7 p10
  (deduction Γ x z).mp p11

lemma exfalso (x : Formula L) : Γ ⊢ ⊥ → x :=
  have p1 := AX Γ <| .h1 ⊥ (x → ⊥)
  have p2 := AX (Γ.insert ⊥) (.h3 x)
  have p3 := (deduction Γ ⊥ ((x → ⊥) → ⊥)).mpr p1
  have p4 := p2.mp p3
  (deduction Γ ⊥ x).mp p4

lemma neg_impl {x y : Formula L} : (Γ ⊢ ¬x) -> (Γ ⊢ x → y) := fun h =>
  have p1 := AX Γ <| .h2 x ⊥ y
  have p2 := exfalso (Γ := Γ) y
  have p3 := AX Γ <| .h1 (⊥ → y) x
  have p4 := mp p3 p2
  have p5 := mp p1 p4
  mp p5 h

lemma intro_double_neg (x : Formula L) : Γ ⊢ x → ¬¬x :=
  let Δ := (Γ.insert x).insert (x → ⊥)
  have p1 := AS (φ := x → ⊥) <| by simp only [Set.insert, Set.mem_setOf_eq, true_or]
  have p2 := AS (φ := x) <| by simp only [Set.insert, Set.mem_setOf_eq, true_or, or_true]
  have p3 := p1.mp p2
  have p4 := deduction (Γ.insert x) (x → ⊥) ⊥
  have p5 := p4.mp p3
  (deduction Γ x ((x → ⊥) → ⊥)).mp p5

lemma contrapositive (x y : Formula L) : Γ ⊢ (¬x → ¬y) → (y → x) :=
  let Δ := (Γ.insert ((x → ⊥) → (y → ⊥))).insert y
  have p1 := AS (φ := (x → ⊥) → (y → ⊥)) <| by simp [Δ, Set.insert]
  have p2 := AS (φ := y) <| by simp [Δ, Set.insert]
  have p3 := AS (φ := x → ⊥) <| by simp [Set.insert]
  have p4 := p1.mp p3
  have p5 := p4.mp p2
  have p6 := (deduction Δ (x → ⊥) ⊥).mp p5
  have p7 := AX Δ (.h3 x)
  have p8 := p7.mp p6
  have p9 := (deduction (Γ.insert ((x → ⊥) → (y → ⊥))) y x).mp p8
  (deduction Γ ((x → ⊥) → (y → ⊥)) (y → x)).mp p9

lemma neg_of_impl_left (x y : Formula L) : Γ ⊢ ¬(x → y) → x :=
  have p1 := AS (φ := ¬x) (Set.mem_insert _ Γ)
  have p2 := neg_impl (y := y) p1
  have p3 := intro_double_neg (Γ := insert (¬x) Γ) (x → y)
  have p4 := mp p3 p2
  have p5 := (deduction ..).mp p4
  have p6 := contrapositive (Γ := Γ) x (¬(x → y))
  mp p6 p5

lemma neg_of_impl_right (x y : Formula L) : Γ ⊢ ¬(x → y) → ¬y :=
  let Δ := insert y <| insert (¬(x → y)) Γ
  have p1 := AX Δ <| .h1 y x
  have p2 := AS <| Set.mem_insert y (insert (¬(x → y)) Γ)
  have p3 := mp p1 p2
  have p4 := AS <| Set.mem_insert_of_mem y (Set.mem_insert (¬(x → y)) Γ)
  have p5 := mp p4 p3
  by simpa only [insert, deduction] using p5

lemma raa (x : Formula L) : (Γ ⊢ x) <-> Inconsistent (Γ.insert (¬x) ∪ FOLTheory) := by
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
    (∀ g ∈ Γ, i ∉ g.fvar) -> (Γ ⊢ φ) -> (Γ ⊢ ∀i# φ) := by
  intro hg p
  induction p with
  | asp ψ h =>
    rw [Set.mem_union] at h
    rcases h with h1 | h2
    · exact (AX Γ (.q3 i ψ <| hg ψ h1)).mp (asp ψ (.inl h1))
    · apply asp (.fall i ψ)
      rw [Set.mem_union]; right
      rw [mem_theory_iff] at h2 ⊢
      obtain ⟨y, h3⟩ := h2
      use .gen i y
      unfold FOLAxioms.toFormula
      rw [h3]
  | @mp x y _ _ p1 p2 => exact ((AX Γ (.q1 i x y)).mp p1).mp p2

lemma all_elim (φ : Formula L) (i : Idx) : Γ ⊢ (∀i# φ) → φ :=
  have h := Formula.fvar_refl i φ
  have p : FOLProof Γ ((∀i# φ) → (φ.subst i (.var i) h)) :=
    AX Γ (.q2 i (.var i) φ h)
  cast (congrArg (Γ ⊢ (∀i# φ) → ·) <| Formula.subst_self i φ) p

lemma all_comm (φ : Formula L) (i j : Idx) :
    Γ.insert (∀i#∀j# φ) ⊢ ∀j#∀i# φ :=
  have p1 := all_elim ∅ φ j
  have p2 := all_elim ∅ (∀j# φ) i
  have p3 := impl_trans p2 p1
  have p4 := (deduction ∅ ..).mpr p3
  have hi : ∀ g ∈ Set.insert (∀i#∀j# φ) ∅, i ∉ g.fvar := by
    intro g;
    simp only [Set.insert, Set.mem_empty_iff_false, or_false,
      Set.setOf_eq_eq_singleton, Set.mem_singleton_iff]
    intro gh; rw[gh]
    simp [Formula.fvar]
  have hj : ∀ g ∈ Set.insert (∀i#∀j# φ) ∅, j ∉ g.fvar := by
    intro g;
    simp only [Set.insert, Set.mem_empty_iff_false, or_false,
      Set.setOf_eq_eq_singleton, Set.mem_singleton_iff]
    intro gh; rw[gh]
    simp [Formula.fvar]
  have p5 := gen_rule _ φ i hi p4
  have p6 := gen_rule _ (∀i# φ) j hj p5
  have p7 := (deduction ∅ _ _).mp p6
  have p8 := mono (Set.empty_subset Γ) p7
  (deduction Γ ..).mpr p8

lemma impl_all_intro (i : Idx) {φ ψ : Formula L} (p : {φ} ⊢ ψ) : {∀i#φ} ⊢ ∀i#ψ :=
  have p1 : ∅ ⊢ φ → ψ := by
    rw [Set.singleton_def] at p; dsimp [insert] at p; exact (deduction ..).mp p
  have p2 := gen_rule ∅ _ i (fun x h => False.elim (Set.notMem_empty x h)) p1
  have p3 := AX ∅ <| .q1 i φ ψ
  have p4 := mp p3 p2
  by rw [Set.singleton_def]; dsimp [insert]; rw [deduction]; exact p4

lemma all_impl_subst (i j : Idx) {φ : Formula L} (hj : j ∉ φ.vars) :
    ∅ ⊢ (∀j#(Formula.subst i (.var j) φ (Formula.var_var_FreeFor i j φ hj))) → ∀i#φ := by
  have h1 := Formula.var_var_FreeFor i j φ hj
  have ⟨h2, h3⟩ := Formula.subst_circulation i j φ hj
  have p1 := AX ∅ <| .q2 j (.var i) (Formula.subst i (.var j) φ h1) h2
  unfold FOLAxioms.toFormula at p1
  rw [h3, ←deduction] at p1
  have p2 := gen_rule _ φ i (fun g h0 => Or.elim h0 (fun h h4 =>
    have ⟨h5, h6⟩ := Set.mem_diff_singleton.mp (by rwa [h] at h4)
    Or.elim ((Formula.subst_fvar i (.var j) φ h1) h5) h6
      fun h' => ((Set.mem_diff_singleton).mp h').2 rfl)
    fun h _ => Set.notMem_empty g h) p1
  exact (deduction ..).mp p2

end quantifier

theorem loose_equiv (i : Idx) (t : Term L) (φ : Formula L) :
    ({φ.loose t i} ⊢ φ) ∧ ({φ} ⊢ φ.loose t i) := by
  open Formula Set in
  induction φ with
  | atom | falsum => unfold loose; split_ands <;> exact AS (Set.mem_singleton _)
  | impl x y hx hy =>
    unfold loose
    repeat rw [Set.singleton_def, insert] at hx hy
    dsimp [Set.instInsert] at hx hy
    repeat rw [deduction] at hx hy
    split_ands
    · let ψ := loose t i x → loose t i y
      have p1 := mono (Set.empty_subset {ψ}) hx.right
      have p2 := AS (Set.mem_singleton ψ)
      have p3 := mono (Set.empty_subset {ψ}) hy.left
      exact impl_trans (impl_trans p1 p2) p3
    · let ψ := x → y
      have p1 := mono (Set.empty_subset {ψ}) hx.left
      have p2 := AS (Set.mem_singleton ψ)
      have p3 := mono (Set.empty_subset {ψ}) hy.right
      exact impl_trans (impl_trans p1 p2) p3
  | fall j ψ h =>
    rcases h with ⟨p1, p2⟩
    let χ := ψ.loose t i
    let k := Freshable.fresh <| i :: (χ.varList ++ t.varList)
    have hk : k ∉ χ.vars := fun h => by
      rw [vars_eq_list] at h
      replace h := List.mem_append_left t.varList h
      replace h := List.mem_cons_of_mem i h
      exact Freshable.fresh_is_new _ h
    have hj : FreeFor j (.var k) χ := by
      apply term_FreeFor
      unfold Term.vars
      rw [Set.singleton_inter_eq_empty]
      exact hk
    split_ands
    · let χ' := χ.subst j (.var k) hj
      obtain ⟨h3, h4⟩ := subst_circulation j k χ hk
      have p3 := AX ∅ (.q2 k (.var j) χ' h3)
      dsimp [AxiomSchema.toFormula, FOLAxioms.toFormula] at p3
      rw [h4] at p3
      replace p3 := (deduction ..).mpr p3
      conv at p1 => rw [Set.singleton_def]; dsimp [insert]; rw [deduction]
      replace p1 := mono (Set.empty_subset <| Set.insert (∀k#χ') ∅) p1
      have h4 : j ∉ (∀k#χ').fvar := by
        unfold fvar
        rw [Set.mem_diff, Set.mem_singleton_iff, not_and, Decidable.not_not]
        intro hjk
        unfold χ' at hjk
        have h5 := Set.mem_of_mem_of_subset hjk <| subst_fvar ..
        unfold Term.vars at h5
        rw [Set.mem_union, Set.mem_singleton_iff, Set.mem_diff, Set.mem_singleton_iff] at h5
        simp only [not_true_eq_false, and_false, or_false] at h5
        exact h5
      rw [Set.singleton_def]; dsimp [insert]
      refine gen_rule _ _ _ ?_ (p1.mp p3)
      intro g hg
      dsimp [Set.insert] at hg
      replace hg := Or.resolve_right hg (Set.notMem_empty g)
      rw [hg]; exact h4
    · have p1 := impl_all_intro j p2
      have p2 := AX ∅ (.q2 j (.var k) χ hj)
      have p3 := (deduction ..).mpr p2
      replace p3 := gen_rule _ _ k (by
        intro g hg
        dsimp [Set.insert] at hg
        rw [Or.resolve_right hg <| Set.notMem_empty g]
        unfold fvar
        rw [Set.mem_diff, not_and, Set.mem_singleton_iff, Decidable.not_not]
        intro h; exfalso
        exact hk <| Set.mem_of_mem_of_subset h (fvar_subset_vars χ)
        ) p3
      replace p3 := (deduction ..).mp p3
      replace p3 := mono (Set.empty_subset {fall j ψ}) p3
      exact mp p3 p1
end Proof
end PrimaryLogic
