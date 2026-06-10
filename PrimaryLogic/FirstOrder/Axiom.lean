import PrimaryLogic.Proof
import PrimaryLogic.Vars

namespace PrimaryLogic
variable {LF LP : Type}

/--
- `h1`: Positive Implication
- `h2`: Distribution of Implication
- `h3`: Elimination of Double Negation
- `q1`: Universal Distribution
- `q2`: Universal Instantiation
- `q3`: Universal Introduction
- `gen`: Universal Generalization
-/
inductive FOLAxioms (L : Lang LF LP) : Type
  | h1 : Formula L -> Formula L -> FOLAxioms L
  | h2 : Formula L -> Formula L -> Formula L -> FOLAxioms L
  | h3 : Formula L -> FOLAxioms L
  | q1 : Idx -> Formula L -> Formula L -> FOLAxioms L
  | q2 (i : Idx) (t : Term L) (φ : Formula L) : φ.FreeFor i t -> FOLAxioms L
  | q3 (i : Idx) (φ : Formula L) : i ∉ φ.fvar -> FOLAxioms L
  | gen : Idx -> FOLAxioms L -> FOLAxioms L

variable {L : Lang LF LP}
def FOLAxioms.toFormula : FOLAxioms L -> Formula L
  | .h1 φ ψ => .impl φ (.impl ψ φ)
  | .h2 φ ψ χ => .impl (.impl φ (.impl ψ χ)) (.impl (.impl φ ψ) (.impl φ χ))
  | .h3 φ => .impl (.impl (.impl φ .falsum) .falsum) φ
  | .q1 i φ ψ => .impl (.fall i (.impl φ ψ)) (.impl (.fall i φ) (.fall i ψ))
  | .q2 i t φ h => .impl (.fall i φ) (φ.subst i t h)
  | .q3 i φ _ => .impl φ (.fall i φ)
  | .gen i a => .fall i (toFormula a)

def FOLAxioms.vars (a : FOLAxioms L) : Set Idx :=
  match a with
  | .h1 φ ψ => φ.vars ∪ ψ.vars
  | .h2 φ ψ χ => φ.vars ∪ (ψ.vars ∪ χ.vars)
  | .h3 φ => φ.vars
  | .q1 i φ ψ => insert i (φ.vars ∪ ψ.vars)
  | .q2 i t φ _ => insert i (t.vars ∪ φ.vars)
  | .q3 i φ _ => insert i φ.vars
  | .gen i a => insert i a.vars

private lemma Set.XYXZ {α : Type*} {x y z : Set α} : (x ∪ y) ∪ (x ∪ z)  = x ∪ (y ∪ z) := by
  ext a; simp only [Set.mem_union]; aesop

lemma FOLAxioms.toFormula_vars_subset (a : FOLAxioms L) :
    (a.toFormula).vars ⊆ a.vars := by
  induction a with
  | h1 φ ψ =>
    dsimp [toFormula, vars, Formula.vars]
    conv => lhs; rw [←Set.union_assoc, Set.union_comm, ←Set.union_assoc, Set.union_self]
  | h2 φ ψ χ =>
    dsimp [toFormula, vars, Formula.vars]
    conv => lhs; rw [Set.XYXZ, Set.union_self]
  | h3 φ =>
    dsimp [toFormula, vars, Formula.vars]
    conv => lhs; rw [Set.union_empty, Set.union_empty, Set.union_self]
  | q1 i φ ψ =>
    dsimp [toFormula, vars, Formula.vars]
    conv => lhs; rw [←Set.insert_union_distrib', ←Set.insert_union_distrib', Set.union_self]
  | q2 i t φ h =>
    dsimp [toFormula, vars, Formula.vars]
    rw [Set.union_subset_iff]
    split_ands
    · apply Set.insert_subset_insert'
      exact Set.subset_union_right
    · exact subset_trans (Formula.subst_vars h) (Set.subset_insert ..)
  | q3 i φ h =>
    dsimp [toFormula, vars, Formula.vars]
    rw [Set.union_insert', Set.union_self]
  | gen i φ h =>
    dsimp [toFormula, vars, Formula.vars]
    exact Set.insert_subset_insert' h

def FOLAxioms.varList : FOLAxioms L -> List Idx
  | .h1 φ ψ => φ.varList ++ ψ.varList
  | .h2 φ ψ χ => φ.varList ++ (ψ.varList ++ χ.varList)
  | .h3 φ => φ.varList
  | .q1 i φ ψ => i :: (φ.varList ++ ψ.varList)
  | .q2 i t φ _ => i :: (t.varList ++ φ.varList)
  | .q3 i φ _ => i :: φ.varList
  | .gen i a => i :: a.varList

lemma FOLAxioms.vars_eq_list (a : FOLAxioms L) (j : Idx) : j ∈ a.vars ↔ j ∈ a.varList := by
  induction a with
  | h1 | h2 | h3 =>
    unfold vars varList
    simp only [Set.mem_union, List.mem_append, Formula.vars_eq_list]
  | q1 i φ ψ =>
    unfold vars varList
    rw [Set.mem_insert_iff, Set.mem_union, List.mem_cons, List.mem_append,
      Formula.vars_eq_list, Formula.vars_eq_list]
  | q2 i t φ h =>
    unfold vars varList
    rw [Set.mem_insert_iff, Set.mem_union, List.mem_cons, List.mem_append,
      Formula.vars_eq_list, Term.vars_eq_list]
  | q3 i φ h =>
    unfold vars varList
    rw [Set.mem_insert_iff, Formula.vars_eq_list, List.mem_cons]
  | gen i a h =>
    unfold vars varList
    rw [Set.mem_insert_iff, List.mem_cons, h]

theorem FOLAxioms.subset_varList (a : FOLAxioms L) : a.toFormula.varList ⊆ a.varList :=
  fun i h => (vars_eq_list a i).mp <| toFormula_vars_subset a <| (Formula.vars_eq_list ..).mpr h

instance : AxiomSchema L (FOLAxioms L) :=
  ⟨FOLAxioms.toFormula, FOLAxioms.varList, FOLAxioms.subset_varList⟩

def Formula.not (φ : Formula L) : Formula L := φ.impl .falsum
def Formula.or (φ ψ : Formula L) : Formula L := φ.not.impl ψ
def Formula.and (φ ψ : Formula L) : Formula L := (φ.impl ψ.not).not
def Formula.iff (φ ψ : Formula L) : Formula L := (φ.impl ψ).and (ψ.impl φ)
def Formula.ex (i : Idx) (φ : Formula L) : Formula L := (Formula.fall i φ.not).not

notation "⊥" => Formula.falsum
infixr:25 " ↔ " => Formula.iff
infixr:30 " → " => Formula.impl
infixl:45 " ∧ " => Formula.and
infixl:40 " ∨ " => Formula.or
prefix:50 "¬" => Formula.not
-- Making `#` instead of `,` as the placeholder behind quantifier and index is to distinguish from
-- their usage in `Prop` type context.
macro "∀" i:ident "# " φ:term : term => `(Formula.fall $i $φ)
macro "∃" i:ident "# " φ:term : term => `(Formula.ex $i $φ)
abbrev FOLTheory := instAxiomSchemaFOLAxioms.toSet (L := L)
abbrev FOLProof (Γ : Set (Formula L)) := Proof (L := L) (Γ ∪ FOLTheory)
infix:20 " ⊢ " => FOLProof

namespace FOL
@[simp]
theorem mem_theory_iff (φ : Formula L) : φ ∈ FOLTheory ↔ ∃ a : FOLAxioms L, a.toFormula = φ := by
  unfold FOLTheory AxiomSchema.toSet AxiomSchema.toFormula instAxiomSchemaFOLAxioms
  dsimp; rw [Set.mem_range]

theorem axiom_proof {Γ : Set (Formula L)} {φ : Formula L} : φ ∈ FOLTheory -> (Γ ⊢ φ) :=
  fun h => Proof.asp φ <| (Set.mem_union ..).mpr (.inr h)

theorem mono {Γ Δ} {φ : Formula L} : Γ ⊆ Δ -> FOLProof Γ φ -> FOLProof Δ φ :=
  fun h p => Proof.monotone (Set.union_subset_union_left _ h) p

def AX (Γ : Set (Formula L)) (a : FOLAxioms L) : (FOLProof Γ a.toFormula) :=
  .asp a.toFormula (by rw [Set.mem_union, mem_theory_iff]; right; use a)

def AS {Γ : Set (Formula L)} {φ : Formula L} (h : φ ∈ Γ) : FOLProof Γ φ :=
  .asp φ ((Set.mem_union ..).mpr (Or.inl h))
end FOL

variable {m : Mor L} (η : (c : VarContext L m.p) → MorAx m c)

private lemma falsum_av : Formula.av (L := L) ⊥ m.p :=
  fun i h => False.elim (Set.notMem_empty i h)

-- get MorAx
def FOLAxioms.gm {m : Mor L} (η : (c : VarContext L m.p) → MorAx m c)
  (j : Σ' i : Idx, m.p i := ⟨m.d, m.pd⟩)
  (s : Σ' t : Term L, t.vars ⊆ m.p := ⟨.var m.d, fun _ h => Set.mem_singleton_iff.mp h ▸ m.pd⟩)
  (x : Σ' φ : Formula L, φ.vars ⊆ m.p := ⟨⊥, falsum_av⟩)
  (y : Σ' ψ : Formula L, ψ.vars ⊆ m.p := ⟨⊥, falsum_av⟩)
  := η ⟨j.1, s.1, x.1, y.1, j.2, s.2, x.2, y.2⟩

def FOLAxioms.transform (a : FOLAxioms L) (ha : a.vars ⊆ m.p) : FOLAxioms L :=
  match a with
  | .h1 φ ψ => .h1 (m.f φ) (m.f ψ)
  | .h2 φ ψ χ => .h2 (m.f φ) (m.f ψ) (m.f χ)
  | .h3 φ => .h3 (m.f φ)
  | .q1 i φ ψ => .q1 (m.ι i) (m.f φ) (m.f ψ)
  | .q2 i t φ h => q2 (m.ι i) (m.τ t) (m.f φ) <|
    have h' := Set.insert_subset_iff'.mp ha
    have g := Set.union_subset_iff.mp h'.2
    (η ⟨i, t, φ, ⊥, h'.1, g.1, g.2, falsum_av⟩).free_for h
  | .q3 i φ h => .q3 (m.ι i) (m.f φ) <|
    have h' := Set.insert_subset_iff'.mp ha
    (gm η (j := ⟨i, h'.1⟩) (x := ⟨φ, h'.2⟩)).free_var h
  | .gen i a => .gen (m.ι i) <| transform a <| (Set.insert_subset_iff'.mp ha).2

theorem FOLAxioms.transform_eq (a : FOLAxioms L) (h : a.vars ⊆ m.p) :
    m.f a.toFormula = (a.transform η h).toFormula := by
  induction a with
  | h1 φ ψ =>
    dsimp [toFormula, transform]
    have hb := Set.union_subset_iff.mp h
    have c1 := gm η (x := ⟨φ, hb.1⟩) (y := ⟨ψ → φ, by
      unfold Formula.vars; rw [Set.union_comm]; exact h⟩)
    have c2 := gm η (x := ⟨ψ, hb.2⟩) (y := ⟨φ, hb.1⟩)
    rw [c1.map_impl, c2.map_impl]
  | h2 φ ψ χ =>
    dsimp [toFormula, transform]
    have c1 := gm η (x := ⟨φ → ψ → χ, h⟩) (y := ⟨(φ → ψ) → φ → χ, by
      simp only [Formula.vars, Set.XYXZ]; simpa only [vars] using h⟩)
    unfold vars at h; rw [Set.union_subset_iff] at h
    have c2 := gm η (x := ⟨φ, h.1⟩) (y := ⟨ψ → χ, h.2⟩)
    rw [Set.union_subset_iff] at h
    have c3 := gm η (x := ⟨ψ, h.2.1⟩) (y := ⟨χ, h.2.2⟩)
    have c4 := gm η (x := ⟨φ → ψ, Set.union_subset_iff.mpr ⟨h.1, h.2.1⟩⟩)
      (y := ⟨φ → χ, Set.union_subset_iff.mpr ⟨h.1, h.2.2⟩⟩)
    have c5 := gm η (x := ⟨φ, h.1⟩) (y := ⟨ψ, h.2.1⟩)
    have c6 := gm η (x := ⟨φ, h.1⟩) (y := ⟨χ, h.2.2⟩)
    rw [c1.map_impl, c2.map_impl, c3.map_impl, c4.map_impl, c5.map_impl, c6.map_impl]
  | h3 φ =>
    dsimp [toFormula, transform]
    unfold vars at h
    have c1 := gm η (x := ⟨(φ → ⊥) → ⊥, by simp [Formula.vars, Set.union_empty, h]⟩) (y := ⟨φ, h⟩)
    have c2 := gm η (x := ⟨φ → ⊥, by simp [Formula.vars, Set.union_empty, h]⟩)
    have c3 := gm η (x := ⟨φ, h⟩)
    rw [c1.map_impl, c2.map_impl, c3.map_impl, c3.map_falsum]
  | q1 i φ ψ =>
    dsimp [toFormula, transform]
    unfold vars at h
    have c1 := gm η (x := ⟨∀i#(φ → ψ), h⟩) (y := ⟨(∀i#φ) → (∀i#ψ), by
      simp only [Formula.vars]; rw [←Set.insert_union_distrib']; exact h⟩)
    have hb := Set.insert_subset_iff'.mp h
    let ix : Σ' j : Idx, m.p j := ⟨i, hb.1⟩
    have c2 := gm η (j := ix) (x := ⟨φ → ψ, hb.2⟩)
    rw [Set.union_subset_iff] at hb
    have c3 := gm η (x := ⟨φ, hb.2.1⟩) (y := ⟨ψ, hb.2.2⟩)
    rw [Set.insert_union_distrib', Set.union_subset_iff] at h
    have c4 := gm η (x := ⟨∀i#φ, h.1⟩) (y := ⟨∀i#ψ, h.2⟩)
    have c5 := gm η (j := ix) (x := ⟨φ, hb.2.1⟩)
    have c6 := gm η (j := ix) (x := ⟨ψ, hb.2.2⟩)
    rw [c1.map_impl, c2.map_fall, c3.map_impl, c4.map_impl, c5.map_fall, c6.map_fall]
  | q2 i t φ h' =>
    dsimp [toFormula, transform]
    unfold vars at h
    have g := Set.union_subset_iff.mp <| (Set.insert_union_distrib' ..) ▸ h
    rw [Set.insert_subset_iff'] at h
    have c1 := gm η (x := ⟨∀i#φ, g.2⟩)
      (y := ⟨Formula.subst i t φ h', subset_trans (Formula.subst_vars h') h.2⟩)
    rw [Set.union_subset_iff] at h
    have c2 := gm η (j := ⟨i, h.1⟩) (x := ⟨φ, h.2.2⟩)
    have c3 := η ⟨i, t, φ, ⊥, h.1, h.2.1, h.2.2, falsum_av⟩
    rw [c1.map_impl, c2.map_fall, c3.map_subst]
  | q3 i φ h' =>
    dsimp [toFormula, transform]
    have g := Set.insert_subset_iff'.mp h
    have c1 := gm η (x := ⟨φ, g.2⟩) (y := ⟨∀i#φ, h⟩)
    have c2 := gm η (j := ⟨i, g.1⟩) (x := ⟨φ, g.2⟩)
    rw [c1.map_impl, c2.map_fall]
  | gen i a h' =>
    dsimp [toFormula, transform]
    unfold vars at h
    rw [Set.insert_subset_iff'] at h
    have h1 := subset_trans (toFormula_vars_subset a) h.2
    have c := gm η (j := ⟨i, h.1⟩) (x := ⟨a.toFormula, h1⟩)
    rw [c.map_fall, h']
end PrimaryLogic
