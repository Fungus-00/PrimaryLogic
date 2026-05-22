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
  | q3 (i : Idx) (φ : Formula L) : i ∉ φ.fVars -> FOLAxioms L
  | gen : Idx -> FOLAxioms L -> FOLAxioms L

def FOLAxioms.toFormula (L : Lang LF LP) : FOLAxioms L -> Formula L
  | .h1 φ ψ => .impl φ (.impl ψ φ)
  | .h2 φ ψ χ => .impl (.impl φ (.impl ψ χ)) (.impl (.impl φ ψ) (.impl φ χ))
  | .h3 φ => .impl (.impl (.impl φ .falsum) .falsum) φ
  | .q1 i φ ψ => .impl (.fall i (.impl φ ψ)) (.impl (.fall i φ) (.fall i ψ))
  | .q2 i t φ h => .impl (.fall i φ) (φ.subst i t h)
  | .q3 i φ _ => .impl φ (.fall i φ)
  | .gen i a => .fall i (toFormula L a)

variable {L : Lang LF LP}

instance : AxiomSchema L (FOLAxioms L) := ⟨FOLAxioms.toFormula L⟩

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
abbrev FOLProof := Proof (L := L) (FOLAxioms L)
infix:20 " ⊢ " => FOLProof

variable {c : LF} {s : Finset Idx} (m : Formula.axiomMor L c s)

def FOLAxioms.transform (a : FOLAxioms L) : a.toFormula.vars ⊆ s → FOLAxioms L :=
  fun h' => open Formula in match a with
  | .h1 φ ψ => .h1 (m.f φ) (m.f ψ)
  | .h2 φ ψ χ => .h2 (m.f φ) (m.f ψ) (m.f χ)
  | .h3 φ => .h3 (m.f φ)
  | .q1 i φ ψ => .q1 i (m.f φ) (m.f ψ)
  | .q2 i t φ h =>
    have h1 : i ∈ s ∧ φ.vars ⊆ s := by
      simp only [toFormula, vars, Finset.union_subset_iff, Finset.insert_subset_iff] at h'
      exact h'.left
    .q2 i (m.τ t) (m.f φ) <| m.free_for h h1.left <|
      subset_trans (bVars_subset_vars φ) h1.right
  | .q3 i φ h =>
    have h1 : i ∈ s ∧ φ.vars ⊆ s := by
      simp only [toFormula, vars, Finset.union_subset_iff, Finset.insert_subset_iff] at h'
      exact h'.right
    .q3 i (m.f φ) (m.free_var h h1.left h1.right)
  | .gen i a => .gen i <| transform a (by
    simp only [toFormula, vars, Finset.insert_subset_iff] at h'; exact h'.right)

theorem FOLAxioms.transform_eq (a : FOLAxioms L) (h' : a.toFormula.vars ⊆ s) :
    (transform m a h').toFormula = m.f a.toFormula := by
  unfold toFormula transform
  open Formula in
  cases a with
  | h1 φ ψ => dsimp; repeat rw [m.map_impl]
  | h2 φ ψ χ => dsimp; repeat rw [m.map_impl]
  | h3 φ => simp only [m.map_impl, m.map_falsum]
  | q1 i φ ψ => simp only [m.map_impl, m.map_fall]
  | q2 i t φ h =>
    simp only [m.map_impl, m.map_fall, impl.injEq, true_and];
    simp only [toFormula, vars, Finset.union_subset_iff, Finset.insert_subset_iff] at h'
    symm; apply m.subst_comm
    · exact h'.left.left
    · trans φ.vars
      · exact bVars_subset_vars φ
      · exact h'.left.right
  | q3 i φ h => dsimp; rw [m.map_impl, m.map_fall]
  | gen i a =>
    dsimp; rw [m.map_fall, fall.injEq]
    simp only [toFormula, vars, Finset.insert_subset_iff] at h'
    exact ⟨rfl, transform_eq a h'.right⟩

instance : AxiomTransform (FOLAxioms L) m where
  transform := FOLAxioms.transform m
  invariance := FOLAxioms.transform_eq m

end PrimaryLogic
