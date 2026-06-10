import PrimaryLogic.Formula

namespace PrimaryLogic

variable {LF LP : Type} {L : Lang LF LP}

class AxiomSchema (L : Lang LF LP) (α : Type) where
  toFormula : α -> Formula L
  varList : α → List Idx
  subset_varList (a : α) : (toFormula a).varList ⊆ varList a

def AxiomSchema.toSet (α : Type) [AxiomSchema L α] : Set (Formula L) :=
  Set.range <| AxiomSchema.toFormula (L := L) (α := α)

/-- `Proof` type is designed for meta theorem proving, and note that is cannot recall subproofs,
  yet `ProofTree` retains them.
`ProofSequence` preorderly traverse the ProofTree, whose theory is not that completed
  as it hasn't been applied yet.

There are two kinds of mainstream FOL theory.
  One intro Gen inference rule, the other intro gen as axiom schemas
  (`.gen` and `.q3` in `FOLAxioms`).
I prefer the second one, as it is easier to prove certain meta theorems,
  without annoyance of checking Gen rule in pattern matching.
Under this circumstance, `.gen` becomes an axiom schema ensuring that an axiom in open formula form
  is equivalent to its closed form (generalized by universal quantifier),
  where the former is flexible to write machine proof, while the latter,
  requiring any axiom to be sentence, guarantees the strictness of traditional logic theory.

- `asp`: assumption
- `axm`: axiom (schema),
  I haven't named it "axiom" for the consideration of confiction with Lean4 keyword.
- `mp`: the unique inference rule
-/
inductive Proof (Γ : Set (Formula L)) : Formula L → Prop
  | asp (φ) : φ ∈ Γ → Proof Γ φ
  | mp {φ ψ : Formula L} : Proof Γ (.impl φ ψ) → Proof Γ φ → Proof Γ ψ

variable (α : Type) [AxiomSchema L α]

inductive ProofTree (Γ : Set (Formula L)) : Formula L → Type
  | asp (φ) : φ ∈ Γ → ProofTree Γ φ
  | axm (a : α) : ProofTree Γ (AxiomSchema.toFormula a)
  | mp {φ ψ : Formula L} : ProofTree Γ (.impl φ ψ) → ProofTree Γ φ → ProofTree Γ ψ

theorem Proof.hasTree {Γ} {φ : Formula L} :
    Proof (Γ ∪ AxiomSchema.toSet α) φ -> Nonempty (ProofTree α Γ φ)
  | asp x h' => Or.elim h' (fun h => .intro (.asp x h))
    fun h => let ⟨a, ha⟩ := Set.mem_range.mp h; .intro (ha ▸ .axm a)
  | mp p1 p2 => match hasTree p1, hasTree p2 with
    | .intro t1, .intro t2 => .intro (.mp t1 t2)

variable {α : Type} [AxiomSchema L α]
theorem ProofTree.toProof {Γ} (φ : Formula L) : ProofTree α Γ φ -> Proof (Γ ∪ AxiomSchema.toSet α) φ
  | .asp φ h => .asp φ <| Or.inl <| h
  | .axm a => .asp (AxiomSchema.toFormula a) <| Or.inr (by
    simp only [AxiomSchema.toSet, Set.mem_range, exists_apply_eq_apply])
  | .mp p q => .mp (p.toProof) (q.toProof)

def ProofTree.varList {Γ} {φ : Formula L} : ProofTree α Γ φ -> List Idx
  | asp x _ => x.varList
  | axm a => AxiomSchema.varList L a
  | mp px py => varList px ++ varList py

lemma ProofTree.mem_target_varList {Γ φ} (t : ProofTree α Γ φ) :
    φ.varList ⊆ t.varList (L := L) := by
  intro h
  induction t with
  | asp x _ => unfold varList; intro v; exact v
  | axm a => unfold varList; intro v; exact AxiomSchema.subset_varList a v
  | @mp x y p1 p2 h1 h2 =>
    unfold varList; unfold Formula.varList at h1
    rw [List.mem_append] at h1 ⊢
    intro h3
    exact .inl <| h1 (.inr h3)

def ProofTree.assumptions {Γ} {φ : Formula L} : ProofTree α Γ φ -> Set (Formula L)
  | asp x _ => {x}
  | axm _ => ∅
  | mp x y => assumptions x ∪ assumptions y

lemma ProofTree.assumptions_subset {Γ} {φ : Formula L} (t : ProofTree α Γ φ) :
    t.assumptions ⊆ Γ := by
  induction t with
  | asp x h => exact Set.singleton_subset_iff.mpr h
  | axm => exact Set.empty_subset Γ
  | mp x y hx hy => exact Set.union_subset hx hy

lemma ProofTree.assumptions_vars_subset {Γ} {φ : Formula L} (t : ProofTree α Γ φ) :
    ∀ x ∈ t.assumptions, x.varList ⊆ t.varList := by
  intro ψ hi
  induction t with
  | asp x h =>
    unfold varList; unfold assumptions at hi
    rw [Set.mem_singleton_iff] at hi; rw [hi]; apply List.Subset.refl
  | axm a => exfalso; exact Set.notMem_empty ψ hi
  | mp x y hx hy =>
    unfold varList
    rcases hi with h | h
    · exact List.subset_append_of_subset_left _ (hx h)
    · exact List.subset_append_of_subset_right _ (hy h)

def Inconsistent (Γ : Set (Formula L)) : Prop := Proof Γ .falsum
abbrev Consistent (Γ : Set (Formula L)) : Prop := ¬ Inconsistent Γ

theorem Proof.monotone {Γ Δ} {φ : Formula L} :
  Γ ⊆ Δ -> Proof Γ φ -> Proof Δ φ := fun h p =>
  match p with
  | asp ψ hi => asp ψ (h hi)
  | mp p1 p2 => mp (p1.monotone h) (p2.monotone h)

def ProofTree.monotone {Γ Δ} {φ : Formula L} :
  Γ ⊆ Δ -> ProofTree α Γ φ -> ProofTree α Δ φ := fun h p =>
  match p with
  | asp ψ hi => asp ψ (h hi)
  | axm a => axm a
  | mp p1 p2 => mp (p1.monotone h) (p2.monotone h)

lemma ProofTree.monotone_varList_eq {Γ Δ} {φ : Formula L} (t : ProofTree α Γ φ) (h : Γ ⊆ Δ) :
    (t.monotone h).varList = t.varList := by
  induction t with
  | asp | axm => rfl
  | mp x y hx hy => unfold monotone varList; rw [hx, hy]

def ProofTree.compress {Γ} {φ : Formula L} (t : ProofTree α Γ φ) :
    ProofTree α (t.assumptions) φ :=
  match t with
  | .asp x h => asp x (Set.mem_singleton _)
  | .axm a => axm a
  | .mp px py => mp
    (monotone Set.subset_union_left <| compress px)
    (monotone Set.subset_union_right <| compress py)

theorem ProofTree.compress_varList_eq {Γ} {φ : Formula L} (t : ProofTree α Γ φ) :
    t.compress.varList = t.varList := by
  induction t with
  | asp | axm => rfl
  | mp x y px py =>
    unfold compress varList
    rw [monotone_varList_eq, monotone_varList_eq, px, py]

def Theory (L : Lang LF LP) := Set (Sentence L)

end PrimaryLogic
