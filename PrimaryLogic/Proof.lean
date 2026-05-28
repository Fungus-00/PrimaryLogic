import PrimaryLogic.Vars

namespace PrimaryLogic

section theory
variable {LF LP : Type} {L : Lang LF LP} (α : outParam Type) [AxiomSchema L α]

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
  | axm (a : α) : Proof Γ (AxiomSchema.toFormula (L := L) a)
  | mp {φ ψ : Formula L} : Proof Γ (.impl φ ψ) → Proof Γ φ → Proof Γ ψ

inductive ProofTree (Γ : Set (Formula L)) : Formula L → Type
  | asp (φ) : φ ∈ Γ → ProofTree Γ φ
  | axm (a : α) : ProofTree Γ (AxiomSchema.toFormula (L := L) a)
  | mp {φ ψ : Formula L} : ProofTree Γ (.impl φ ψ) → ProofTree Γ φ → ProofTree Γ ψ

def ProofTree.toProof {Γ} (φ : Formula L) : ProofTree α Γ φ -> Proof α Γ φ
  | .asp φ h => .asp φ h
  | .axm a => .axm a
  | .mp p q => .mp (p.toProof) (q.toProof)

theorem Proof.hasTree {Γ} {φ : Formula L} : Proof α Γ φ -> Nonempty (ProofTree α Γ φ)
  | asp x h => .intro (.asp x h)
  | axm a => .intro (.axm a)
  | mp p1 p2 => match hasTree p1, hasTree p2 with
    | .intro t1, .intro t2 => .intro (.mp t1 t2)

def ProofTree.vars {Γ} {φ : Formula L} : ProofTree α Γ φ -> Finset Idx
  | asp .. | axm .. => φ.vars
  | mp px py => vars px ∪ vars py

variable (m : Mor L) (c : VarContext L m.p) (ma : MorAx m c)

structure AxiomTransform where
  pass : α → Prop
  transform : α → α
  pass_valid : ∀ a : α, (AxiomSchema.toFormula (L := L) a).av m.p
  invariance (a : α) :
      AxiomSchema.toFormula (L := L) (transform a) = m.f (AxiomSchema.toFormula (L := L) a)
/-
variable {T : AxiomTransform α m}
def ProofTree.transform {Γ φ} (hΓ : ∀ x ∈ Γ, x.av m.p) (hφ : φ.av m.p) :
  ProofTree α Γ φ -> ProofTree α (m.f '' Γ) (m.f φ)
  | axm a => cast (congrArg (ProofTree α _ ·) (T.invariance a)) <| .axm <| T.transform a
  | asp ψ h => .asp (m.f ψ) (Set.mem_image_of_mem m.f h)
  | mp (φ := x) (ψ := y) px py => .mp (ma.map_impl ▸ (transform sorry sorry px)) (transform py)
-/
section runtime

inductive ProofType : Type
  | asp : ProofType
  | axm : α -> ProofType
  | mp : Nat -> ProofType

abbrev ProofSeq {LF LP : Type} (L : Lang LF LP) (α : outParam Type) :=
  List ((ProofType α) × (Formula L))
variable {α : outParam Type} [AxiomSchema L α]

def ProofSeq.check [AxiomSchema L α] (Γ : Set (Formula L)) : ProofSeq L α -> Prop
  | [(.asp, φ)] => φ ∈ Γ
  | [(.axm a, φ)] => φ = AxiomSchema.toFormula (L := L) a
  | (.mp i, φ) :: s =>
    let s1 := s.take i
    let s2 := s.drop i
    check Γ s1 ∧ check Γ s2 ∧ match s1, s2 with
    | (_, ψ) :: _, (_, χ) :: _ => χ = .impl ψ φ
    | _, _ => False
  | _ => False
termination_by s => s.length

theorem ProofSeq.checked_ne_nil {Γ : Set (Formula L)} {s : ProofSeq L α} :
    s.check Γ → s ≠ [] := by
  intro h; by_contra; unfold check at h; rwa [this] at h

def ProofSeq.toTree {Γ} (s : ProofSeq L α) (h : s.check Γ) :
    ProofTree α Γ (s.head (checked_ne_nil h)).2 :=
  match hs : s with
  | [(.asp, φ)] => .asp φ (by unfold check at h; assumption)
  | [(.axm a, φ)] => by
    unfold check at h
    rw [List.head_singleton, h]
    exact .axm a
  | (.mp i, φ) :: as => by
    unfold check at h
    obtain ⟨h1, h2, h3⟩ := h
    match h4 : List.take i as, h5 : List.drop i as with
    | (t1, ψ) :: s1, (t2, χ) :: s2 =>
      rw [h4, h5] at h3
      dsimp at h3
      have h6 := h3 ▸ h5
      have p1 := toTree ((t1, ψ) :: s1) (h4 ▸ h1)
      have p2 := toTree ((t2, _) :: s2) (h6 ▸ h2)
      exact .mp p2 p1
    | [], [] | [], _ | _ :: _, [] => exfalso; rwa [h4, h5] at h3
  | [] | (.asp, _) :: _ :: _ | (.axm _, _) :: _ :: _ =>
    by unfold check at h; contradiction
termination_by s.length
decreasing_by
  open List in
  constructor
  · have d1 := congrArg length h5
    have d2 := congrArg length (take_append_drop i as)
    rw [length] at d1
    rw [length_append] at d2
    rw [←h4, ←d2, d1, ←Nat.add_one]
    simp [length_take]
  · rw [←h6, length, length_drop]
    apply Nat.lt_of_le_of_lt (Nat.sub_le as.length i)
    exact Nat.lt_add_right_iff_pos.mpr (by decide)

def ProofTree.toSeq {Γ} {φ : Formula L} : ProofTree α Γ φ -> ProofSeq (L := L) α
  | asp x _ => [(.asp, x)]
  | axm a => [(.axm a, AxiomSchema.toFormula a)]
  | mp (ψ := y) p1 p2 =>
    let s := p2.toSeq
    (.mp s.length, y) :: s ++ p1.toSeq

open ProofSeq in
theorem ProofTree.toSeq_checked {Γ} {φ : Formula L} (p : ProofTree α Γ φ) :
    ∃ h : p.toSeq.check Γ, (p.toSeq.head (checked_ne_nil h)).2 = φ := by
  induction hp : p with
  | asp x h1 =>
    unfold toSeq check; use h1; eq_refl
  | axm a =>
    unfold toSeq check; use rfl; eq_refl
  | @mp x y px py hx hy =>
    obtain ⟨h1, h2⟩ := hx px rfl
    obtain ⟨h3, h4⟩ := hy py rfl
    refine ⟨?_, rfl⟩
    unfold toSeq check
    dsimp
    open List in
    rw [take_append, drop_append, Nat.sub_self, take_zero, drop_zero,
      take_of_length_le (Nat.le_refl _), drop_of_length_le (Nat.le_refl _), append_nil, nil_append]
    refine ⟨h3, h1, ?_⟩
    match h5 : py.toSeq, h6 : px.toSeq with
    | (_, ψ) :: _, (_, χ) :: _ =>
      conv at h2 => enter [1, 1, 1]; rw [h6]
      conv at h4 => enter [1, 1, 1]; rw [h5]
      dsimp at *
      rwa [←h4] at h2
    | [], _  => rw [h5] at h3; unfold check at h3; contradiction
    | _, [] => rw [h6] at h1; unfold check at h1; contradiction

def ProofSeq.allVars (σ : ProofSeq L α) : Finset Idx :=
  (σ.map (·.2.vars) |> List.toFinset).biUnion id

lemma ProofSeq.fresh_not_mem_vars {α : Type} (σ : ProofSeq L α) :
    ∀ k : Fin σ.length, Freshable.fresh σ.allVars ∉ σ[k].2.vars := by
  intro n
  suffices h : σ[n].2.vars ⊆ σ.allVars by
    apply Finset.not_mem_subset h
    apply Freshable.fresh_is_new
  dsimp only [allVars]
  intro k h
  simp only [Finset.mem_biUnion, List.mem_toFinset, id]
  use σ[n].2.vars
  constructor
  · rw [List.mem_map]; use σ[n]
    exact ⟨List.getElem_mem n.prop, rfl⟩
  · exact h

end runtime

def Inconsistent (Γ : Set (Formula L)) : Prop := Proof α Γ .falsum
abbrev Consistent (Γ : Set (Formula L)) : Prop := ¬ Inconsistent α Γ

theorem Proof.monotone {α : outParam Type} [AxiomSchema L α] {Γ Δ} {φ : Formula L} :
  Γ ⊆ Δ -> Proof α Γ φ -> Proof α Δ φ := fun h p =>
  match p with
  | asp ψ hi => asp ψ (h hi)
  | axm a => axm a
  | mp p1 p2 => mp (p1.monotone h) (p2.monotone h)

def Theory (L : Lang LF LP) := Set (Sentence L)

end theory

end PrimaryLogic
