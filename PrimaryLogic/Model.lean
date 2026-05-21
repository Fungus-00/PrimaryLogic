import PrimaryLogic.Formula
import PrimaryLogic.Vars

namespace PrimaryLogic

variable {LF LP : Type} {L : Lang LF LP} {α : Type} [Inhabited α]

@[ext]
structure Structure (L : Lang LF LP) (α : Type) [Inhabited α] : Type where
  funMap : (n : LF) -> (Fin (L.funcs n) -> α) -> α
  relMap : (n : LP) -> (Fin (L.preds n) -> α) -> Prop

def Term.interpret (M : Structure L α) (s : Assignment α) : Term L -> α
  | .var i => s i
  | .app n args => M.funMap n fun i => (args i).interpret M s

def Formula.interpret (M : Structure L α) (s : Assignment α) : Formula L -> Prop
  | .atom n args => M.relMap n fun i => (args i).interpret M s
  | .falsum => False
  | .impl φ ψ => (φ.interpret M s) → (ψ.interpret M s)
  | .fall i φ => ∀ a : α, φ.interpret M (replace s i a)

def Structure.satisfies (M : Structure L α) (Γ : Set (Formula L)) (φ : Formula L) : Prop :=
  ∀ s : Assignment α, (∀ g ∈ Γ, g.interpret M s) -> φ.interpret M s

abbrev Structure.models (M : Structure L α) (φ : Formula L) : Prop := M.satisfies ∅ φ

abbrev Structure.modelsOf (M : Structure L α) (Γ : Set (Formula L)) := ∀ g : Γ, M.models g

@[simp]
theorem Structure.models_reduce (M : Structure L α) (φ : Formula L) :
    M.models φ <-> ∀ s : Assignment α, φ.interpret M s := by
  unfold models; unfold Structure.satisfies; simp [Set.mem_empty_iff_false]

def SemanticConsequence (Γ : Set (Formula L)) (φ : Formula L) : Prop :=
  ∀ (α : Type) [Inhabited α] (M : Structure L α), M.satisfies Γ φ
infix:20 " ⊨ " => SemanticConsequence

lemma SemanticConsequence.monotone {Γ Δ} (φ : Formula L) :
    Γ ⊆ Δ -> (Γ ⊨ φ) -> (Δ ⊨ φ) :=
  fun h0 h1 β _ M s h2 =>
    (h1 β M) s fun g hg => h2 g (Set.mem_of_subset_of_mem h0 hg)

abbrev Formula.valid (φ : Formula L) := SemanticConsequence ∅ φ
prefix:21 "⊨ " => Formula.valid

def Satisfiable (Γ : Set (Formula L)) : Prop :=
  ∃ (α : Type) (_ : Inhabited α) (M : Structure L α) (s : Assignment α),
  ∀ g ∈ Γ, g.interpret M s

def Mod (Γ : Set (Formula L)) (α : Type) [Inhabited α] := { M : Structure L α // M.modelsOf Γ }

def ModAll (Γ : Set (Formula L)) : Type 1 := Σ (β : Type), Σ (_ : Inhabited β), Mod Γ β

def DefinableSet (M : Structure L α) (φ : Formula L) := { s : Assignment α // φ.interpret M s }

def Structure.definableSets (M : Structure L α) : Set (Set (Assignment α)) :=
  { S | ∃ φ, S = DefinableSet M φ }
section interpret

lemma Term.interpret_coincidence (M) {x : Term L} {s t : Assignment α} :
    (∀ i ∈ x.vars, s i = t i) -> x.interpret M s = x.interpret M t := by
  intro hx
  induction x with
  | var i =>
    unfold Term.interpret
    exact hx i (Finset.mem_singleton_self i)
  | app m ms f =>
    unfold Term.interpret
    simp only [vars, Finset.mem_biUnion, Finset.mem_univ, true_and, forall_exists_index] at hx
    conv =>
      lhs; arg 3; intro fi
      exact f fi fun i hi => hx i fi hi

lemma Term.interpret_replace_invariance
    (M) {t : Term L} (s : Assignment α) (a : α) {i : Idx} :
    i ∉ t.vars -> t.interpret M (replace s i a) = t.interpret M s := by
  intro hi
  apply interpret_coincidence M
  simp only [ite_eq_right_iff]
  intro j hj h
  rw [h] at hj
  exfalso
  exact hi hj

theorem Formula.interpret_coincidence (M) {φ : Formula L} (s t : Assignment α) :
    (∀ i ∈ φ.fVars, s i = t i) -> (φ.interpret M s <-> φ.interpret M t) := by
  intro h
  induction φ generalizing s t with
  | atom n ns =>
    unfold interpret
    simp only [fVars, Finset.mem_biUnion, Finset.mem_univ, true_and, forall_exists_index] at h
    conv =>
      lhs; arg 3; intro fi;
      exact Term.interpret_coincidence M fun i hi => h i fi hi
  | falsum => unfold interpret; decide
  | impl φ ψ ha hb =>
    unfold interpret
    simp only [fVars, Finset.mem_union] at h
    have h1 := ha s t fun i hi => h i (.inl hi)
    have h2 := hb s t fun i hi => h i (.inr hi)
    rw [h1, h2]
  | fall i φ hi =>
    unfold interpret
    simp only [fVars, Finset.mem_erase, ne_eq, and_imp] at h
    have : ∀ a : α, ∀ j ∈ φ.fVars,
        (replace s i a) j = (replace t i a) j := by
      intro a j hj
      by_cases h' : j = i <;> simp only [replace, h', ↓reduceIte]; exact h j h' hj
    conv => lhs; intro a; rw [hi _ _ (this a)]

theorem Formula.interpret_replace_invariance
    (M : Structure L α) {φ : Formula L} (s : Assignment α) (a : α) {i : Idx} :
    i ∉ φ.fVars -> (φ.interpret M (replace s i a) <-> φ.interpret M s) := by
  intro hi
  apply interpret_coincidence M
  simp only [ite_eq_right_iff]
  intro j hj h
  rw [h] at hj
  exfalso; exact hi hj

/-- Classical needed -/
theorem Structure.sentence_determinacy (M) (φ : Formula L) : φ.fVars = ∅ ->
    (∀ s : Assignment α, φ.interpret M s) ∨ (∀ s : Assignment α, ¬ φ.interpret M s) := by
  intro h0
  let s0 : Assignment α := fun _ => Inhabited.default (α := α)
  have := Formula.interpret_coincidence M (φ := φ) s0
  by_cases h : φ.interpret M s0
  · left; intro s; exact (this s (by simp [h0])).mp h
  · right; intro s; exact (Iff.not (this s (by simp [h0]))).mp h

/-- The following two theorems show that the sentence makes no essential difference from
  unclosed formula in the sense of semantic level, corresponding to the generalizing theorem
  in the sense of syntax. -/
theorem Structure.satisfies_gen_elim (M : Structure L α) {Γ} {φ : Formula L} {i : Idx} :
    M.satisfies Γ (.fall i φ) -> M.satisfies Γ φ := by
  unfold satisfies
  intro h s h1
  rw [←replace_absorb s i]
  exact (h s h1) (s i)

theorem Structure.satisfies_gen_intro (M : Structure L α) (Γ) (φ : Formula L) (i : Idx) :
    (∀ g ∈ Γ, i ∉ g.fVars) -> M.satisfies Γ φ -> M.satisfies Γ (.fall i φ) := by
  intro hg h s h1 a
  have : ∀ g ∈ Γ, Formula.interpret M (replace s i a) g := by
    intro g h2
    have := h1 g h2
    rw [Formula.interpret_replace_invariance M s a (hg g h2)]
    exact this
  exact h (replace s i a) this

theorem Structure.deduction (M : Structure L α) {Γ} (φ ψ : Formula L) :
    (M.satisfies (Γ.insert φ) ψ) ↔ (M.satisfies Γ (.impl φ ψ)) := by
  constructor
  · intro h s g hg
    have : ∀ g ∈ Set.insert φ Γ, Formula.interpret M s g := by
      intro x hx
      simp only [Set.insert, Set.mem_setOf_eq] at hx
      rcases hx with h1 | h2
      · rw [h1]; exact hg
      · exact g x h2
    exact h s this
  · intro h s hg
    simp only [satisfies, Formula.interpret] at h
    exact h s (fun g h1 => hg g (id (.inr h1))) (hg φ (id (.inl rfl)))

lemma Term.interpret_subst (M : Structure L α) (s) {i ti t} :
    interpret M s (subst i ti t) = interpret M (replace s i (ti.interpret M s)) t := by
  induction t with
  | var j =>
    simp only [interpret, subst]
    by_cases h : i = j
    · simp [h]
    · simp only [h, interpret, ↓reduceIte, right_eq_ite_iff]; intro h'
      exfalso; exact h h'.symm
  | app n args h =>
    simp only [interpret, subst]
    conv => lhs; arg 3; intro x; rw [h x]

theorem Formula.interpret_subst (M : Structure L α) (s) {i t φ} (h : FreeFor i t φ) :
    interpret M s (safeSub i t φ h) <-> interpret M (replace s i (t.interpret M s)) φ := by
  induction φ generalizing s with
  | atom n ns =>
    simp only [interpret, safeSub]
    conv => lhs; arg 3; intro x; rw [Term.interpret_subst M s]
  | falsum => simp only [interpret, safeSub]
  | impl φ ψ h1 h2 => simp only [interpret, safeSub]; rw [h1 s h.left, h2 s h.right]
  | fall j φ h' =>
    by_cases hi : i = j
    · simp only [interpret, safeSub, hi, ↓reduceDIte]
      conv => rhs; intro a; lhs; rw [replace_idempotent]
    · simp only [safeSub, hi, ↓reduceDIte, interpret]
      rcases h with h1 | h2 | h3
      · exfalso; exact hi h1
      · conv => rhs; intro a; lhs; rw [replace_comm s i j hi]
        conv => rhs; intro a; rw [interpret_replace_invariance M _ _ h2]
        conv =>
          lhs; intro a; arg 3;
          rw [subst_invariance (out_var_is_free_for_any_term t h2) h2]
      · have (a : α) := h' (replace s j a) h3.right
        conv => lhs; intro a; rw [this a]
        conv => rhs; intro a; lhs; rw [replace_comm s i j hi]
        conv =>
          lhs; intro a; arg 2; arg 3;
          rw [Term.interpret_replace_invariance M s a h3.left]
end interpret

end PrimaryLogic
