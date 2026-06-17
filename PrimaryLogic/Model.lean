import PrimaryLogic.Vars

namespace PrimaryLogic

variable {LF LP : Type} {L : Lang LF LP} {α : Type u}

@[ext]
structure Structure (L : Lang LF LP) (α : Type u) : Type u where
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
  ∀ (α : Type) (M : Structure L α), M.satisfies Γ φ
infix:20 " ⊨ " => SemanticConsequence

lemma SemanticConsequence.monotone {Γ Δ} (φ : Formula L) :
    Γ ⊆ Δ -> (Γ ⊨ φ) -> (Δ ⊨ φ) :=
  fun h0 h1 β M s h2 =>
    (h1 β M) s fun g hg => h2 g (Set.mem_of_subset_of_mem h0 hg)

abbrev Formula.valid (φ : Formula L) := SemanticConsequence ∅ φ
prefix:21 "⊨ " => Formula.valid

def Satisfiable (Γ : Set (Formula L)) : Prop :=
  ∃ (α : Type) (M : Structure L α) (s : Assignment α),
  ∀ g ∈ Γ, g.interpret M s

def Mod (Γ : Set (Formula L)) (α : Type*) := { M : Structure L α // M.modelsOf Γ }

def ModAll (Γ : Set (Formula L)) : Type (u + 1) := Σ (β : Type u), Mod Γ β

variable (M : Structure L α)
def DefinableSet (φ : Formula L) := { s : Assignment α // φ.interpret M s }

def Structure.definableSets : Set (Set (Assignment α)) := { S | ∃ φ, S = DefinableSet M φ }
section interpret

lemma Term.interpret_coincidence {x : Term L} {s t : Assignment α} :
    (∀ i ∈ x.vars, s i = t i) -> x.interpret M s = x.interpret M t := by
  intro hx
  induction x with
  | var i =>
    unfold Term.interpret
    exact hx i (Set.mem_singleton i)
  | app m ms f =>
    unfold Term.interpret
    simp only [vars, Set.mem_iUnion, forall_exists_index] at hx
    conv =>
      lhs; arg 3; intro fi
      exact f fi fun i hi => hx i fi hi

lemma Term.interpret_replace_invariance {t : Term L} (s : Assignment α) (a : α) {i : Idx} :
    i ∉ t.vars -> t.interpret M (replace s i a) = t.interpret M s := by
  intro hi
  apply interpret_coincidence M
  simp only [ite_eq_right_iff]
  intro j hj h
  rw [h] at hj
  exfalso
  exact hi hj

theorem Formula.interpret_coincidence {φ : Formula L} (s t : Assignment α) :
    (∀ i ∈ φ.fvar, s i = t i) -> (φ.interpret M s <-> φ.interpret M t) := by
  intro h
  induction φ generalizing s t with
  | atom n ns =>
    unfold interpret
    simp only [fvar, Set.mem_iUnion, forall_exists_index] at h
    conv =>
      lhs; arg 3; intro fi;
      exact Term.interpret_coincidence M fun i hi => h i fi hi
  | falsum => unfold interpret; decide
  | impl φ ψ ha hb =>
    unfold interpret
    simp only [fvar, Set.mem_union] at h
    have h1 := ha s t fun i hi => h i (.inl hi)
    have h2 := hb s t fun i hi => h i (.inr hi)
    rw [h1, h2]
  | fall i φ hi =>
    unfold interpret
    simp only [fvar, Set.mem_diff, Set.mem_singleton_iff, and_imp] at h
    have : ∀ a : α, ∀ j ∈ φ.fvar,
        (replace s i a) j = (replace t i a) j := by
      intro a j hj
      by_cases h' : j = i <;> simp only [replace, h', ↓reduceIte]; exact h j hj h'
    conv => lhs; intro a; rw [hi _ _ (this a)]

theorem Formula.interpret_replace_invariance
    {φ : Formula L} (s : Assignment α) (a : α) {i : Idx} :
    i ∉ φ.fvar -> (φ.interpret M (replace s i a) <-> φ.interpret M s) := by
  intro hi
  apply interpret_coincidence M
  simp only [ite_eq_right_iff]
  intro j hj h
  rw [h] at hj
  exfalso; exact hi hj

/-- Classical needed -/
theorem Structure.sentence_determinacy [Inhabited α] (φ : Formula L) : φ.fvar = ∅ ->
    (∀ s : Assignment α, φ.interpret M s) ∨ (∀ s : Assignment α, ¬φ.interpret M s) := by
  intro h0
  let s0 : Assignment α := fun _ => Inhabited.default (α := α)
  have := Formula.interpret_coincidence M (φ := φ) s0
  rcases lem (φ.interpret M s0) with h1 | h2
  · left; intro s; exact (this s <| by simp [h0]).mp h1
  · right; intro s; exact (Iff.not <| this s <| by simp [h0]).mp h2

/-- The following two theorems show that the sentence makes no essential difference from
  unclosed formula in the sense of semantic level, corresponding to the generalizing theorem
  in the sense of syntax. -/
theorem Structure.satisfies_gen_elim {M : Structure L α} {Γ} {φ : Formula L} {i : Idx} :
    M.satisfies Γ (.fall i φ) -> M.satisfies Γ φ := by
  unfold satisfies
  intro h s h1
  rw [←replace_absorb s i]
  exact (h s h1) (s i)

theorem Structure.satisfies_gen_intro (Γ) (φ : Formula L) (i : Idx) :
    (∀ g ∈ Γ, i ∉ g.fvar) -> M.satisfies Γ φ -> M.satisfies Γ (.fall i φ) := by
  intro hg h s h1 a
  have : ∀ g ∈ Γ, Formula.interpret M (replace s i a) g := by
    intro g h2
    have := h1 g h2
    rw [Formula.interpret_replace_invariance M s a (hg g h2)]
    exact this
  exact h (replace s i a) this

theorem Structure.deduction {Γ} (φ ψ : Formula L) :
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

lemma Term.interpret_subst (s) {i ti t} :
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

theorem Formula.interpret_subst (s) {i t φ} (h : FreeFor i t φ) :
    interpret M s (subst i t φ h) <-> interpret M (replace s i (t.interpret M s)) φ := by
  induction φ generalizing s with
  | atom n ns =>
    simp only [interpret, subst]
    conv => lhs; arg 3; intro x; rw [Term.interpret_subst M s]
  | falsum => simp only [interpret, subst]
  | impl φ ψ h1 h2 => simp only [interpret, subst]; rw [h1 s h.left, h2 s h.right]
  | fall j φ h' =>
    by_cases hi : i = j
    · simp only [interpret, subst, hi, ↓reduceDIte]
      conv => rhs; intro a; lhs; rw [replace_idempotent]
    · simp only [subst, hi, ↓reduceDIte, interpret]
      rcases h with h1 | h2 | h3
      · exfalso; exact hi h1
      · conv => rhs; intro a; lhs; rw [replace_comm s i j hi]
        conv => rhs; intro a; rw [interpret_replace_invariance M _ _ h2]
        conv =>
          lhs; intro a; arg 3;
          rw [subst_invariance h2]
      · have (a : α) := h' (replace s j a) h3.right
        conv => lhs; intro a; rw [this a]
        conv => rhs; intro a; lhs; rw [replace_comm s i j hi]
        conv =>
          lhs; intro a; arg 2; arg 3;
          rw [Term.interpret_replace_invariance M s a h3.left]

lemma Term.interpret_varMap (f : Idx -> Idx) (s) (t) :
    interpret M s (varMap f t) = interpret M (s ∘ f) t := by
  induction t with
  | var i => unfold varMap interpret; rfl
  | app n a h => unfold varMap interpret; congr; funext k; apply h

lemma Formula.interpret_varMap {p : Set Idx} {f : Idx → Idx} (hf : PartInj p f) (s) {φ}
    (hi : φ.vars ⊆ p) : interpret M s (varMap f φ) ↔ interpret M (s ∘ f) φ := by
  induction φ generalizing s with
  | atom n a => unfold varMap interpret; conv => lhs; arg 3; intro i; rw [Term.interpret_varMap]
  | falsum => rfl
  | impl x y hx hy =>
    unfold vars at hi; rw [Set.union_subset_iff] at hi
    unfold varMap interpret; rw [hx s hi.1, hy s hi.2]
  | fall i ψ h' =>
    unfold varMap interpret
    suffices h : ∀ (a : α), interpret M (replace s (f i) a) (varMap f ψ)
        ↔ interpret M (replace (s ∘ f) i a) ψ from
      ⟨fun x a => (h a).mp (x a), fun x a => (h a).mpr (x a)⟩
    intro a
    unfold vars at hi; rw [Set.insert_subset_iff] at hi
    have h (j : Idx) (hj : j ∈ ψ.fvar) :=
      replace_of_map' s hf hi.1 (hi.2 <| Formula.fvar_subset_vars _ hj) a
    replace h := Formula.interpret_coincidence M _ _ h
    rw [h]
    exact h' _ hi.2

theorem Structure.satisfies_varMap_inj {p : Set Idx} {f : Idx → Idx} (hf : PartInj p f)
    (M : Structure L α) {Γ φ} (hΓ : ∀ g ∈ Γ, g.vars ⊆ p) (hφ : φ.vars ⊆ p) :
    M.satisfies Γ φ -> M.satisfies ((Formula.varMap f) '' Γ) (Formula.varMap f φ) := by
  intro h s ψ
  rw [Formula.interpret_varMap M hf _ hφ]
  apply h
  intro χ h'
  rw [←Formula.interpret_varMap M hf _ (hΓ χ h')]
  exact ψ _ (Set.mem_image_of_mem _ h')
end interpret
end PrimaryLogic
