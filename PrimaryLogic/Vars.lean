import PrimaryLogic.Formula

namespace PrimaryLogic
variable {LF LP : Type} {L : Lang LF LP}

lemma Formula.bVars_subset_vars : (φ : Formula L) -> φ.bVars ⊆ φ.vars
  | atom .. | falsum => Finset.empty_subset _
  | impl φ ψ => by
    unfold bVars vars
    apply Finset.union_subset_union
    · exact Formula.bVars_subset_vars φ
    · exact Formula.bVars_subset_vars ψ
  | fall i φ => by
    unfold bVars vars
    apply Finset.insert_subset_insert
    exact Formula.bVars_subset_vars φ

lemma Formula.fVars_subset_vars (φ : Formula L) : φ.fVars ⊆ φ.vars := by
  induction φ with
  | atom n args | falsum => simp only [fVars, vars, subset_refl]
  | impl x y hx hy => simp only [fVars, vars]; exact Finset.union_subset_union hx hy
  | fall i x h =>
    simp only [fVars, vars]
    calc x.fVars.erase i
      _ ⊆ x.fVars := Finset.erase_subset ..
      _ ⊆ x.vars := h
      _ ⊆ insert i x.vars := Finset.subset_insert ..

lemma Formula.term_FreeFor (i : Idx) (t : Term L) (φ : Formula L) (h : t.vars ∩ φ.vars = ∅) :
    FreeFor i t φ := by
  open Finset in
  induction φ with
  | atom | falsum => trivial
  | impl x y hx hy =>
    unfold FreeFor
    unfold vars at h
    rw [inter_union_distrib_left, union_eq_empty] at h
    exact ⟨hx h.left, hy h.right⟩
  | fall j ψ h' =>
    unfold FreeFor
    unfold vars at h
    rw [insert_eq, inter_union_distrib_left, union_eq_empty, inter_singleton] at h
    split_ifs at h with h1
    · exfalso; exact singleton_ne_empty j h.left
    · right; right; exact ⟨h1, h' h.right⟩

lemma Term.const_vars_empty (t : Term L) : t.isConst -> t.vars = ∅ := by
  intro h; cases t with
  | var i => dsimp [isConst] at h
  | app f s =>
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i; unfold vars
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists]
    intro x
    rw [h] at x
    exact Fin.elim0 x

theorem Formula.const_FreeFor (i : Idx) (φ : Formula L) (t : Term L) :
    t.isConst -> FreeFor i t φ := fun h =>
  term_FreeFor i t φ <| by rw [Term.const_vars_empty t h, Finset.empty_inter]

lemma Formula.fVar_refl (i : Idx) (φ : Formula L) : φ.FreeFor i (.var i) := by
  induction φ with
  | atom | falsum => trivial
  | impl x y hx hy => exact ⟨hx, hy⟩
  | fall j x h =>
    unfold FreeFor
    by_cases h' : i = j
    · left; exact h'
    · right; right
      constructor
      · unfold Term.vars
        rw [Finset.mem_singleton]
        rwa [eq_comm] at h'
      · exact h

lemma Term.subst_self (i : Idx) (t : Term L) :
    Term.subst i (.var i) t = t := by
  induction t with
  | var j => simp [subst]
  | app n a h =>
    simp only [subst, app.injEq, heq_eq_eq, true_and]
    funext x
    exact h x

theorem Formula.subst_self (i : Idx) (φ : Formula L)
    (h : φ.FreeFor i (.var i)) : φ.subst i (.var i) h = φ := by
  induction φ with
  | atom n a =>
    simp only [subst, atom.injEq, heq_eq_eq, true_and]
    funext x
    exact Term.subst_self i (a x)
  | falsum => unfold subst; eq_refl
  | impl x y hx hy =>
    unfold subst;
    unfold FreeFor at h
    rw [hx h.left]
    rw [hy h.right]
  | fall j ψ h' =>
    simp only [subst, dite_eq_left_iff, fall.injEq, true_and]
    by_cases hi : i = j
    · intro hi; contradiction
    · intro _;
      unfold FreeFor at h
      rcases h with h1 | h2 | h3
      · exfalso; exact hi h1
      · exact h' (out_var_FreeFor_term (.var i) h2)
      · exact h' h3.right

lemma Term.subst_invariance (i : Idx) (t s : Term L) :
  i ∉ s.vars -> t.subst i s = s := by
  intro h
  induction s with
  | var j =>
    simp [vars] at h
    simp [subst, h]
  | app n args h' =>
    simp only [vars, Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists] at h
    simp only [subst, app.injEq, heq_eq_eq, true_and]
    funext x
    exact h' x (h x)

theorem Formula.subst_invariance {i : Idx} {t : Term L} {φ : Formula L} (h : FreeFor i t φ) :
    i ∉ φ.fVars -> φ.subst i t h = φ := by
  intro hi
  induction φ with
  | atom n args =>
    simp only [subst, atom.injEq, heq_eq_eq, true_and]
    simp only [fVars, Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists] at hi
    funext x
    exact Term.subst_invariance i t (args x) (hi x)
  | falsum => dsimp only [subst]
  | impl x y hx hy =>
    simp only [subst, impl.injEq]
    simp only [fVars, Finset.mem_union, not_or] at hi
    dsimp only [FreeFor] at h
    exact ⟨hx h.left hi.left, hy h.right hi.right⟩
  | fall j x hx =>
    simp only [subst, dite_eq_left_iff, fall.injEq, true_and]
    simp only [fVars, Finset.mem_erase, ne_eq, not_and] at hi
    by_cases h' : i = j
    · intro h1; exfalso; exact h1 h'
    · intro _; apply hx; exact hi h'

lemma Term.subst_circulation (i j : Idx) (t : Term L) (hj : j ∉ t.vars) :
    subst j (.var i) (subst i (.var j) t) = t := by
  induction t with
  | var k =>
    dsimp only [subst]
    simp only [vars, Finset.notMem_singleton] at hj
    split_ifs with h
    · simp only [subst, ↓reduceIte, var.injEq]; exact h
    · simp only [subst, ite_eq_right_iff, var.injEq]
      intro hk; exfalso; exact hj hk
  | app n s h =>
    simp only [subst, app.injEq, heq_eq_eq, true_and]
    simp only [vars, Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists] at hj
    funext k; apply h; apply hj

theorem Formula.var_var_FreeFor (i j : Idx) (φ : Formula L) (hj : j ∉ φ.vars) :
    FreeFor i (.var j) φ := term_FreeFor i (.var j) φ <|
  (Finset.inter_comm φ.vars (Term.var j).vars) ▸ Finset.inter_singleton_of_notMem hj

theorem Formula.subst_circulation (i j : Idx) (φ : Formula L) (hj : j ∉ φ.vars) :
    let ψ := subst i (.var j) φ <| var_var_FreeFor i j φ hj
    ∃ h : FreeFor j (.var i) ψ, subst j (.var i) ψ h = φ := by
  induction φ with
  | atom n s =>
    use True.intro
    simp only [subst, atom.injEq, heq_eq_eq, true_and]
    simp only [vars, Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists] at hj
    funext k
    exact Term.subst_circulation i j _ (hj _)
  | falsum => use True.intro; dsimp [subst]
  | impl x y hx hy =>
    simp only [vars, Finset.mem_union, not_or] at hj
    dsimp only [subst]
    obtain ⟨hx1, hx2⟩ := hx hj.left
    obtain ⟨hy1, hy2⟩ := hy hj.right
    use ⟨hx1, hy1⟩
    congr
  | fall k x h =>
    simp only [vars, Finset.mem_insert, not_or] at hj
    have h' := Finset.notMem_mono (fVars_subset_vars _) hj.right
    dsimp only [subst]
    split_ifs with hi
    · simp only [FreeFor, Term.vars, Finset.mem_singleton]
      refine ⟨?_, ?_⟩
      · right; left; exact h'
      · dsimp [subst]
        split_ifs with hk
        · exfalso; exact hj.left hk
        · congr; exact subst_invariance _ h'
    · simp only [FreeFor, Term.vars, Finset.mem_singleton]
      obtain ⟨h1, h2⟩ := h hj.right
      refine ⟨?_, ?_⟩
      · right; right; exact ⟨ne_comm.mp hi, h1⟩
      · dsimp [subst]
        split_ifs with hk
        · exfalso; exact hj.left hk
        · rw [fall.injEq]; exact ⟨rfl, h2⟩

-- Prepared for completeness proofs.
def Formula.loose (t : Term L) (i : Idx) : Formula L -> Formula L
  | x@(.atom ..) => x
  | .falsum => .falsum
  | .impl φ ψ => .impl (φ.loose t i) (ψ.loose t i)
  | .fall j φ =>
    let ψ := φ.loose t i
    let k := Freshable.fresh <| insert i (ψ.vars ∪ t.vars)
    have h : FreeFor j (.var k) ψ := term_FreeFor _ _ _ <| by
      unfold Term.vars; rw [Finset.singleton_inter]
      split_ifs with hk
      · exfalso; dsimp only [k] at hk
        apply Freshable.fresh_is_new (insert i (ψ.vars ∪ t.vars))
        open Finset in
        refine mem_of_subset ?_ hk
        exact subset_trans (subset_union_left ..) (subset_insert ..)
      · rfl
    .fall k <| ψ.subst j (.var k) h

lemma Term.subst_vars (i : Idx) (s t : Term L) :
    (subst i s t).vars ⊆ s.vars ∪ (t.vars.erase i) := by
  induction t with
  | var j =>
    unfold subst
    split_ifs with h
    · apply Finset.subset_union_left
    · conv => lhs; unfold vars
      conv =>
        rhs; rhs; unfold vars
        rw [Finset.erase_eq_of_notMem (by rw [Finset.mem_singleton]; exact h)]
      apply Finset.subset_union_right
  | app n a h =>
    dsimp only [subst, vars]
    rw [Finset.biUnion_subset_iff_forall_subset]
    intro x hx
    apply subset_trans (h x)
    apply Finset.union_subset_union_right
    apply Finset.erase_subset_erase
    exact Finset.subset_biUnion_of_mem
      (s := @Finset.univ (Fin (L.funcs n)) _) (fun k => (a k).vars) hx

theorem Formula.subst_vars {i : Idx} {t : Term L} {φ} (h : FreeFor i t φ) :
    (subst i t φ h).vars ⊆ t.vars ∪ φ.vars := by
  open Finset in
  induction φ with
  | atom n a =>
    dsimp [subst, vars];
    rw [Finset.biUnion_subset_iff_forall_subset]
    intro x hx
    apply subset_trans (Term.subst_vars ..)
    apply union_subset_union_right
    apply subset_trans (Finset.erase_subset ..)
    exact subset_biUnion_of_mem
      (s := @Finset.univ (Fin (L.preds n)) _) (fun k => (a k).vars) hx
  | falsum => dsimp [subst, fVars]; apply subset_union_right
  | impl x y hx hy =>
    dsimp [subst, vars]
    unfold FreeFor at h
    conv =>
      rhs; rw [←union_self t.vars, ←union_assoc]
      conv => lhs; rw [union_assoc, union_comm]
      rw [union_assoc]
    apply union_subset_union
    · exact hx h.left
    · exact hy h.right
  | fall j ψ h' =>
    dsimp [subst, vars]
    split_ifs with hij
    · dsimp [vars]; apply subset_union_right
    · dsimp [vars]
      unfold FreeFor at h
      replace h := Or.resolve_left h hij
      rcases h with h1 | h2
      · rw [subst_invariance _ h1]
        apply subset_union_right
      · rw [union_insert, insert_subset_iff]
        refine ⟨mem_insert_self .., ?_⟩
        apply subset_trans (h' h2.right)
        apply subset_insert

theorem Formula.subst_fvars (i : Idx) (t : Term L) (φ : Formula L) (h : FreeFor i t φ) :
    (subst i t φ h).fVars ⊆ t.vars ∪ (φ.fVars.erase i) := by
  open Finset in
  induction φ with
  | atom n a =>
    dsimp [subst, fVars];
    rw [biUnion_subset_iff_forall_subset]
    intro x hx
    apply subset_trans <| Term.subst_vars ..
    apply union_subset_union_right
    apply erase_subset_erase
    exact subset_biUnion_of_mem
      (s := @univ (Fin (L.preds n)) _) (fun k => (a k).vars) hx
  | falsum => dsimp [subst, fVars]; apply subset_union_right
  | impl x y hx hy =>
    dsimp [subst, fVars]
    unfold FreeFor at h
    conv =>
      rhs; rw [←union_self t.vars, erase_union_distrib, ←union_assoc]
      conv => lhs; rw [union_assoc, union_comm]
      rw [union_assoc]
    apply union_subset_union
    · exact hx h.left
    · exact hy h.right
  | fall j ψ h' =>
    dsimp [subst, fVars]
    split_ifs with hij
    · dsimp [fVars]; rw [hij, erase_idem]; apply subset_union_right
    · dsimp [fVars]
      unfold FreeFor at h
      replace h := Or.resolve_left h hij
      rcases h with h1 | h2
      · rw [subst_invariance _ h1, erase_right_comm, erase_eq_of_notMem h1]
        apply subset_union_right
      · apply subset_trans <| erase_subset_erase _ (h' h2.right)
        rw [erase_union_distrib, erase_right_comm]
        apply union_subset_union_left
        apply erase_subset

lemma Formula.FreeFor_subst (i j : Idx) (t s : Term L) (φ : Formula L)
    (hi : FreeFor i t φ) (hj : FreeFor j s φ) :
    i ∉ s.vars -> FreeFor i t (φ.subst j s hj) := fun h => by
  induction φ with
  | atom | falsum => trivial
  | impl x y hx hy =>
    unfold subst FreeFor
    unfold FreeFor at hi hj
    exact ⟨hx hi.left hj.left, hy hi.right hj.right⟩
  | fall k ψ h' =>
    unfold subst
    unfold FreeFor at hj
    split_ifs with hjk
    · exact hi
    · unfold FreeFor at hi ⊢
      rcases hi with h1 | h2 | h3
      · left; exact h1;
      · right
        replace hj := Or.resolve_left hj hjk
        left
        apply Finset.not_mem_subset (t := s.vars ∪ ψ.fVars)
        · apply subset_trans (subst_fvars ..)
          apply Finset.union_subset_union_right
          apply Finset.erase_subset
        · rw [Finset.notMem_union]; exact ⟨h, h2⟩
      · right
        rcases Or.resolve_left hj hjk with h4 | h5
        · right; refine ⟨h3.left, ?_⟩
          apply h' h3.right
        · right; exact ⟨h3.left, h' h3.right h5.right⟩

theorem Formula.loose_FreeFor (i : Idx) (t : Term L) (φ : Formula L) :
    FreeFor i t (φ.loose t i) := by
  induction φ with
  | atom | falsum => trivial
  | impl x y hx hy => unfold loose FreeFor; exact ⟨hx, hy⟩
  | fall j x h =>
    unfold loose FreeFor
    open Finset in
    right; right; constructor
    · have : t.vars ⊆ insert i ((loose t i x).vars ∪ t.vars) :=
        subset_trans (subset_union_right ..) (subset_insert ..)
      exact not_mem_subset this <| Freshable.fresh_is_new _
    · apply FreeFor_subst _ _ _ _ _ h
      unfold Term.vars
      rw [notMem_singleton]
      by_contra
      have h' := Freshable.fresh_is_new <| insert i ((loose t i x).vars ∪ t.vars)
      rw [←this, mem_insert, not_or] at h'
      exact h'.left rfl

theorem Formula.loose_depth_eq (i : Idx) (t : Term L) (φ : Formula L) :
    (φ.loose t i).depth = φ.depth := by
  induction φ with
  | atom | falsum => unfold loose depth; rfl
  | impl x y hx hy =>
    unfold loose depth
    rw [Nat.add_right_cancel_iff]
    exact congr_arg₂ _ hx hy
  | fall j ψ h =>
    unfold loose depth
    rw [Nat.add_right_cancel_iff, ←h]
    apply subst_depth_eq

section map

abbrev Term.av (t : Term L) (p : Idx → Prop) : Prop := ∀ i ∈ t.vars, p i
abbrev Formula.av (φ : Formula L) (p : Idx → Prop) : Prop := ∀ i ∈ φ.vars, p i

variable (p : Idx -> Prop) (f : Idx -> Idx)
def Term.varMap (t : Term L) (hi : t.av p) : Term L :=
  match t with
  | var i => .var (f i)
  | app n s => .app n fun k => varMap (s k) fun j hj => hi j <| by
    simp only [vars, Finset.mem_biUnion, Finset.mem_univ, true_and]; exact ⟨k, hj⟩

def Formula.varMap (φ : Formula L) (hi : φ.av p) : Formula L :=
  match φ with
  | atom n s => atom n fun k => Term.varMap p f (s k) fun j hj => by
    apply hi; simp only [vars, Finset.mem_biUnion, Finset.mem_univ, true_and]; exact ⟨k, hj⟩
  | falsum => falsum
  | impl ψ χ => impl
    (varMap ψ fun j hj => by apply hi; unfold vars; rw [Finset.mem_union]; left; exact hj)
    (varMap χ fun j hj => by apply hi; unfold vars; rw [Finset.mem_union]; right; exact hj)
  | fall i ψ => fall (f i) <| varMap ψ fun j hj => by
    apply hi; unfold vars; exact Finset.mem_insert_of_mem hj

variable {p : Idx -> Prop} {f : Idx -> Idx}

lemma Term.varMap_vars (t : Term L) (hi : t.av p) :
    (varMap p f t hi).vars = t.vars.image f := by
  induction t with
  | var i => unfold varMap vars; rw [Finset.image_singleton]
  | app n s h =>
    unfold varMap vars
    rw [Finset.biUnion_image]
    dsimp
    conv => lhs; arg 2; intro k; rw [h k]

lemma Formula.varMap_vars (φ : Formula L) (hi : φ.av p) :
    (varMap p f φ hi).vars = φ.vars.image f := by
  induction φ with
  | atom n s =>
    unfold varMap vars
    rw [Finset.biUnion_image]
    dsimp
    conv => lhs; arg 2; intro k; rw [Term.varMap_vars]
  | falsum => rfl
  | impl x y hx hy =>
    unfold varMap vars
    rw [Finset.image_union, hx, hy]
  | fall i ψ h =>
    unfold varMap vars
    rw [Finset.image_insert, h]

lemma Formula.varMap_fVars {φ : Formula L} (hf : PartialInj p f) (hi : φ.av p) :
    (varMap p f φ hi).fVars = φ.fVars.image f := by
  induction φ with
  | atom n s =>
    unfold varMap fVars
    rw [Finset.biUnion_image]
    dsimp
    conv => lhs; arg 2; intro k; rw [Term.varMap_vars]
  | falsum => rfl
  | impl x y hx hy =>
    unfold varMap fVars
    rw [Finset.image_union, hx, hy]
  | fall i ψ h =>
    unfold varMap fVars
    rw [PartialInj.image_erase hf, h]
    · intro x hx
      apply hi x
      unfold vars; rw [Finset.mem_insert]; right
      apply Finset.mem_of_subset (fVars_subset_vars ..) hx
    · apply hi
      unfold vars;
      apply Finset.mem_insert_self

lemma Term.varMap_subst (hf : PartialInj p f) (i : Idx) (t s : Term L)
    (pi : p i) (ht : t.av p) (hs : s.av p) :
    (s.subst i t).varMap p f (fun j hj => Or.elim
      (Finset.mem_union.mp <| Finset.mem_of_subset (subst_vars ..) hj)
      (hs j ·) (ht j <| Finset.mem_of_mem_erase ·))
    = (s.varMap p f hs).subst (f i) (t.varMap p f ht) := by
  induction t with
  | var j =>
    conv => rhs; arg 3; unfold varMap
    conv => lhs; unfold subst
    split_ifs with h
    · conv => rhs; rw [h]
      simp only [subst, ↓reduceIte]
    · have := hf.ne pi (ht j (Finset.mem_singleton_self ..)) h
      simp only [subst, this, ↓reduceIte]
      unfold varMap
      rfl
  | app n args h =>
    simp only [subst, varMap]
    congr; funext k
    apply h k

lemma Formula.varMap_FreeFor (hf : PartialInj p f) {i : Idx} {t : Term L} {φ : Formula L}
    (pi : p i) (hi : φ.av p) (ht : t.av p) :
    φ.FreeFor i t ↔ (varMap p f φ hi).FreeFor (f i) (t.varMap p f ht) := by
  induction φ with
  | atom | falsum => dsimp only [FreeFor, varMap]; rfl
  | impl x y hx hy => dsimp [FreeFor, varMap]; rw [hx, hy]
  | fall j ψ h' =>
    dsimp [FreeFor, varMap]
    rw [←h']
    by_cases h : i = j
    · simp only [h, true_or]
    · unfold av vars at hi
      conv at hi => intro _; lhs; rw [Finset.mem_insert]
      have hij : f i ≠ f j := hf.ne pi (hi j (Or.inl rfl)) h
      simp only [h, false_or, hij, Term.varMap_vars, Finset.mem_image, not_exists, not_and]
      have h1 := varMap_fVars hf (fun k hk => hi k (Or.inr hk))
      have h2 := fun k hk => hi k <| Or.inr <| Finset.mem_of_subset (fVars_subset_vars _) hk
      rw [h1, hf.mem_finset_image h2 pi]
      suffices x : (∀ x ∈ t.vars, ¬f x = f j) ↔ j ∉ t.vars from by rw [x]
      constructor
      · intro h3; by_contra
        exact h3 j this rfl
      · intro h3 k hk; by_contra
        have h4 := hf (ht k hk) (hi j (Or.inl rfl)) this
        rw [h4] at hk
        exact h3 hk

lemma Formula.varMap_subst (hf : PartialInj p f) {i : Idx} {t : Term L} {φ : Formula L}
    (h : φ.FreeFor i t) (pi : p i) (hi : φ.av p) (ht : t.av p) :
    (φ.subst i t h).varMap p f (fun j hj => Or.elim
      (Finset.mem_union.mp <| Finset.mem_of_subset (subst_vars h) hj) (ht j ·) (hi j ·))
    = (varMap p f φ hi).subst (f i) (t.varMap p f ht) (by
      rw [←Formula.varMap_FreeFor hf pi hi ht]; exact h) := by
  induction φ with
  | atom n s =>
    dsimp [subst, varMap]
    congr; funext k
    apply Term.varMap_subst hf
    exact pi
  | falsum => rfl
  | impl x y hx hy => dsimp [subst, varMap]; rw [hx h.left, hy h.right]
  | fall j ψ h' =>
    dsimp [Formula.subst, Formula.varMap]
    split_ifs with h1
    · simp only [h1, ↓reduceDIte, varMap]
    · unfold av vars at hi
      conv at hi => intro _; rw [Finset.mem_insert]
      have := hf.ne pi (hi j <| Or.inl rfl) h1
      simp only [this, ↓reduceDIte, varMap]
      congr
      unfold FreeFor at h
      simp [h1] at h
      apply h'

structure VarContext (L : Lang LF LP) (p : Idx → Prop) where
  i : Idx
  t : Term L
  φ : Formula L
  ψ : Formula L
  hi : p i
  ht : t.av p
  hx : φ.av p
  hy : ψ.av p

structure Mor (L : Lang LF LP) where
  p : Idx -> Prop
  ι (i : Idx) : p i -> Idx
  τ (t : Term L) : t.av p -> Term L
  f : (φ : Formula L) -> φ.av p -> Formula L

open Formula Finset in
structure MorAx (m : Mor L) (c : VarContext L m.p) : Prop where
  map_falsum : m.f falsum (False.elim <| notMem_empty · ·) = falsum
  map_impl :
      m.f (impl c.φ c.ψ) (fun j h => Or.elim (mem_union.mp h) (c.hx j ·) (c.hy j ·))
    = impl (m.f c.φ c.hx) (m.f c.ψ c.hy)
  map_fall :
      m.f (fall c.i c.φ) (fun j h => Or.elim (mem_insert.mp h) (· ▸ c.hi) (c.hx j ·))
    = fall (m.ι c.i c.hi) (m.f c.φ c.hx)
  free_var : c.i ∉ c.φ.fVars → (m.ι c.i c.hi) ∉ (m.f c.φ c.hx).fVars
  free_for : FreeFor c.i c.t c.φ → FreeFor (m.ι c.i c.hi) (m.τ c.t c.ht) (m.f c.φ c.hx)
  map_subst (h) :
      m.f (subst c.i c.t c.φ h) (fun j e => Or.elim
        (mem_union.mp <| mem_of_subset (subst_vars h) e) (c.ht j ·) (c.hx j ·))
    = subst (m.ι c.i c.hi) (m.τ c.t c.ht) (m.f c.φ c.hx) (free_for h)

def Formula.varMor (p : Idx → Prop) (f : Idx → Idx) (L : Lang LF LP) : Mor L where
  p := p
  ι i _ := f i
  τ := Term.varMap p f
  f := Formula.varMap p f

def Formula.varMorAx (p : Idx → Prop) (f : Idx → Idx) (hf : PartialInj p f)
  (c : VarContext L p) : MorAx (varMor p f L) c where
  map_falsum := rfl
  map_impl := rfl
  map_fall := rfl
  free_var h := by
    dsimp [varMor]
    have : ∀ i ∈ c.φ.fVars, p i := fun i h =>
      c.hx i <| Finset.mem_of_subset (fVars_subset_vars ..) h
    rw [varMap_fVars hf c.hx, hf.mem_finset_image this c.hi]
    exact h
  free_for h := (varMap_FreeFor hf c.hi c.hx c.ht).mp h
  map_subst h := varMap_subst hf h c.hi c.hx c.ht

end map

section substFun
variable [DecidableEq LF]

theorem Term.fun_var_subst_distrib (i : Idx) (f : LF) (ir fr tr : Term L) : i ∉ fr.vars →
    substFun fr f (subst i ir tr) = subst i (substFun fr f ir) (substFun fr f tr) := by
  intro h0
  induction tr with
  | var j =>
    by_cases h : i = j <;>
    simp only [subst, h, substFun, ite_cond_eq_true, ite_cond_eq_false]
  | app g s h =>
    by_cases h1 : g = f
    · simp only [subst, substFun, h1, ite_cond_eq_true]
      apply symm
      exact Term.subst_invariance i _ fr h0
    · simp only [subst, substFun, h1, ite_cond_eq_false, app.injEq, heq_eq_eq, true_and]
      funext k; exact h k

lemma Term.substFun_not_mem_fVars {i : Idx} {f : LF} {fr tr : Term L} :
    i ∉ fr.vars → i ∉ tr.vars → i ∉ (substFun fr f tr).vars := by
  intro h0 h1
  induction tr with
  | var j =>
    dsimp only [vars] at h1
    dsimp only [substFun, vars]
    exact h1
  | app g s h =>
    simp only [vars, Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists] at h1
    dsimp only [substFun]
    split_ifs with h2
    · exact h0
    · simp only [vars, Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists]
      intro x; exact h x <| h1 x

lemma Formula.substFun_not_mem_fVars {i : Idx} {f : LF} {fr : Term L} {φ : Formula L} :
    i ∉ fr.vars → i ∉ φ.fVars → i ∉ (substFun fr f φ).fVars := by
  intro h0 h1
  induction φ with
  | atom n p =>
    simp only [substFun, fVars, Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists]
    simp only [fVars, Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists] at h1
    intro x; exact Term.substFun_not_mem_fVars h0 (h1 x)
  | falsum => dsimp only [substFun, fVars, Finset.notMem_empty]; trivial
  | impl x y hx hy =>
    simp only [substFun, fVars, Finset.mem_union, not_or]
    simp only [fVars, Finset.mem_union, not_or] at h1
    exact ⟨hx h1.left, hy h1.right⟩
  | fall j x h' =>
    simp only [substFun, fVars, Finset.mem_erase, not_and]
    simp only [fVars, Finset.mem_erase, not_and] at h1
    intro h; exact h' (h1 h)

lemma Formula.substFun_FreeFor {i : Idx} {f : LF} {ir fr : Term L} {φ : Formula L}
    (hi : FreeFor i ir φ) (h : i ∉ fr.vars) (hb : fr.vars ∩ φ.bVars = ∅) :
      FreeFor i (Term.substFun fr f ir) (Formula.substFun fr f φ) := by
  induction φ with
  | atom p s | falsum => dsimp only [Formula.substFun, FreeFor]
  | impl x y hx hy =>
    dsimp only [Formula.substFun, FreeFor]
    have ⟨h1, h2⟩ := hi
    simp only [bVars, Finset.inter_union_distrib_left, Finset.union_eq_empty] at hb
    exact ⟨hx h1 hb.left, hy h2 hb.right⟩
  | fall j x h' =>
    dsimp only [Formula.substFun, FreeFor]
    dsimp [FreeFor] at hi
    rcases hi with h1 | h2 | ⟨h3, h4⟩
    · left; exact h1
    · right; left; exact Formula.substFun_not_mem_fVars h h2
    · right; right; constructor
      · refine Term.substFun_not_mem_fVars ?_ h3
        unfold bVars at hb
        by_contra
        have h5 := Finset.mem_insert_self j x.bVars
        have h6 := hb ▸ Finset.mem_inter.mpr ⟨this, h5⟩
        have h7 := Finset.notMem_empty j
        contradiction
      · simp only [bVars, Finset.insert_inter] at hb
        split_ifs at hb with h5
        · exfalso; simp only [Finset.insert_ne_empty] at hb
        · exact h' h4 hb

theorem Formula.fun_var_subst_distrib (i : Idx) (f : LF) (ir fr : Term L) (φ : Formula L)
    (h : FreeFor i ir φ) (h1 : i ∉ fr.vars) (hb : fr.vars ∩ φ.bVars = ∅) :
    Formula.substFun fr f (subst i ir φ h) =
      subst i (Term.substFun fr f ir) (substFun fr f φ) (substFun_FreeFor h h1 hb) := by
  induction φ with
  | atom p s =>
    simp only [subst, substFun, atom.injEq, heq_eq_eq, true_and]
    funext k; apply Term.fun_var_subst_distrib; exact h1
  | falsum => dsimp only [subst, substFun]
  | impl x y hx hy =>
    simp only [subst, substFun, impl.injEq]
    simp only [bVars, Finset.inter_union_distrib_left, Finset.union_eq_empty] at hb
    exact ⟨hx _ hb.left, hy _ hb.right⟩
  | fall j x h' =>
    dsimp only [subst, substFun]
    split_ifs with h1
    · rw [←h1]; dsimp only [substFun]
    · simp only [substFun, fall.injEq, true_and]
      simp only [FreeFor, h1, false_or] at h
      simp only [bVars, Finset.insert_inter] at hb
      split_ifs at hb with h5
      · exfalso; simp only [Finset.insert_ne_empty] at hb
      · rcases h with h2 | h3
        · have := out_var_FreeFor_term ir h2
          exact h' this hb
        · exact h' h3.right hb

end substFun

section close_formula

/-- Failed to apply `Finset.toList` for the sake of its noncomputable def,
  so that `Finset.sort` was used instead.
It takes me quite a while to complete the proof of `close_success` theorem,
  which seemes obvious for human but actually rather complicated to prove in Lean4.
There might be simpler proof, but anyway, it doesn't matter.
Honestly speaking, this section is bad implemented,
  as `Idx` becomes depending on `Nat` property,
  but I cannot come up with an easier way.
Generalized scheme that suits for other Idx type would make the proof more complicated,
  and I have to spend more time on the index handling,
  which is not the main topic of this project,
  at least for now.
However, the generalization of `Idx` type might not be impossible.
Seeming dependency on `Nat` property in the following proof only involves the order relation,
  which can be defined as any other sorts of relations.
For example, lexicographical order can be applied in `String` type,
  so that `Formula.close` is still valid with `String` as `Idx`.
Therefore, the above issues doesn't constitute fundamental difficulties,
  yet the key is the order decidability
  (it can be implemented in arbitrary form without the concern of its actual meaning),
  which cannot be bypassed by any other type of `close` algorithm.
-/
lemma first_element_from_sorted_set_is_outside (set : Finset Nat) (i : Nat)
    (s : List Nat) (h : i :: s = set.sort) : i ∉ s := by
  have hn : (set.sort (· ≤ ·)).Nodup := Finset.sort_nodup ..
  rw [←h] at hn
  simp at hn
  exact hn.left

lemma Formula.quantifier_extract_free_var
    (i : Idx) (s : List Idx) (h : i ∉ s) (φ : Formula L) :
    (List.foldr fall (fall i φ) s).fVars = (fall i (List.foldr fall φ s)).fVars := by
  unfold List.foldr
  induction s with
  | nil => eq_refl
  | cons j s hi =>
    dsimp only [fVars]
    simp at h
    cases s with
    | nil =>
      unfold List.foldr
      exact Finset.erase_right_comm
    | cons k _ =>
      have := hi h.right
      simp only [fVars] at this
      unfold List.foldr
      rw [Finset.erase_right_comm]
      congr

lemma sort_insert_cons_head_min (w : Finset Nat) (i : Nat) (s : List Nat)
    (h : i :: s = (insert i w).sort) : ∀ j ∈ w, i ≤ j := by
  intro j hj
  have h' : j ∈ insert i w := Finset.mem_of_subset (Finset.subset_insert ..) hj
  replace h' := (Finset.mem_sort (· ≤ ·)).mpr h'
  have h0 := Finset.pairwise_sort (insert i w) (· ≤ ·)
  rw [←h] at h0
  simp at h0
  rw [←h, List.mem_cons] at h'
  rcases h' with h1 | h2
  · rw [h1]
  · exact h0.left j h2

lemma Formula.foldr_forall_free_vars_down_to_nil (φ : Formula L) (s : List Idx)
    (h : s = φ.fVars.sort) : (s.foldr fall φ).fVars.sort = [] := by
  induction s generalizing φ with
  | nil => unfold List.foldr; exact h.symm
  | cons i s his =>
    unfold List.foldr
    let w := φ.fVars
    have : s = (fall i φ).fVars.sort := by
      unfold fVars
      have hi : i ∈ w := by
        rw [←Finset.mem_sort (· ≤ ·), ←h, List.mem_cons]
        left; eq_refl
      have h' : i :: s = (insert i (w.erase i)).sort := by
        rw [Finset.insert_erase hi, ←h]
      have := sort_insert_cons_head_min (w.erase i) i s h'
      rw [Finset.sort_insert (· ≤ ·) this (Finset.notMem_erase i w)] at h'
      simp only [List.cons.injEq, true_and] at h'
      exact h'
    have h0 := his (.fall i φ) this
    have : i ∉ s := first_element_from_sorted_set_is_outside w _ _ h
    replace := quantifier_extract_free_var i s this φ
    rwa [this] at h0

theorem Formula.close_success (φ : Formula L) : φ.close.fVars = ∅ := by
  unfold close
  have := foldr_forall_free_vars_down_to_nil φ φ.fVars.sort rfl
  replace := congr_arg List.toFinset this
  rwa [Finset.sort_toFinset _ (· ≤ ·), List.toFinset_nil] at this

def Formula.toSentence (φ : Formula L) : Sentence L := ⟨φ.close, close_success φ⟩

end close_formula

end PrimaryLogic
