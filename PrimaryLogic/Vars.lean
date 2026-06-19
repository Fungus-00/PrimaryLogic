import PrimaryLogic.Formula

namespace PrimaryLogic
variable {LF LP : Type} {L : Lang LF LP}

section dec
lemma Term.vars_eq_list (t : Term L) (i : Idx) : i ∈ t.vars ↔ i ∈ t.varList := by
  induction t with
  | var j => unfold vars varList; simp
  | app n s h => unfold vars varList; simp [h]

lemma Formula.vars_eq_list (φ : Formula L) (i : Idx) : i ∈ φ.vars ↔ i ∈ φ.varList := by
  induction φ with
  | atom n s =>
    unfold vars varList
    simp only [Set.mem_iUnion, Term.vars_eq_list, List.mem_flatMap, List.mem_finRange, true_and]
  | falsum => unfold vars varList; simp only [Set.notMem_empty, List.not_mem_nil]
  | impl x y hx hy => unfold vars varList; simp only [Set.mem_union, hx, hy, List.mem_append]
  | fall j φ h => unfold vars varList; simp only [Set.mem_insert_iff, h, List.mem_cons]

lemma Formula.fvar_eq_list (φ : Formula L) (i : Idx) : i ∈ φ.fvar ↔ i ∈ φ.fvarList := by
  induction φ with
  | atom n s => unfold fvar fvarList; simp [Term.vars_eq_list]
  | falsum => unfold fvar fvarList; simp only [Set.notMem_empty, List.not_mem_nil]
  | impl x y hx hy =>
    unfold fvar fvarList; simp only [Set.mem_union, hx, hy, List.mem_append]
  | fall j φ h' =>
    unfold fvar fvarList; simp only [Set.mem_diff, h', Set.mem_singleton_iff]
    constructor
    · intro h
      unfold List.removeAll
      rw [List.mem_filter]
      simp only [List.elem_eq_contains, List.contains_eq_mem, List.mem_cons, List.not_mem_nil,
          or_false, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
      exact h
    · intro h
      simp only [List.removeAll, List.elem_eq_contains, List.contains_eq_mem, List.mem_cons,
        List.not_mem_nil, or_false, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not] at h
      exact h

lemma Formula.bvar_eq_list (φ : Formula L) (i : Idx) : i ∈ φ.bvar ↔ i ∈ φ.bvarList := by
  induction φ with
  | atom | falsum => unfold bvar bvarList; simp only [Set.mem_empty_iff_false, List.not_mem_nil]
  | impl x y hx hy =>
    unfold bvar bvarList; simp only [Set.mem_union, hx, hy, List.mem_append]
  | fall j φ h' =>
    unfold bvar bvarList; rw [List.mem_cons, Set.mem_insert_iff]; simp only [h']

instance Term.decVars (t : Term L) (i : Idx) : Decidable (i ∈ t.vars) := by
  rw [vars_eq_list]; infer_instance

instance Formula.decVars (φ : Formula L) (i : Idx) : Decidable (i ∈ φ.vars) := by
  rw [vars_eq_list]; infer_instance

instance Formula.decFvar (φ : Formula L) (i : Idx) : Decidable (i ∈ φ.fvar) := by
  rw [fvar_eq_list]; infer_instance

instance Formula.decBvar (φ : Formula L) (i : Idx) : Decidable (i ∈ φ.bvar) := by
  rw [bvar_eq_list]; infer_instance

end dec

lemma Formula.bvar_subset_vars : (φ : Formula L) -> φ.bvar ⊆ φ.vars
  | atom .. | falsum => Set.empty_subset _
  | impl φ ψ => by
    unfold bvar vars
    apply Set.union_subset_union
    · exact Formula.bvar_subset_vars φ
    · exact Formula.bvar_subset_vars ψ
  | fall i φ => by
    unfold bvar vars
    apply Set.insert_subset_insert
    exact Formula.bvar_subset_vars φ

lemma Formula.fvar_subset_vars (φ : Formula L) : φ.fvar ⊆ φ.vars := by
  induction φ with
  | atom n args | falsum => simp only [fvar, vars, subset_refl]
  | impl x y hx hy => simp only [fvar, vars]; exact Set.union_subset_union hx hy
  | fall i x h =>
    simp only [fvar, vars]
    calc x.fvar \ {i}
      _ ⊆ x.fvar := Set.diff_subset' ..
      _ ⊆ x.vars := h
      _ ⊆ insert i x.vars := Set.subset_insert ..

lemma Formula.term_FreeFor (i : Idx) (t : Term L) (φ : Formula L) (h : t.vars ∩ φ.vars = ∅) :
    FreeFor i t φ := by
  open Set in
  induction φ with
  | atom | falsum => trivial
  | impl x y hx hy =>
    unfold FreeFor
    unfold vars at h
    rw [Set.inter_union_distrib_left, Set.union_eq_empty] at h
    exact ⟨hx h.left, hy h.right⟩
  | fall j ψ h' =>
    unfold FreeFor
    unfold vars at h
    rw [Set.insert_eq, Set.inter_union_distrib_left, union_eq_empty,
      Set.inter_singleton_eq_empty] at h
    · right; right; exact ⟨h.1, h' h.2⟩

lemma Term.const_vars_empty (t : Term L) : t.isConst -> t.vars = ∅ := by
  intro h; cases t with
  | var i => dsimp [isConst] at h
  | app f s =>
    rw [Set.eq_empty_iff_forall_notMem]
    intro i; unfold vars
    rw [Set.mem_iUnion, not_exists]
    intro x
    rw [h] at x
    exact Fin.elim0 x

theorem Formula.const_FreeFor (i : Idx) (φ : Formula L) (t : Term L) :
    t.isConst -> FreeFor i t φ := fun h =>
  term_FreeFor i t φ <| by rw [Term.const_vars_empty t h, Set.empty_inter]

lemma Formula.fvar_refl (i : Idx) (φ : Formula L) : φ.FreeFor i (.var i) := by
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
        rw [Set.mem_singleton_iff]
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

theorem Formula.subst_self (i : Idx) (φ : Formula L) : φ.subst i (.var i) (fvar_refl ..) = φ := by
  induction φ with
  | atom n a =>
    simp only [subst, atom.injEq, heq_eq_eq, true_and]
    funext x
    exact Term.subst_self i (a x)
  | falsum => unfold subst; eq_refl
  | impl x y hx hy => unfold subst; rw [hx, hy]
  | fall j ψ h' =>
    simp only [subst, dite_eq_left_iff, fall.injEq, true_and]
    by_cases hi : i = j
    · intro hi; contradiction
    · intro _; exact h'

lemma Term.subst_invariance (i : Idx) (t s : Term L) :
  i ∉ s.vars -> t.subst i s = s := by
  intro h
  induction s with
  | var j =>
    simp [vars] at h
    simp [subst, h]
  | app n args h' =>
    rw [vars, Set.mem_iUnion, not_exists] at h
    simp only [subst, app.injEq, heq_eq_eq, true_and]
    funext x
    exact h' x (h x)

theorem Formula.subst_invariance {i : Idx} {t : Term L} {φ : Formula L} (hi : i ∉ φ.fvar) :
    φ.subst i t (out_var_FreeFor_term t hi) = φ := by
  induction φ with
  | atom n args =>
    simp only [subst, atom.injEq, heq_eq_eq, true_and]
    rw [fvar, Set.mem_iUnion, not_exists] at hi
    funext x
    exact Term.subst_invariance i t (args x) (hi x)
  | falsum => dsimp only [subst]
  | impl x y hx hy =>
    simp only [subst, impl.injEq]
    simp only [fvar, Set.mem_union, not_or] at hi
    exact ⟨hx hi.left, hy hi.right⟩
  | fall j x hx =>
    simp only [subst, dite_eq_left_iff, fall.injEq, true_and]
    simp only [fvar, Set.mem_diff, Set.mem_singleton_iff, Decidable.not_not, not_and] at hi
    by_cases h' : i = j
    · intro h1; exfalso; exact h1 h'
    · intro _; apply hx; exact fun h2 => h' (hi h2)

lemma Term.subst_circulation (i j : Idx) (t : Term L) (hj : j ∉ t.vars) :
    subst j (.var i) (subst i (.var j) t) = t := by
  induction t with
  | var k =>
    dsimp only [subst]
    simp only [vars, Set.notMem_singleton_iff] at hj
    split_ifs with h
    · simp only [subst, ↓reduceIte, var.injEq]; exact h
    · simp only [subst, ite_eq_right_iff, var.injEq]
      intro hk; exfalso; exact hj hk
  | app n s h =>
    simp only [subst, app.injEq, heq_eq_eq, true_and]
    rw [vars, Set.mem_iUnion, not_exists] at hj
    funext k; apply h; apply hj

lemma Formula.var_var_FreeFor (i j : Idx) (φ : Formula L) (hj : j ∉ φ.vars) :
    FreeFor i (.var j) φ := term_FreeFor i (.var j) φ <|
  (Set.inter_comm φ.vars (Term.var j).vars) ▸ Set.inter_singleton_of_notMem hj

theorem Formula.subst_circulation (i j : Idx) (φ : Formula L) (hj : j ∉ φ.vars) :
    let ψ := subst i (.var j) φ <| var_var_FreeFor i j φ hj
    ∃ h : FreeFor j (.var i) ψ, subst j (.var i) ψ h = φ := by
  induction φ with
  | atom n s =>
    use True.intro
    simp only [subst, atom.injEq, heq_eq_eq, true_and]
    simp only [vars, Set.mem_iUnion, not_exists] at hj
    funext k
    exact Term.subst_circulation i j _ (hj _)
  | falsum => use True.intro; dsimp [subst]
  | impl x y hx hy =>
    simp only [vars, Set.mem_union, not_or] at hj
    dsimp only [subst]
    obtain ⟨hx1, hx2⟩ := hx hj.left
    obtain ⟨hy1, hy2⟩ := hy hj.right
    use ⟨hx1, hy1⟩
    congr
  | fall k x h =>
    simp only [vars, Set.mem_insert_iff, not_or] at hj
    have h' := Set.notMem_subset (fvar_subset_vars _) hj.right
    dsimp only [subst]
    split_ifs with hi
    · simp only [FreeFor, Term.vars]
      refine ⟨?_, ?_⟩
      · right; left; exact h'
      · dsimp [subst]
        split_ifs with hk
        · exfalso; exact hj.left hk
        · congr; exact subst_invariance h'
    · simp only [FreeFor, Term.vars]
      obtain ⟨h1, h2⟩ := h hj.right
      refine ⟨?_, ?_⟩
      · right; right; exact ⟨ne_comm.mp hi, h1⟩
      · dsimp [subst]
        split_ifs with hk
        · exfalso; exact hj.left hk
        · rw [fall.injEq]; exact ⟨rfl, h2⟩

def Formula.loose (t : Term L) (i : Idx) : Formula L -> Formula L
  | x@(.atom ..) => x
  | .falsum => .falsum
  | .impl φ ψ => .impl (φ.loose t i) (ψ.loose t i)
  | .fall j φ =>
    let ψ := φ.loose t i
    let k := Freshable.fresh <| i :: (ψ.varList ++ t.varList)
    have h : FreeFor j (.var k) ψ := term_FreeFor _ _ _ <| by
      unfold Term.vars; rw [Set.singleton_inter_eq_empty]
      by_contra; dsimp only [k] at this
      apply Freshable.fresh_is_new (i :: (ψ.varList ++ t.varList))
      rw [List.mem_cons, List.mem_append, ←vars_eq_list]
      right; left; exact this
    .fall k <| ψ.subst j (.var k) h

lemma Term.subst_vars (i : Idx) (s t : Term L) :
    (subst i s t).vars ⊆ s.vars ∪ (t.vars \ {i}) := by
  induction t with
  | var j =>
    unfold subst
    split_ifs with h
    · apply Set.subset_union_left
    · conv => lhs; unfold vars
      conv => rhs; rhs; unfold vars
      rw [Set.singleton_subset_iff]
      apply Set.subset_union_right
      simp only [Set.mem_singleton_iff, h, not_false_eq_true, Set.diff_singleton_eq_self']
  | app n a h =>
    dsimp only [subst, vars]
    rw [Set.iUnion_subset_iff']
    intro x hx
    apply subset_trans (h x)
    apply Set.union_subset_union_right
    apply Set.diff_subset_diff_left'
    apply Set.subset_iUnion_of_subset' x
    exact subset_rfl

theorem Formula.subst_vars {i : Idx} {t : Term L} {φ} (h : FreeFor i t φ) :
    (subst i t φ h).vars ⊆ t.vars ∪ φ.vars := by
  induction φ with
  | atom n a =>
    dsimp [subst, vars]
    rw [Set.iUnion_subset_iff']
    intro x
    apply subset_trans (Term.subst_vars ..)
    apply Set.union_subset_union_right
    apply subset_trans Set.diff_subset'
    apply Set.subset_iUnion_of_subset' x
    exact subset_rfl
  | falsum => dsimp [subst, fvar]; apply Set.subset_union_right
  | impl x y hx hy =>
    dsimp [subst, vars]
    unfold FreeFor at h
    conv =>
      rhs; rw [←Set.union_self t.vars, ←Set.union_assoc]
      conv => lhs; rw [Set.union_assoc, Set.union_comm]
      rw [Set.union_assoc]
    apply Set.union_subset_union
    · exact hx h.left
    · exact hy h.right
  | fall j ψ h' =>
    dsimp [subst, vars]
    split_ifs with hij
    · dsimp [vars]; apply Set.subset_union_right
    · dsimp [vars]
      unfold FreeFor at h
      replace h := Or.resolve_left h hij
      rcases h with h1 | h2
      · rw [subst_invariance h1]
        apply Set.subset_union_right
      · rw [Set.union_insert', Set.insert_subset_iff']
        refine ⟨Set.mem_insert .., ?_⟩
        apply subset_trans (h' h2.right)
        apply Set.subset_insert

theorem Formula.subst_fvar (i : Idx) (t : Term L) (φ : Formula L) (h : FreeFor i t φ) :
    (subst i t φ h).fvar ⊆ t.vars ∪ (φ.fvar \ {i}) := by
  induction φ with
  | atom n a =>
    dsimp [subst, fvar];
    rw [Set.iUnion_subset_iff']
    intro x hx
    apply subset_trans <| Term.subst_vars ..
    apply Set.union_subset_union_right
    apply Set.diff_subset_diff_left'
    apply Set.subset_iUnion_of_subset' x
    exact subset_rfl
  | falsum => dsimp [subst, fvar]; apply Set.empty_subset
  | impl x y hx hy =>
    dsimp [subst, fvar]
    unfold FreeFor at h
    conv =>
      rhs; rw [←Set.union_self t.vars, Set.union_diff_distrib', ←Set.union_assoc]
      conv => lhs; rw [Set.union_assoc, Set.union_comm]
      rw [Set.union_assoc]
    apply Set.union_subset_union
    · exact hx h.left
    · exact hy h.right
  | fall j ψ h' =>
    dsimp [subst, fvar]
    split_ifs with hij
    · dsimp [fvar]; rw [hij, Set.diff_diff', Set.union_self]; apply Set.subset_union_right
    · dsimp [fvar]
      unfold FreeFor at h
      replace h := Or.resolve_left h hij
      rcases h with h1 | h2
      · rw [subst_invariance h1, Set.diff_diff_comm', Set.diff_singleton_eq_self' h1]
        apply Set.subset_union_right
      · have h3 := h' h2.2
        rw [Set.diff_diff_comm', Set.diff_subset_iff', ←Set.union_assoc]
        conv => rhs; lhs; rw [Set.union_comm]
        apply subset_trans h3
        rw [Set.union_assoc]
        apply Set.union_subset_union_right
        conv => rhs; rw [Set.union_comm, Set.diff_union_self']
        exact Set.subset_union_left

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
        by_contra h1
        have hf : FreeFor j s ψ := Or.elim hj (out_var_FreeFor_term _ ·) (·.2)
        have h3 := Set.mem_of_subset_of_mem (subst_fvar j s ψ hf) h1
        rw [Set.mem_union] at h3
        replace h3 := Or.resolve_left h3 h
        rw [Set.mem_diff] at h3
        exact h2 h3.1
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
    open Set in
    right; right; constructor
    · have h1 := Freshable.fresh_is_new (i :: ((loose t i x).varList ++ t.varList))
      rw [Term.vars_eq_list]
      refine fun h' => h1 ?_
      rw [List.mem_cons, List.mem_append]
      right; right; exact h'
    · apply FreeFor_subst _ _ _ _ _ h
      unfold Term.vars
      rw [Set.mem_singleton_iff]
      by_contra h1
      have h' := Freshable.fresh_is_new <| i :: ((loose t i x).varList ++ t.varList)
      rw [←h1, List.mem_cons, not_or] at h'
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

def Term.varMap (f : Idx -> Idx) : Term L -> Term L
  | var i => .var (f i)
  | app n s => .app n fun k => varMap f (s k)

def Formula.varMap (f : Idx -> Idx) (φ : Formula L) : Formula L :=
  match φ with
  | atom n s => atom n fun k => Term.varMap f (s k)
  | falsum => falsum
  | impl ψ χ => impl (varMap f ψ) (varMap f χ)
  | fall i ψ => fall (f i) <| varMap f ψ

variable {p : Idx -> Prop} {f : Idx -> Idx}

lemma Term.varMap_id : varMap (L := L) id = id := by
  ext t
  induction t with
  | var i => rfl
  | app n s h => dsimp [varMap]; congr; funext k; exact h k

lemma Term.varMap_comp {g : Idx → Idx} :
    varMap (L := L) (f ∘ g) = (varMap f) ∘ (varMap g) := by
  ext t
  induction t with
  | var i => rfl
  | app n s h => dsimp [varMap]; congr; funext k; exact h k

lemma Term.varMap_vars (t : Term L) :
    (varMap f t).vars = t.vars.image f := by
  induction t with
  | var i => unfold varMap vars; rw [Set.image_singleton']
  | app n s h =>
    unfold varMap vars
    rw [Set.image_iUnion]
    dsimp
    conv => lhs; arg 1; intro k; rw [h k]

lemma Term.varMap_subst (hf : PartInj p f) (i : Idx) (t s : Term L)
    (pi : p i) (ht : t.av p) :
    (s.subst i t).varMap f = (s.varMap f).subst (f i) (t.varMap f) := by
  induction t with
  | var j =>
    conv => rhs; arg 3; unfold varMap
    conv => lhs; unfold subst
    split_ifs with h
    · conv => rhs; rw [h]
      simp only [subst, ↓reduceIte]
    · have := hf.ne pi (ht j (Set.mem_singleton ..)) h
      simp only [subst, this, ↓reduceIte]
      unfold varMap
      rfl
  | app n args h =>
    open Set in
    simp only [av, vars, Set.mem_iUnion, forall_exists_index] at ht
    simp only [subst, varMap]
    congr; funext k
    apply h k fun j hj => ht j k hj

lemma Term.varMap_eq {f g : Idx → Idx} {t : Term L} (h : ∀ i ∈ t.vars, f i = g i) :
    t.varMap f = t.varMap g := by
  induction t with
  | var i => unfold varMap; congr; exact h i (Set.mem_singleton _)
  | app n s h' =>
    unfold varMap; congr; funext k
    exact h' k fun j hj => h j <| Set.mem_iUnion_of_mem k hj

lemma Formula.varMap_id : varMap (L := L) id = id := by
  ext φ
  induction φ with
  | atom n s => dsimp [varMap]; congr; funext k; rw [Term.varMap_id]; rfl
  | falsum => rfl
  | impl x y hx hy => simp only [varMap, hx, id, hy]
  | fall i x h => simp only [varMap, id, h]

lemma Formula.varMap_comp {g : Idx → Idx} :
    varMap (L := L) (f ∘ g) = (varMap f) ∘ (varMap g) := by
  ext φ
  induction φ with
  | atom n s => dsimp [varMap]; congr; funext k; rw [Term.varMap_comp]; rfl
  | falsum => rfl
  | impl x y hx hy => simp only [varMap, hx, Function.comp_apply, hy]
  | fall i x h => simp only [varMap, Function.comp_apply, h]

lemma Formula.varMap_vars (φ : Formula L) :
    (varMap f φ).vars = φ.vars.image f := by
  induction φ with
  | atom n s =>
    unfold varMap vars
    rw [Set.image_iUnion]
    dsimp
    conv => lhs; arg 1; intro k; rw [Term.varMap_vars]
  | falsum => dsimp [varMap, vars]; rw [Set.image_empty']
  | impl x y hx hy =>
    unfold varMap vars
    rw [Set.image_union', hx, hy]
  | fall i ψ h =>
    unfold varMap vars
    rw [Set.image_insert_eq', h]

lemma Formula.varMap_fvar {φ : Formula L} (hf : PartInj p f) (hi : φ.vars ⊆ p) :
    (varMap f φ).fvar = φ.fvar.image f := by
  open Set in
  induction φ with
  | atom n s =>
    unfold varMap fvar
    rw [Set.image_iUnion]
    dsimp
    conv => lhs; arg 1; intro k; rw [Term.varMap_vars]
  | falsum => dsimp [varMap, fvar]; rw [Set.image_empty']
  | impl x y hx hy =>
    unfold varMap fvar
    simp only [Set.subset_def, vars, Set.mem_union] at hi
    rw [Set.image_union', hx fun i h => hi i (Or.inl h), hy fun i h => hi i (Or.inr h)]
  | fall i ψ h =>
    unfold varMap fvar
    rw [PartInj.image_diff hf, h]
    · rw [Set.image_singleton']
    · intro x hx
      apply hi
      unfold vars
      apply Set.mem_insert_of_mem
      exact hx
    · intro x hx
      apply hi
      unfold vars
      apply Set.mem_insert_of_mem
      refine Set.mem_of_subset_of_mem ?_ hx
      apply fvar_subset_vars
    · intro x hx
      unfold vars at hi
      rw [Set.subset_def] at hi
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hi i (Set.mem_insert ..)

lemma Formula.varMap_FreeFor (hf : PartInj p f) {i : Idx} {t : Term L} {φ : Formula L}
    (pi : p i) (hi : φ.av p) (ht : t.av p) :
    φ.FreeFor i t ↔ (varMap f φ).FreeFor (f i) (t.varMap f) := by
  open Set in
  induction φ with
  | atom | falsum => dsimp only [FreeFor, varMap]; rfl
  | impl x y hx hy =>
    simp only [av, vars, Set.mem_union] at hi
    dsimp only [FreeFor, varMap]
    rw [hx fun i h => hi i (Or.inl h), hy fun i h => hi i (Or.inr h)]
  | fall j ψ h' =>
    dsimp [FreeFor, varMap]
    rw [←h' fun k hk => hi k <| Set.mem_of_subset_of_mem (Set.subset_insert ..) hk]
    by_cases h : i = j
    · simp only [h, true_or]
    · unfold av vars at hi
      conv at hi => intro _; lhs; rw [Set.mem_insert_iff]
      have hij : f i ≠ f j := hf.ne pi (hi j (Or.inl rfl)) h
      simp only [h, false_or, hij, Term.varMap_vars, Set.mem_image, not_exists, not_and]
      have h1 := varMap_fvar hf (fun k hk => hi k (Or.inr hk))
      have h2 := fun k hk => hi k <| Or.inr <| Set.mem_of_subset_of_mem (fvar_subset_vars _) hk
      rw [h1, hf.mem_set_image h2 pi]
      suffices x : (∀ x ∈ t.vars, ¬f x = f j) ↔ j ∉ t.vars from by rw [x]
      constructor
      · intro h3; by_contra
        exact h3 j this rfl
      · intro h3 k hk; by_contra
        have h4 := hf (ht k hk) (hi j (Or.inl rfl)) this
        rw [h4] at hk
        exact h3 hk

theorem Formula.varMap_subst (hf : PartInj p f) {i : Idx} {t : Term L} {φ : Formula L}
    (h : φ.FreeFor i t) (pi : p i) (hi : φ.av p) (ht : t.av p) :
    (φ.subst i t h).varMap f = (varMap f φ).subst (f i) (t.varMap f) (by
      rw [←Formula.varMap_FreeFor hf pi hi ht]; exact h) := by
  open Set in
  induction φ with
  | atom n s =>
    dsimp [subst, varMap]
    congr; funext k
    apply Term.varMap_subst hf _ _ _ pi
    simp only [av, vars, Set.mem_iUnion, forall_exists_index] at hi
    intro j hj
    exact hi j k hj
  | falsum => rfl
  | impl x y hx hy =>
    dsimp [subst, varMap]
    simp only [av, vars, Set.mem_union] at hi
    rw [hx h.left fun j hj => hi j (Or.inl hj), hy h.right fun j hj => hi j (Or.inr hj)]
  | fall j ψ h' =>
    simp only [av, vars, Set.mem_insert_iff, forall_eq_or_imp] at hi
    dsimp [Formula.subst, Formula.varMap]
    split_ifs with h1 h2
    · simp only [varMap]
    · exfalso; exact h2 (congrArg f h1)
    · rename_i h2; exfalso; exact h1 (hf pi hi.left h2)
    · rename_i h2
      simp only [varMap]
      congr
      unfold FreeFor at h
      simp only [h1, false_or] at h
      exact h' _ hi.right

theorem Formula.varMap_eq {f g : Idx → Idx} {φ : Formula L} (h : ∀ i ∈ φ.vars, f i = g i) :
    φ.varMap f = φ.varMap g := by
  induction φ with
  | atom n s =>
    unfold varMap; congr; funext k
    exact Term.varMap_eq fun j hj => h j <| Set.mem_iUnion_of_mem k hj
  | falsum => dsimp [varMap]
  | impl x y hx hy =>
    unfold varMap; simp only [vars, Set.mem_union] at h
    rw [hx fun j hj => h j (.inl hj), hy fun j hj => h j (.inr hj)]
  | fall i ψ h' =>
    unfold varMap; simp only [vars, Set.mem_insert_iff] at h
    rw [h i (.inl rfl), h' fun j hj => h j (.inr hj)]

def Formula.varMor (L : Lang LF LP) {p d} {f : Idx → Idx} (pd : p d)
    (hf : PartInj p f) : Mor L where
  d := d
  p := p
  ι := f
  τ := Term.varMap f
  f := Formula.varMap f
  pd := pd
  inj_ι := hf

def Formula.varMorAx {p f d} (pd : p d) (hf : PartInj p f) (c : VarContext L p) :
    MorAx (varMor L pd hf) c where
  map_τvars := Term.varMap_vars c.t
  map_fvars := Formula.varMap_vars c.φ
  map_falsum := rfl
  map_impl := rfl
  map_fall := rfl
  free_var h := by
    dsimp [varMor]
    have : ∀ i ∈ c.φ.fvar, p i := fun i h =>
      Set.mem_of_subset_of_mem c.hx <| Set.mem_of_subset_of_mem (fvar_subset_vars c.φ) h
    rw [varMap_fvar hf c.hx, hf.mem_set_image this c.hi]
    exact h
  free_for h := (varMap_FreeFor hf c.hi c.hx c.ht).mp h
  map_subst h := varMap_subst hf h c.hi c.hx c.ht
end map
end PrimaryLogic
