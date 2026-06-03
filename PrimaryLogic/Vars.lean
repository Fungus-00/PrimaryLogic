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

variable (p : Idx -> Prop) (f : Idx -> Idx)
def Term.varMap : Term L -> Term L
  | var i => .var (f i)
  | app n s => .app n fun k => varMap (s k)

def Formula.varMap (φ : Formula L) : Formula L :=
  match φ with
  | atom n s => atom n fun k => Term.varMap f (s k)
  | falsum => falsum
  | impl ψ χ => impl (varMap ψ) (varMap χ)
  | fall i ψ => fall (f i) <| varMap ψ

variable {p : Idx -> Prop} {f : Idx -> Idx}

lemma Term.varMap_vars (t : Term L) :
    (varMap f t).vars = t.vars.image f := by
  induction t with
  | var i => unfold varMap vars; rw [Set.image_singleton']
  | app n s h =>
    unfold varMap vars
    rw [Set.image_iUnion]
    dsimp
    conv => lhs; arg 1; intro k; rw [h k]

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

lemma Formula.varMap_fvar {φ : Formula L} (hf : PartInj p f) (hi : φ.av p) :
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
    simp only [av, vars, Set.mem_union] at hi
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
      unfold av at hi
      apply hi
      unfold vars
      apply Set.mem_insert_of_mem
      refine Set.mem_of_subset_of_mem ?_ hx
      apply fvar_subset_vars
    · intro x hx
      unfold av vars at hi
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hi i (Set.mem_insert ..)

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
  ι : Idx -> Idx
  τ : Term L -> Term L
  f : Formula L -> Formula L
  inj_ι : PartInj p ι

open Formula Set in
structure MorAx (m : Mor L) (c : VarContext L m.p) : Prop where
  map_falsum : m.f falsum = falsum
  map_impl : m.f (impl c.φ c.ψ) = impl (m.f c.φ) (m.f c.ψ)
  map_fall : m.f (fall c.i c.φ) = fall (m.ι c.i) (m.f c.φ)
  free_var : c.i ∉ c.φ.fvar → (m.ι c.i) ∉ (m.f c.φ).fvar
  free_for : FreeFor c.i c.t c.φ → FreeFor (m.ι c.i) (m.τ c.t) (m.f c.φ)
  map_subst (h) :
    m.f (subst c.i c.t c.φ h) = subst (m.ι c.i) (m.τ c.t) (m.f c.φ) (free_for h)

def Formula.varMor {p} {f : Idx → Idx} (hf : PartInj p f) (L : Lang LF LP) : Mor L where
  p := p
  ι := f
  τ := Term.varMap f
  f := Formula.varMap f
  inj_ι := hf

def Formula.varMorAx {p f} (hf : PartInj p f) (c : VarContext L p) :
    MorAx (varMor hf L) c where
  map_falsum := rfl
  map_impl := rfl
  map_fall := rfl
  free_var h := by
    dsimp [varMor]
    have : ∀ i ∈ c.φ.fvar, p i := fun i h =>
      c.hx i <| Set.mem_of_subset_of_mem (fvar_subset_vars ..) h
    rw [varMap_fvar hf c.hx, hf.mem_set_image this c.hi]
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

lemma Term.substFun_not_mem_fvar {i : Idx} {f : LF} {fr tr : Term L} :
    i ∉ fr.vars → i ∉ tr.vars → i ∉ (substFun fr f tr).vars := by
  intro h0 h1
  induction tr with
  | var j =>
    dsimp only [vars] at h1
    dsimp only [substFun, vars]
    exact h1
  | app g s h =>
    simp only [vars, Set.mem_iUnion, not_exists] at h1
    dsimp only [substFun]
    split_ifs with h2
    · exact h0
    · simp only [vars, Set.mem_iUnion, not_exists]
      intro x; exact h x <| h1 x

lemma Formula.substFun_not_mem_fvar {i : Idx} {f : LF} {fr : Term L} {φ : Formula L} :
    i ∉ fr.vars → i ∉ φ.fvar → i ∉ (substFun fr f φ).fvar := by
  intro h0 h1
  induction φ with
  | atom n p =>
    simp only [substFun, fvar, Set.mem_iUnion, not_exists]
    simp only [fvar, Set.mem_iUnion, not_exists] at h1
    intro x; exact Term.substFun_not_mem_fvar h0 (h1 x)
  | falsum => dsimp only [substFun, fvar, Set.notMem_empty]; trivial
  | impl x y hx hy =>
    simp only [substFun, fvar, Set.mem_union, not_or]
    simp only [fvar, Set.mem_union, not_or] at h1
    exact ⟨hx h1.left, hy h1.right⟩
  | fall j x h' =>
    rw [Decidable.not_imp_not] at h'
    simp only [substFun, fvar, Set.mem_diff, not_and]
    simp only [fvar, Set.mem_diff, not_and] at h1
    intro h; exact h1 (h' h)

lemma Formula.substFun_FreeFor {i : Idx} {f : LF} {ir fr : Term L} {φ : Formula L}
    (hi : FreeFor i ir φ) (h : i ∉ fr.vars) (hb : fr.vars ∩ φ.bvar = ∅) :
      FreeFor i (Term.substFun fr f ir) (Formula.substFun fr f φ) := by
  induction φ with
  | atom p s | falsum => dsimp only [Formula.substFun, FreeFor]
  | impl x y hx hy =>
    dsimp only [Formula.substFun, FreeFor]
    have ⟨h1, h2⟩ := hi
    simp only [bvar, Set.inter_union_distrib_left, Set.union_eq_empty] at hb
    exact ⟨hx h1 hb.left, hy h2 hb.right⟩
  | fall j x h' =>
    dsimp only [Formula.substFun, FreeFor]
    dsimp [FreeFor] at hi
    rcases hi with h1 | h2 | ⟨h3, h4⟩
    · left; exact h1
    · right; left; exact Formula.substFun_not_mem_fvar h h2
    · right; right; constructor
      · refine Term.substFun_not_mem_fvar ?_ h3
        unfold bvar at hb
        by_contra
        have h5 := Set.mem_insert j x.bvar
        have h6 := hb ▸ Set.mem_inter this h5
        have h7 := Set.notMem_empty j
        contradiction
      · simp only [bvar, Set.insert_eq, Set.inter_union_distrib_left, Set.union_eq_empty] at hb
        exact h' h4 hb.2

theorem Formula.fun_var_subst_distrib (i : Idx) (f : LF) (ir fr : Term L) (φ : Formula L)
    (h : FreeFor i ir φ) (h1 : i ∉ fr.vars) (hb : fr.vars ∩ φ.bvar = ∅) :
    Formula.substFun fr f (subst i ir φ h) =
      subst i (Term.substFun fr f ir) (substFun fr f φ) (substFun_FreeFor h h1 hb) := by
  induction φ with
  | atom p s =>
    simp only [subst, substFun, atom.injEq, heq_eq_eq, true_and]
    funext k; apply Term.fun_var_subst_distrib; exact h1
  | falsum => dsimp only [subst, substFun]
  | impl x y hx hy =>
    simp only [subst, substFun, impl.injEq]
    simp only [bvar, Set.inter_union_distrib_left, Set.union_eq_empty] at hb
    exact ⟨hx _ hb.left, hy _ hb.right⟩
  | fall j x h' =>
    dsimp only [subst, substFun]
    split_ifs with h1
    · rw [←h1]; dsimp only [substFun]
    · simp only [substFun, fall.injEq, true_and]
      simp only [FreeFor, h1, false_or] at h
      simp only [bvar, Set.insert_eq, Set.inter_union_distrib_left, Set.union_eq_empty] at hb
      rcases h with h2 | h3
      · have := out_var_FreeFor_term ir h2
        exact h' this hb.2
      · exact h' h3.right hb.2
end substFun
end PrimaryLogic
