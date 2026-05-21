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

@[simp]
theorem Formula.safe_subst_equiv (i : Idx) (t : Term L) (φ : Formula L) (h : φ.FreeFor i t) :
    φ.subst i t = φ.safeSub i t h := by
  induction φ with
  | atom n args | falsum => simp only [subst, safeSub]
  | impl x y hx hy => simp only [subst, safeSub, impl.injEq]; exact ⟨hx h.left, hy h.right⟩
  | fall j x h' =>
    simp only [subst, safeSub]
    by_cases hi : i = j <;>
      simp only [hi, ↓reduceIte, ↓reduceDIte, fall.injEq, true_and];
      simp only [FreeFor] at h;
      apply h'

lemma Term.subst_self (i : Idx) (t : Term L) :
    Term.subst i (.var i) t = t := by
  induction t with
  | var j => simp [subst]
  | app n a h =>
    simp only [subst, app.injEq, heq_eq_eq, true_and]
    funext x
    exact h x

theorem Formula.subst_self (i : Idx) (φ : Formula L)
    (h : φ.FreeFor i (.var i)) : φ.safeSub i (.var i) h = φ := by
  induction φ with
  | atom n a =>
    simp only [safeSub, atom.injEq, heq_eq_eq, true_and]
    funext x
    exact Term.subst_self i (a x)
  | falsum => unfold safeSub; eq_refl
  | impl x y hx hy =>
    unfold safeSub;
    unfold FreeFor at h
    rw [hx h.left]
    rw [hy h.right]
  | fall j ψ h' =>
    simp only [safeSub, dite_eq_left_iff, fall.injEq, true_and]
    by_cases hi : i = j
    · intro hi; contradiction
    · intro _;
      unfold FreeFor at h
      rcases h with h1 | h2 | h3
      · exfalso; exact hi h1
      · exact h' (out_var_is_free_for_any_term (.var i) h2)
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

theorem Formula.subst_invariance {i : Idx} {t : Term L} {φ : Formula L} (h : φ.FreeFor i t) :
    i ∉ φ.fVars -> φ.safeSub i t h = φ := by
  intro hi
  induction φ with
  | atom n args =>
    simp only [safeSub, atom.injEq, heq_eq_eq, true_and]
    simp only [fVars, Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists] at hi
    funext x
    exact Term.subst_invariance i t (args x) (hi x)
  | falsum => dsimp only [safeSub]
  | impl x y hx hy =>
    simp only [safeSub, impl.injEq]
    simp only [fVars, Finset.mem_union, not_or] at hi
    dsimp only [FreeFor] at h
    exact ⟨hx h.left hi.left, hy h.right hi.right⟩
  | fall j x hx =>
    simp only [safeSub, dite_eq_left_iff, fall.injEq, true_and]
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

theorem Formula.subst_circulation (i j : Idx) (φ : Formula L) (hj : j ∉ φ.vars) :
    let ψ := safeSub i (.var j) φ <| term_FreeFor i (.var j) φ
      (by rw [Finset.inter_comm]; exact Finset.inter_singleton_of_notMem hj)
    ∃ h : FreeFor j (.var i) ψ, safeSub j (.var i) ψ h = φ := by
  induction φ with
  | atom n s =>
    use True.intro
    simp only [safeSub, atom.injEq, heq_eq_eq, true_and]
    simp only [vars, Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists] at hj
    funext k
    exact Term.subst_circulation i j _ (hj _)
  | falsum => use True.intro; dsimp [safeSub]
  | impl x y hx hy =>
    simp only [vars, Finset.mem_union, not_or] at hj
    dsimp only [safeSub]
    obtain ⟨hx1, hx2⟩ := hx hj.left
    obtain ⟨hy1, hy2⟩ := hy hj.right
    use ⟨hx1, hy1⟩
    congr
  | fall k x h =>
    simp only [vars, Finset.mem_insert, not_or] at hj
    have h' := Finset.notMem_mono (fVars_subset_vars _) hj.right
    dsimp only [safeSub]
    split_ifs with hi
    · simp only [FreeFor, Term.vars, Finset.mem_singleton]
      refine ⟨?_, ?_⟩
      · right; left; exact h'
      · dsimp [safeSub]
        split_ifs with hk
        · exfalso; exact hj.left hk
        · congr; exact subst_invariance _ h'
    · simp only [FreeFor, Term.vars, Finset.mem_singleton]
      obtain ⟨h1, h2⟩ := h hj.right
      refine ⟨?_, ?_⟩
      · right; right; exact ⟨ne_comm.mp hi, h1⟩
      · dsimp [safeSub]
        split_ifs with hk
        · exfalso; exact hj.left hk
        · rw [fall.injEq]; exact ⟨rfl, h2⟩

theorem Formula.loose_FreeFor (i : Idx) (t : Term L) (φ : Formula L) :
    FreeFor i t (φ.loose t i) := by
  induction φ with
  | atom | falsum => trivial
  | impl x y hx hy => unfold loose FreeFor; exact ⟨hx, hy⟩
  | fall j x h =>
    unfold loose FreeFor
    right; right; constructor
    · have : t.vars ⊆ insert i ((loose t i x).vars ∪ t.vars) :=
        subset_trans (Finset.subset_union_right ..) (Finset.subset_insert ..)
      exact Finset.not_mem_subset this <| Freshable.fresh_is_new _
    · sorry

section substFun
variable [DecidableEq LF]

theorem Term.fun_var_subst_distrib (i : Idx) (f : LF) (ir fr tr : Term L) : i ∉ fr.vars →
    substFun fr f (subst i ir tr) = subst i (substFun fr f ir) (substFun fr f tr) := by
  intro h0
  induction tr with
  | var j =>
    by_cases h : i = j <;> simp only [subst, h, substFun, ite_cond_eq_true, ite_cond_eq_false]
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
    Formula.substFun fr f (safeSub i ir φ h) =
      safeSub i (Term.substFun fr f ir) (Formula.substFun fr f φ) (substFun_FreeFor h h1 hb) := by
  induction φ with
  | atom p s =>
    simp only [safeSub, substFun, atom.injEq, heq_eq_eq, true_and]
    funext k; apply Term.fun_var_subst_distrib; exact h1
  | falsum => dsimp only [safeSub, substFun]
  | impl x y hx hy =>
    simp only [safeSub, substFun, impl.injEq]
    simp only [bVars, Finset.inter_union_distrib_left, Finset.union_eq_empty] at hb
    exact ⟨hx _ hb.left, hy _ hb.right⟩
  | fall j x h' =>
    dsimp only [safeSub, substFun]
    split_ifs with h1
    · rw [←h1]; dsimp only [substFun]
    · simp only [substFun, fall.injEq, true_and]
      simp only [FreeFor, h1, false_or] at h
      simp only [bVars, Finset.insert_inter] at hb
      split_ifs at hb with h5
      · exfalso; simp only [Finset.insert_ne_empty] at hb
      · rcases h with h2 | h3
        · have := out_var_is_free_for_any_term ir h2
          exact h' this hb
        · exact h' h3.right hb

open Finset in
def Formula.substFunMor (c : LF) (y : Term L) (s : Finset Idx) (h : y.vars ∩ s = ∅) :
    axiomMor (L := L) c s where
  τ := Term.substFun y c
  f := Formula.substFun y c
  map_falsum := rfl
  map_impl := fun _ _ => rfl
  map_fall := fun _ _ => rfl
  free_var := fun {i φ} h0 h1 h2 => by
    have : ∀ t : Term L, i ∉ t.vars → t.vars ⊆ s → i ∉ (Term.substFun y c t).vars :=
      fun t h3 h4 => by induction t with
      | var j => unfold Term.substFun; exact h3
      | app g as h5 =>
        unfold Term.substFun
        split_ifs
        · by_contra
          apply Finset.notMem_empty i
          exact h ▸ Finset.mem_inter_of_mem this h1
        · simp only [Term.vars, mem_biUnion, mem_univ, true_and, not_exists] at h3 ⊢
          simp only [Term.vars, biUnion_subset_iff_forall_subset, mem_univ, true_imp_iff] at h4
          intro x; exact h5 x (h3 x) (h4 x)
    induction φ with
    | atom p as =>
      simp only [vars, biUnion_subset_iff_forall_subset, mem_univ, true_imp_iff] at h2
      simp only [substFun, fVars, mem_biUnion, mem_univ, not_exists,
        not_and, true_imp_iff] at h0 ⊢
      intro x; exact this (as x) (h0 x) (h2 x)
    | falsum => unfold substFun fVars; exact notMem_empty i
    | impl x z hx hz =>
      unfold fVars at h0; unfold vars at h2
      unfold substFun fVars
      rw [union_subset_iff] at h2
      rw [notMem_union] at h0 ⊢
      exact ⟨hx h0.left h2.left, hz h0.right h2.right⟩
    | fall j x hx =>
      simp only [substFun, fVars, mem_erase, not_and]
      simp only [fVars, mem_erase, not_and] at h0
      simp only [vars, insert_subset_iff] at h2
      intro h3; exact hx (h0 h3) h2.right
  free_for := fun {i t φ} h0 h1 h2 => by
    apply substFun_FreeFor h0
    · by_contra
      apply notMem_empty i
      exact h ▸ mem_inter_of_mem this h1
    · apply subset_empty.mp
      exact h ▸ inter_subset_inter_left h2
  subst_comm := fun {i t φ} h0 h1 h2 => by
    apply Formula.fun_var_subst_distrib
    · by_contra
      apply notMem_empty i
      exact h ▸ mem_inter_of_mem this h1
    · apply subset_empty.mp
      exact h ▸ inter_subset_inter_left h2
end substFun

section close_formula

/-- Failed to apply `Finset.toList` for the sake of its noncomputable def,
  so that `Finset.sort` was used instead.
It takes me quite a while to complete the proof of `close_success` theorem,
  which seemes obvious for human but actually rather complicated to prove in Lean4.
There might be simpler proof, but anyway, it doesn't matter.
Honestly speaking, this section is bad implemented, as `Idx` becomes depending on `Nat` property,
  but I cannot come up with an easier way.
Generalized scheme that suits for other Idx type would make the proof more complicated,
  and I have to spend more time on the index handling, which is not the main topic of this project,
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

lemma Formula.quantifier_extract_free_var (i : Idx) (s : List Idx) (h : i ∉ s) (φ : Formula L) :
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
