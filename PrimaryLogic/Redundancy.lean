import PrimaryLogic.Vars

namespace PrimaryLogic
variable {LF LP : Type} {L : Lang LF LP}
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
