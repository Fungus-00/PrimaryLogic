import PrimaryLogic.Encoding
import PrimaryLogic.FirstOrder.Theorem

namespace PrimaryLogic
variable {LF LP : Type} {L : Lang LF LP} (Γ : Set (Formula L))

section expand
variable {α : Type*} (f : Set α → Nat → Set α) (s : Set α)

def expand : Nat -> Set α
  | .zero => s
  | .succ n => f (expand n) n

theorem expand_monotone (hf : ∀ n, ∀ Δ, Δ ⊆ f Δ n) (m n : Nat) :
    m ≤ n -> expand f s m ⊆ expand f s n := by
  intro hm
  induction n with
  | zero => rw [Nat.le_zero.mp hm]
  | succ n h =>
    by_cases hn : m = n + 1
    · rw [hn]
    · have : m ≤ n := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hm hn)
      apply Set.Subset.trans (h this)
      simp only [expand]
      apply hf

def completeExpand := ⋃ n : Nat, expand f s n

variable {f : Set (Formula L) → Nat → Set (Formula L)} {Γ : Set (Formula L)}
theorem maximalSet_compact (hf : ∀ n, ∀ Δ, Δ ⊆ f Δ n) (φ : Formula L) :
    (completeExpand f Γ ⊢ φ) -> ∃ n : Nat, expand f Γ n ⊢ φ := by
  intro p
  induction p with
  | asp ψ hg =>
    unfold completeExpand at hg
    rw [Set.mem_union, Set.mem_iUnion] at hg
    rcases hg with ⟨n, h⟩ | h
    · use n
      apply Proof.asp ψ
      rw [Set.mem_union]
      left; exact h
    · use 0
      exact FOL.axiom_proof h
  | @mp ψ χ p q hp hq =>
    obtain ⟨m, hm⟩ := hp
    obtain ⟨n, hn⟩ := hq
    use max m n
    have := expand_monotone f Γ hf m (max m n) (Nat.le_max_left m n)
    have h1 := FOL.mono this hm
    have := expand_monotone f Γ hf n (max m n) (Nat.le_max_right m n)
    have h2 := FOL.mono this hn
    exact Proof.mp h1 h2
end expand

section maximal_con
abbrev InCon : Prop := Inconsistent (Γ ∪ FOLTheory)
abbrev Con : Prop := Consistent (Γ ∪ FOLTheory)

def MaximalConsistent : Prop := Con Γ ∧ (∀ φ, φ ∈ Γ ∨ (¬φ) ∈ Γ)

theorem maxConSet_iff (Γ : Set (Formula L)) (φ : Formula L) :
    MaximalConsistent Γ -> (φ ∈ Γ ↔ (Γ ⊢ φ)) := by
  intro m
  open Proof in
  constructor
  · intro h
    exact FOL.AS h
  · intro h
    have h' : (¬φ) ∉ Γ := by
      by_contra
      have p1 := FOL.AS this
      have p2 := mp p1 h
      exact m.left p2
    rcases m.right φ with h1 | h2
    · exact h1
    · exfalso; exact h' h2

variable [Encodable LF] [Encodable LP] [DecidablePred (InCon (L := L))]

def tryAdd (n : Nat) : Set (Formula L) :=
  match Encodable.decode (α := Formula L) n with
  | none => Γ
  | some φ => if InCon (Γ.insert φ)
    then Γ.insert (¬φ) else Γ.insert φ

def expandM (Γ : Set (Formula L)) : Nat -> Set (Formula L) :=
  expand (fun x => tryAdd (L := L) x) Γ

lemma tryAdd_con_valid (n : Nat) : Con Γ -> Con (tryAdd Γ n) := by
  intro h
  cases h1 : Encodable.decode (α := Formula L) n with
  | none => simp only [tryAdd, h1]; exact h
  | some φ =>
    simp only [tryAdd, h1]
    unfold Con Consistent Inconsistent at h
    split_ifs with h2
    · unfold Con Consistent
      rw [←Proof.raa]
      unfold InCon Inconsistent at h2
      have h3 := (Proof.deduction Γ φ .falsum).mp h2
      by_contra
      have := Proof.mp h3 this
      contradiction
    · exact h2

lemma expandAdd_con_valid (n : Nat) : Con Γ -> Con (expandM Γ n) := by
  intro h
  induction n with
  | zero => unfold expandM; exact h
  | succ n hn => unfold expandM; exact tryAdd_con_valid _ n hn

lemma tryAdd_monotone (n : Nat) (Δ : Set (Formula L)) : Δ ⊆ tryAdd Δ n := by
  cases h' : Encodable.decode (α := Formula L) n with
  | none => simp only [tryAdd, h', Set.Subset.refl]
  | some φ => simp only [tryAdd, h']; split_ifs <;> exact Set.subset_insert _ Δ

private abbrev maxExpand := completeExpand (tryAdd (L := L) ·)

theorem Lindenbaum : Con Γ -> MaximalConsistent (maxExpand Γ) := by
  intro h
  unfold MaximalConsistent
  split_ands
  · by_contra
    unfold Inconsistent at this
    obtain ⟨n, p⟩ := maximalSet_compact tryAdd_monotone ⊥ this
    have := expandAdd_con_valid Γ n h
    contradiction
  · intro φ
    rcases lem (φ ∈ maxExpand Γ) with h1 | h1
    · left; exact h1
    · right; unfold maxExpand completeExpand at h1
      rw [Set.mem_iUnion, not_exists] at h1
      let n := Encodable.encode (α := Formula L) φ
      refine Set.mem_iUnion.mpr ⟨n.succ, ?_⟩
      have h2 : Encodable.decode n = some φ := Encodable.encodek φ
      simp only [expand, tryAdd, h2]
      by_cases h4 : InCon (Set.insert φ (expand (fun x ↦ tryAdd x) Γ n))
      · simp only [h4]; apply Set.mem_insert
      · have h3 := h1 n.succ
        simp only [expand, tryAdd, h2, h4] at h3
        have := Set.mem_insert φ (expandM Γ n)
        contradiction
end maximal_con

def ProofTree.transform {m : Mor L} (η : (c : VarContext L m.p) → MorAx m c) {φ : Formula L}
    (t : ProofTree (FOLAxioms L) Γ φ) (hp : ∀ i ∈ t.varList, m.p i) :
    ProofTree (FOLAxioms L) (m.f '' Γ) (m.f φ) :=
  match t with
  | .asp ψ h => .asp (m.f ψ) <| (Set.mem_image ..).mp ⟨ψ, h, rfl⟩
  | .axm a => FOLAxioms.transform_eq η a (fun i h => hp i <| (FOLAxioms.vars_eq_list ..).mp h)
    ▸ .axm (Γ := m.f '' Γ) (a.transform η _)
  | .mp (φ := x) (ψ := y) p1 p2 =>
    have hv : x.vars ⊆ m.p ∧ y.vars ⊆ m.p := Set.union_subset_iff.mp
      fun i h => hp i
      <| List.mem_append.mpr
      <| Or.inl
      <| (List.subset_def.mp <| ProofTree.mem_target_varList p1)
      <| (Formula.vars_eq_list ..).mp
      <| Or.elim h (.inl ·) (.inr ·)
    have he : m.f (x → y) = ((m.f x) → (m.f y)) := MorAx.map_impl <| FOLAxioms.gm η
      (x := ⟨x, hv.1⟩) (y := ⟨y, hv.2⟩)
    .mp (φ := m.f x) (ψ := m.f y)
      (he ▸ transform η p1 fun i h => hp i <| List.mem_append.mpr <| Or.inl h)
      (transform η p2 fun i h => hp i <| List.mem_append.mpr <| Or.inr h)

def ProofTree.map {p} [DecidablePred p] [fr : Freshable (Subtype p)] {f : Idx → Idx}
    (hf : PartInj p f) {Γ : Set (Formula L)} (hΓ : ∀ φ ∈ Γ, φ.vars ⊆ p) {φ : Formula L}
    (hφ : φ.vars ⊆ p) : ProofTree (FOLAxioms L) Γ φ ->
    ProofTree (FOLAxioms L) ((Formula.varMap f) '' Γ) (Formula.varMap f φ) := fun t =>
  let d := (fr.fresh []).val
  let s := d :: t.varList
  let q (i : Idx) : Prop := i ∈ s
  let g (i : Idx) : Idx := f <| (s.canonize p i).val
  let h' : PartInj q g := fun {x y} hx hy he => List.canonize_PartInj s hx hy
    <| Subtype.ext <| hf (s.canonize p x).prop (s.canonize p y).prop he
  let m : Mor L := Formula.varMor L List.mem_cons_self h'
  let η (c : VarContext L m.p) : MorAx m c := Formula.varMorAx List.mem_cons_self h' c
  have h1 : Formula.varMap g '' t.assumptions = Formula.varMap f '' t.assumptions :=
    Set.image_eq_from fun ψ h => Formula.varMap_eq fun i hi => congrArg f
    <| Subtype.ext_iff.mp
    <| List.canonize_invariance
      (List.mem_cons_of_mem d
      <| assumptions_vars_subset t ψ h
      <| (Formula.vars_eq_list ..).mp hi)
    <| (Set.subset_def ▸ hΓ ψ <| assumptions_subset t h) i hi
  have h2 : Formula.varMap g φ = Formula.varMap f φ :=
    Formula.varMap_eq fun i hi => congrArg f
    <| Subtype.ext_iff.mp
    <| List.canonize_invariance
      (List.mem_cons_of_mem d <| mem_target_varList t <| (Formula.vars_eq_list ..).mp hi)
    <| (Set.subset_def ▸ hφ) i hi
  let r : ProofTree (FOLAxioms L) (Formula.varMap f '' t.assumptions) (Formula.varMap f φ) :=
    h1 ▸ h2 ▸ transform t.assumptions η t.compress
      fun _ h => List.mem_cons_of_mem d (compress_varList_eq t ▸ h)
  monotone (Set.image_mono' <| assumptions_subset t) r

def ffresh {α : Type*} [fr : Freshable α] (ρ : Nat → Option (List α)) : Nat → List α
  | .zero => []
  | .succ n => match ρ n with
    | none => ffresh ρ n
    | some s => let l := s ++ ffresh ρ n; fr.fresh l :: l

lemma ffresh_notMem {α : Type*} [fr : Freshable α] (ρ : Nat → Option (List α)) {m n : Nat} :
    m < n → match ρ m with | some s => s ⊆ ffresh ρ n | none => True := fun h =>
  match hv : ρ m with | none => True.intro | some s => by induction n generalizing m with
  | zero => exfalso; exact Nat.not_lt_zero m h
  | succ n hn =>
    dsimp
    unfold ffresh
    rw [Nat.lt_add_one_iff, Nat.le_iff_lt_or_eq] at h
    rcases h with h | h
    · cases ρ n with
      | none => exact hn h hv
      | some l =>
        dsimp only [Lean.Elab.WF.paramLet]
        apply List.subset_cons_of_subset
        apply List.subset_append_of_subset_right
        exact hn h hv
    · subst h
      cases hu : ρ m with
      | none => exfalso; rw [hv] at hu; simp at hu
      | some l =>
        dsimp only [Lean.Elab.WF.paramLet]
        rw [hv, Option.some_inj] at hu
        rw [hu]
        apply List.subset_cons_of_subset
        apply List.subset_append_of_subset_left
        apply List.Subset.refl

section Henkin
variable (p : Idx → Prop) [fr : Freshable (Subtype p)]
instance [Encodable LP] [Encodable LF] : Encodable (Idx × Formula L) := inferInstance

def newVar (ρ : Nat → (Option <| List <| Subtype p)) (n : Nat) (h : (ρ n).isSome) : Subtype p :=
  fr.fresh <| (ρ n).get h ++ ffresh ρ n

lemma newVar_mem_ffresh {ρ : Nat → (Option <| List <| Subtype p)} {m n : Nat} (h0 : m < n)
    (hm : (ρ m).isSome) : newVar p ρ m hm ∈ ffresh ρ n := by
  induction n with
  | zero => exfalso; exact Nat.not_lt_zero m h0
  | succ n hn =>
    unfold ffresh
    rw [Nat.lt_add_one_iff, Nat.le_iff_lt_or_eq] at h0
    cases hv : ρ n with
    | none =>
      dsimp
      rcases h0 with h0 | h0
      · exact hn h0
      · exfalso; rwa [h0, hv, Option.isSome_none, Bool.false_eq_true] at hm
    | some t =>
      dsimp
      rcases h0 with h0 | h0
      · apply List.mem_cons_of_mem
        apply List.mem_append_right
        exact hn h0
      · subst h0; unfold newVar; rw [List.mem_cons]
        left; congr; simp only [hv, Option.get_some]

lemma newVar_uni {ρ : Nat → (Option <| List <| Subtype p)} {m n : Nat} (h0 : m < n)
    (hm : (ρ m).isSome) (hn : (ρ n).isSome) : newVar p ρ m hm ≠ newVar p ρ n hn := fun h => by
  have h1 := newVar_mem_ffresh p h0 hm
  rw [h] at h1
  unfold newVar at h1
  apply Freshable.fresh_is_new ((ρ n).get hn ++ ffresh ρ n)
  exact List.mem_append_right _ h1

variable [DecidablePred p]

def varGet (f : Nat → Option (Formula L)) (n : Nat) : Option <| List <| Subtype p :=
  Option.map (List.pass p <| Formula.varList <| ·) (f n)

def newTerm (f : Nat → Option (Formula L)) (n : Nat) (h : (f n).isSome) : Term L :=
  .var <| Subtype.val <| newVar p (varGet p f) n <| by
    dsimp [varGet]; rw [Option.isSome_map]; exact h

lemma newTerm_vars (f : Nat → Option (Formula L)) (n : Nat) (h : (f n).isSome) :
    (newTerm p f n h).vars ∩ ((f n).get h).vars = ∅ := by
  dsimp [newTerm, Term.vars]
  rw [Set.singleton_inter_eq_empty]
  intro h'
  have hl := List.pass_valid ((Formula.vars_eq_list ..).mp h') (Subtype.prop _)
  rw [Subtype.coe_eta] at hl
  simp only [newVar, varGet, Option.get_map] at hl
  exact fr.fresh_is_new _ <| List.mem_append_left _ <| hl

lemma newTerm_gvars (f : Nat → Option (Formula L)) {m n : Nat} (h0 : m < n)
    (hm : (f m).isSome) (hn : (f n).isSome) :
    (newTerm p f n hn).vars ∩ ((f m).get hm).vars = ∅ := by
  dsimp [newTerm, Term.vars, newVar]
  rw [Set.singleton_inter_eq_empty]
  intro h'
  rw [Formula.vars_eq_list] at h'
  replace h' := List.pass_valid h' (Subtype.prop _)
  rw [Subtype.coe_eta] at h'
  have h := ffresh_notMem (varGet p f) h0
  cases hm' : f m with
  | none => simp only [hm', Option.isSome_none, Bool.false_eq_true] at hm
  | some a => cases hn' : f n with
    | none => simp only [hn', Option.isSome_none, Bool.false_eq_true] at hn
    | some b =>
      simp only [varGet, hm', hn', Option.map_some, Option.get_some] at h'
      simp only [varGet, hm', Option.map_some] at h
      replace h := List.subset_append_of_subset_right (List.pass p b.varList) h
      rw [List.subset_def] at h
      exact Freshable.fresh_is_new _ (h h')

lemma newTerm_disjoint (f : Nat → Option (Formula L)) {m n : Nat} (h0 : m < n)
    (hm : (f m).isSome) (hn : (f n).isSome) :
    (newTerm p f m hm).vars ∩ (newTerm p f n hn).vars = ∅ := by
  dsimp [newTerm, Term.vars]
  rw [Set.singleton_inter_eq_empty, Set.mem_singleton_iff, ←Subtype.ext_iff]
  apply newVar_uni p h0

private abbrev dc {LF LP : Type} [Encodable LP] [Encodable LF] (L : Lang LF LP) :=
  Encodable.decode (α := Idx × Formula L)

variable [Encodable LP] [Encodable LF]

def forGet (n : Nat) : Option (Formula L) := Option.map (fun x => Formula.fall (x.1) x.2) (dc L n)

def Formula.henkinTerm (n : Nat) (h : (dc L n).isSome) : Term L :=
  newTerm p forGet n <| by simp only [forGet, Option.isSome_map]; exact h

lemma Formula.henkinTerm_vars (n : Nat) (h : (dc L n).isSome) :
    (henkinTerm p n h).vars ∩ ((dc L n).get h).2.vars = ∅ := by
  unfold henkinTerm
  have hb := newTerm_vars p forGet n <| by
    simp only [forGet, Option.isSome_map]; exact h
  conv at hb => lhs; rhs; simp only [forGet, Option.get_map, Formula.vars]
  rw [Set.insert_eq, Set.inter_union_distrib_left, Set.union_eq_empty] at hb
  exact hb.2

lemma henkinTerm_gvars {m n : Nat} (h0 : m < n) (hm : (dc L m).isSome) (hn : (dc L n).isSome) :
    let x := (dc L m).get hm; (Formula.henkinTerm p n hn).vars ∩
    ((insert x.1 x.2.vars) ∪ (Formula.henkinTerm p m hm).vars) = ∅ := by
  unfold Formula.henkinTerm
  let m' := dc L m
  let n' := dc L n
  cases hm' : m' with
  | none => simp only [m', hm', Option.isSome_none, Bool.false_eq_true] at hm
  | some a => cases hn' : n' with
    | none => simp only [n', hn', Option.isSome_none, Bool.false_eq_true] at hn
    | some b =>
      unfold m' at hm'
      unfold n' at hn'
      simp only [hm', Option.get_some, Set.inter_union_distrib_left, Set.union_eq_empty]
      have hm1 : Option.isSome <| Option.map (fun x ↦ Formula.fall x.1 x.2) (dc L m) := by
        simp only [hm', Option.map_some, Option.isSome_some]
      have hn1 : Option.isSome <| Option.map (fun x ↦ Formula.fall x.1 x.2) (dc L n) := by
        simp only [hn', Option.map_some, Option.isSome_some]
      split_ands
      · have h := newTerm_gvars p forGet h0 hm1 hn1
        conv at h => lhs; rhs; simp only [forGet, hm', Option.map, Option.get_some, Formula.vars]
        exact h
      · exact Set.inter_comm .. ▸ newTerm_disjoint p forGet h0 hm1 hn1

def Formula.henkinForm (i : Idx) (t : Term L) (φ : Formula L) (h : FreeFor i t φ) : Formula L :=
  (¬∀i# φ) → ¬(subst i t φ h)

def Formula.henkinfy (n : Nat) (h : (dc L n).isSome) :
    Formula L :=
  let x := (dc L n).get h
  Formula.henkinForm x.1 (henkinTerm p n h) x.2
  <| Formula.term_FreeFor _ _ _ <| Formula.henkinTerm_vars ..

def henkinAdd (Γ : Set (Formula L)) (n : Nat) : Set (Formula L) :=
  if h : (dc L n).isSome then insert (Formula.henkinfy p n h) Γ else Γ

lemma henkinAdd_monotone (n : Nat) (Δ : Set (Formula L)) : Δ ⊆ henkinAdd p Δ n := by
  cases h' : Encodable.decode (α := Idx × Formula L) n with
  | none => simp only [henkinAdd, h', Option.isSome_none, Bool.false_eq_true,
    ↓reduceDIte, subset_refl]
  | some φ => simp only [henkinAdd, h']; exact Set.subset_insert _ Δ

theorem henkinExpand_ord {n : Nat} {g : Formula L} (hg : g ∈ expand (henkinAdd p) Γ n) :
    g ∈ Γ ∨ ∃ m : Nat, ∃ hm : (dc L m).isSome, m < n ∧ Formula.henkinfy p m hm = g := by
  induction n with
  | zero => unfold expand at hg; left; exact hg
  | succ n hn =>
    dsimp [expand, henkinAdd] at hg
    split_ifs at hg with h'
    · rw [Set.mem_insert_iff] at hg
      rcases hg with h1 | h2
      · right; use n; use h'; refine ⟨Nat.lt_add_one n, ?_⟩
        let n' := dc L n
        cases hn' : n' with
        | none => unfold n' at hn'; exfalso; rwa [hn', Option.isSome_none, Bool.false_eq_true] at h'
        | some a => unfold n' at hn'; rw [h1]
      · refine Or.elim (hn h2) Or.inl fun ⟨m, hm, h3, h4⟩ => ?_
        right; use m; use hm; exact ⟨Nat.lt_trans h3 (Nat.lt_add_one n), h4⟩
    · refine Or.elim (hn hg) Or.inl fun ⟨m, hm, h3, h4⟩ => ?_
      right; use m; use hm; exact ⟨Nat.lt_trans h3 (Nat.lt_add_one n), h4⟩

theorem henkinExpand_vars {n : Nat} {g : Formula L} (hn : (dc L n).isSome)
    (hg : g ∈ expand (henkinAdd p) Γ n) :
    g ∈ Γ ∨ (Formula.henkinTerm p n hn).vars ∩ g.vars = ∅ := by
  refine Or.elim (henkinExpand_ord Γ p hg) Or.inl fun ⟨m, hm, h1, h2⟩ => ?_
  right; rw [←h2]; unfold Formula.henkinfy
  let m' := dc L m
  cases h' : m' with
  | none => simp only [m', h', Option.isSome_none, Bool.false_eq_true] at hm
  | some x =>
    unfold m' at h'
    simp only [h', Option.get_some, Formula.henkinForm, Formula.vars, Formula.not,
      Set.union_empty, ←Set.disjoint_iff_inter_eq_empty]
    have h3 := Formula.henkinTerm_vars p m hm
    simp only [h', Option.get_some] at h3
    have h4 := Formula.subst_vars (i := x.1) (t := Formula.henkinTerm p m hm) (φ := x.2) <|
      Formula.term_FreeFor _ _ _ h3
    apply Set.disjoint_of_subset_right <| Set.union_subset_union_right _ h4
    conv =>
      arg 2
      conv => arg 2; rw [Set.union_comm]
      rw [←Set.union_assoc, Set.insert_union', Set.union_self]
    rw [Set.disjoint_iff_inter_eq_empty]
    have h5 := henkinTerm_gvars p h1 hm hn
    simpa only [h', Option.get_some] using h5

private abbrev henkinExpand := completeExpand (henkinAdd p (L := L) ·)

set_option linter.unusedDecidableInType false in
theorem Henkinbaum [hd : DecidablePred (InCon (L := L))] (hg : ∀ g ∈ Γ, g.vars ∩ p = ∅) :
    Con Γ -> Con (henkinExpand p Γ) := by
  intro h'; by_contra h
  unfold henkinExpand completeExpand Inconsistent at h
  replace h := maximalSet_compact (henkinAdd_monotone p) ⊥ h
  have ⟨m, h1, h2⟩ := @Nat.findX _ (fun n => hd <| expand (henkinAdd p) Γ n) h
  unfold InCon Inconsistent expand at h1
  match hm : m with
  | .zero => exact h' h1
  | .succ n => match hn : Encodable.decode n (α := Idx × Formula L) with
    | .none =>
      simp only [henkinAdd, hn] at h1
      exact h2 n (Nat.lt_succ_self n) h1
    | .some ⟨i, φ⟩ =>
      simp only [henkinAdd, hn, insert, Option.isSome_some, ↓reduceDIte, Proof.deduction] at h1
      unfold Formula.henkinfy Formula.henkinForm at h1
      have h3 := Proof.mp (Proof.neg_of_impl_left _ _) h1
      have h4 := Proof.mp (Proof.neg_of_impl_right _ _) h1
      replace h4 := Proof.mp (FOL.AX _ (.h3 _)) h4
      unfold Formula.henkinTerm newTerm at h4
      apply h2 n <| Nat.lt_succ_self n
      apply Proof.mp h3
      simp only [dc, hn, Option.get_some] at h4 ⊢
      refine Proof.mp (Proof.monotone (Set.empty_union _ ▸ Set.subset_union_right)
        (Proof.all_impl_subst i _ ?_)) <| Proof.gen_rule _ _ _ ?_ h4
      · intro h5
        have h6 := Formula.henkinTerm_vars (L := L) p n <| by
          simp only [dc, hn, Option.isSome_some]
        unfold Formula.henkinTerm newTerm Term.vars at h6
        simp only [dc, hn, Option.get_some, Set.singleton_inter_eq_empty] at h6
        exact h6 h5
      · intro ψ h5 h6
        replace h6 := Formula.fvar_subset_vars ψ h6
        have h7 := hn ▸ Option.isSome_some
        rcases henkinExpand_vars Γ p h7 h5 with h0 | h0
        · have h8 := hg ψ h0
          exact Set.notMem_empty _ <| h8 ▸ Set.mem_inter h6 (Subtype.prop _)
        · unfold Formula.henkinTerm newTerm Term.vars at h0
          rw [Set.singleton_inter_eq_empty] at h0
          exact h0 h6

end Henkin
end PrimaryLogic
