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
        dsimp
        apply List.subset_cons_of_subset
        apply List.subset_append_of_subset_right
        exact hn h hv
    · subst h
      cases hu : ρ m with
      | none => exfalso; rw [hv] at hu; simp at hu
      | some l =>
        dsimp
        rw [hv, Option.some_inj] at hu
        rw [hu]
        apply List.subset_cons_of_subset
        apply List.subset_append_of_subset_left
        apply List.Subset.refl

section Henkin
variable (p : Idx → Prop) [DecidablePred p] [fr : Freshable (Subtype p)]

def newVar (n : Nat) (ρ : Nat → (Option <| List <| Subtype p)) : Subtype p :=
  fr.fresh <| (ρ n).getD [] ++ ffresh ρ n

def newTerm (f : Nat → Option (Formula L)) (n : Nat) : Term L :=
  .var <| Subtype.val <| newVar p n fun k => List.pass p <$> Formula.varList <$> f k

lemma newTerm_vars (f : Nat → Option (Formula L)) (n : Nat) :
    match f n with | some φ => (newTerm p f n).vars ∩ φ.vars = ∅ | none => True :=
  match hn : f n with
  | none => True.intro
  | some φ => by
    dsimp [newTerm, Term.vars]
    rw [Set.singleton_inter_eq_empty]
    intro h'
    have h := List.pass_valid ((Formula.vars_eq_list ..).mp h') (Subtype.prop _)
    rw [Subtype.coe_eta] at h
    unfold newVar at h
    simp only [hn, Option.map_some, Option.getD_some, Option.map_map] at h
    exact fr.fresh_is_new _ <| List.mem_append_left _ <| h

lemma newTerm_gvars (f : Nat → Option (Formula L)) {m n : Nat} (h0 : m < n) :
    match f n, f m with | some _, some ψ => (newTerm p f n).vars ∩ ψ.vars = ∅ | _, _ => True :=
  match hn : f n, hm : f m with
  | some φ, some ψ => by
    dsimp [newTerm, Term.vars, newVar]
    rw [Set.singleton_inter_eq_empty, hn]
    intro h'
    rw [Formula.vars_eq_list, Option.map_some, Option.map_some, Option.getD_some] at h'
    replace h' := List.pass_valid h' (Subtype.prop _)
    rw [Subtype.coe_eta] at h'
    have h := ffresh_notMem (fun k ↦ Option.map (List.pass p) (Option.map Formula.varList (f k))) h0
    simp only [hm, Option.map_some] at h
    replace h := List.subset_append_of_subset_right (List.pass p φ.varList) h
    rw [List.subset_def] at h
    exact Freshable.fresh_is_new _ (h h')
  | none, some _ | some _, none | none, none => True.intro

def Formula.henkin (i : Idx) (t : Term L) (φ : Formula L) (h : FreeFor i t φ) : Formula L :=
  (¬∀i# φ) → ¬(subst i t φ h)

instance [Encodable LP] [Encodable LF] : Encodable (Idx × Formula L) := inferInstance

variable [Encodable LP] [Encodable LF]
def Formula.henkinTerm (i : Idx) (φ : Formula L) : Term L :=
  newTerm p (Prod.snd <$> Encodable.decode (α := Idx × Formula L) ·) (Encodable.encode (i, φ))

lemma Formula.henkinTerm_vars (i : Idx) (φ : Formula L) :
    (henkinTerm p i φ).vars ∩ φ.vars = ∅ := by
  have h : Prod.snd <$> Encodable.decode (α := Idx × Formula L) ((Encodable.encode (i, φ)))
      = φ := by simp only [Encodable.encode_prod_val', Encodable.encode_nat,
    Encodable.decode_prod_val', Nat.unpair_pair', Encodable.decode_nat,
    Encodable.encodek, Option.map_some, Option.bind_some, Option.map_eq_map]
  have h2 := h ▸ newTerm_vars p (Prod.snd <$> Encodable.decode (α := Idx × Formula L) ·)
    (Encodable.encode (i, φ))
  unfold henkinTerm
  dsimp only [Option.map_eq_map, Encodable.encode_prod_val, Encodable.encode_nat] at h2
  exact h2

def Formula.henkinfy (i : Idx) (φ : Formula L) : Formula L :=
  henkin i (henkinTerm p i φ) φ <| Formula.term_FreeFor _ _ _ <| henkinTerm_vars ..

def henkinAdd (Γ : Set (Formula L)) (n : Nat) : Set (Formula L) :=
  match Encodable.decode n (α := Idx × Formula L) with
  | .none => Γ
  | .some ⟨i, φ⟩ => insert (Formula.henkinfy p i φ) Γ

lemma henkinAdd_monotone (n : Nat) (Δ : Set (Formula L)) : Δ ⊆ henkinAdd p Δ n := by
  cases h' : Encodable.decode (α := Idx × Formula L) n with
  | none => simp only [henkinAdd, h', Set.Subset.refl]
  | some φ => simp only [henkinAdd, h']; exact Set.subset_insert _ Δ

theorem henkinTerm_gvars {i j : Idx} {φ ψ : Formula L}
    (h0 : Encodable.encode (j, ψ) < Encodable.encode (i, φ)) :
    (Formula.henkinTerm p i φ).vars ∩ ψ.vars = ∅ := by
  unfold Formula.henkinTerm
  have h1 := newTerm_gvars p (fun x ↦ Prod.snd <$> Encodable.decode (α := Idx × Formula L) x) h0
  simp only [Encodable.encodek, Option.map_eq_map, Option.map_some] at h1
  dsimp only [Option.map_eq_map]
  exact h1

theorem henkinExpand_ord0 {Γ : Set (Formula L)} {φ ψ : Formula L} {i : Idx} {n : Nat}
    (hg : ψ ∈ expand (henkinAdd p) ∅ n) (h0 : n = Encodable.encode (i, φ)) :
    ∃ m : Nat, ∃ j : Idx, m < n ∧ m = Encodable.encode (j, ψ):= by
  induction n with
  | zero => unfold expand at hg; sorry
  | succ n hn =>
    dsimp [expand, henkinAdd] at hg

    sorry
theorem henkinExpand_ord {Γ : Set (Formula L)} {φ ψ : Formula L} {i : Idx}
    (hg : ψ ∈ expand (henkinAdd p) ∅ (Encodable.encode (i, φ))) :
    ∃ j : Idx, Encodable.encode (j, ψ) < Encodable.encode (i, φ) := by
  induction hi : Encodable.encode (i, φ) /-generalizing i ψ φ-/ with
  | zero => sorry
  | succ n hn =>
    rw [hi] at hg
    dsimp [expand, henkinAdd] at hg
    match hj : Encodable.decode (α := Idx × Formula L) n with
    | none =>
      simp only [hj] at hg
      unfold expand at hg
      cases n with
      | zero => sorry
      | succ m => dsimp [henkinAdd] at hg; sorry
    | some (j, χ) =>

      sorry

theorem henkinExpand_vars {φ g : Formula L} {i : Idx}
    (hg : g ∈ expand (henkinAdd p) ∅ (Encodable.encode (i, φ)).succ) :
    (Formula.henkinTerm p i φ).vars ∩ g.vars = ∅ := by
  /-have h : Prod.snd <$> Encodable.decode (α := Idx × Formula L) ((Encodable.encode (i, φ)))
      = φ := by simp only [Encodable.encode_prod_val', Encodable.encode_nat,
    Encodable.decode_prod_val', Nat.unpair_pair', Encodable.decode_nat,
    Encodable.encodek, Option.map_some, Option.bind_some, Option.map_eq_map]-/
  cases hi : Encodable.encode (i, φ) with
  | zero =>
    simp only [expand, henkinAdd, Encodable.encodek, Set.mem_insert_iff] at hg
    rw [hi] at hg
    unfold expand at hg
    rcases hg with hg | hg
    · subst hg
      unfold Formula.henkinTerm
      sorry
    · sorry
  | succ n =>
    simp only [expand, henkinAdd, Encodable.encodek, Set.mem_insert_iff] at hg

    sorry

private abbrev henkinExpand := completeExpand (henkinAdd p (L := L) ·)

set_option linter.unusedDecidableInType false in
theorem Henkinbaum [hd : DecidablePred (InCon (L := L))] : Con Γ -> Con (henkinExpand p Γ) := by
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
      simp only [henkinAdd, hn, insert, Proof.deduction] at h1
      unfold Formula.henkinfy Formula.henkin at h1
      have h3 := Proof.mp (Proof.neg_of_impl_left _ _) h1
      have h4 := Proof.mp (Proof.neg_of_impl_right _ _) h1
      replace h4 := Proof.mp (FOL.AX _ (.h3 _)) h4
      unfold Formula.henkinTerm newTerm at h4
      apply h2 n <| Nat.lt_succ_self n
      apply Proof.mp h3
      refine Proof.mp (Proof.monotone (Set.empty_union _ ▸ Set.subset_union_right)
        (Proof.all_impl_subst i _ ?_)) <| Proof.gen_rule _ _ _ ?_ h4
      · intro h5
        have h6 := Formula.henkinTerm_vars p i φ
        unfold Formula.henkinTerm newTerm Term.vars at h6
        rw [Set.singleton_inter_eq_empty] at h6
        exact h6 h5
      · intro ψ h5 h6
        sorry

end Henkin
end PrimaryLogic
