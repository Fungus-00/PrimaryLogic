import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Find

namespace PrimaryLogic

section lem

theorem idn_iff_lem : (∀ p : Prop, ¬¬p → p) ↔ (∀ p : Prop, p ∨ ¬p) where
  mp hp p := hp (p ∨ ¬p) fun h => h <| .inr fun h' => h (.inl h')
  mpr h p hp := Or.rec id (fun h' => False.elim (hp h')) (h p)

axiom idn (p : Prop) : ¬¬p → p

lemma or_dec {p : Prop} (e : p ∨ ¬ p) : Nonempty (Decidable p) :=
  Or.elim e (.intro <| isTrue ·) (.intro <| isFalse ·)
end lem

section forall_in

def forallInRange (m n : Nat) (p : Nat → Bool) : Bool :=
  if h : m < n then
    p m && forallInRange (m + 1) n p
  else true
termination_by n - m

def forallInFin (n : Nat) (p : Fin n → Bool) (m : Nat := 0) : Bool :=
  if h : m < n then
    p ⟨m, h⟩ && forallInFin n p (m + 1)
  else true
termination_by n - m

lemma forall_range_eq_fin (m n : Nat) (p : Nat → Bool) (q : Fin n → Bool) :
    (∀ i : Nat, (h : i < n) → i ≥ m → p i = q ⟨i, h⟩) →
    forallInRange m n p = forallInFin n q m := by
  intro h
  induction h0 : n - m generalizing m with
  | zero =>
    unfold forallInRange forallInFin
    split_ifs
    · have := Nat.not_lt_of_ge (Nat.sub_eq_zero_iff_le.mp h0)
      contradiction
    · eq_refl
  | succ d hd =>
    unfold forallInRange forallInFin
    split_ifs with h1
    · have h2 (i : Nat) (hm : i ≥ m + 1) := Nat.le_trans (Nat.le_add_right m 1) hm
      rw [hd (m + 1) (fun i hi hm => h i hi (h2 i hm)) (by omega)]
      rw [h m h1 (Nat.le_refl m)]
    · eq_refl

theorem forallInRange_eq (i n : Nat) (p : Nat → Bool) :
    forallInRange i n p = true ↔ ∀ j : Nat, j < n → j ≥ i → p j := by
  constructor
  · intro h j hn hi
    revert h p
    induction h0 : n - i generalizing i with
    | zero =>
      have := Nat.not_lt_of_ge (Nat.sub_eq_zero_iff_le.mp h0)
      have := Nat.lt_of_le_of_lt (ge_iff_le.mp hi) hn
      contradiction
    | succ d hd =>
      intros p h
      by_cases h1 : j = i
      · rw [h1]
        have h2 : i < n := by omega
        unfold forallInRange at h
        split_ifs at h
        exact Bool.and_elim_left h
      · apply hd (i + 1) (by omega) (by omega) p
        unfold forallInRange at h
        split_ifs at h with h2
        · exact Bool.and_elim_right h
        · have : i < n := by omega
          contradiction
  · intro h
    induction h0 : n - i generalizing i with
    | zero =>
      unfold forallInRange
      split_ifs with h1
      · have := Nat.not_lt_of_ge (Nat.sub_eq_zero_iff_le.mp h0)
        contradiction
      · eq_refl
    | succ d hd =>
      have h1 : i < n := by omega
      unfold forallInRange
      split_ifs
      rw [Bool.and_eq_true_iff]
      constructor
      · exact h i h1 (Nat.le_refl i)
      · apply hd (i + 1)
        · intro j hj hi
          exact h j hj (by omega)
        · omega

theorem forallInFin_eq (n : Nat) (p : Fin n → Bool) :
    forallInFin n p = true ↔ ∀ i : Fin n, p i := by
  let s (i : Nat) := if h : i < n then p ⟨i, h⟩ else true
  have h1 := forallInRange_eq 0 n s
  have h2 : ∀ (i : ℕ) (h : i < n), i ≥ 0 → s i = p ⟨i, h⟩ := by
    intros; unfold s; split_ifs; eq_refl
  have h3 := forall_range_eq_fin 0 n s p h2
  rw [←h3, h1]
  constructor
  · intro h i
    have h4 := h i.val i.isLt (Nat.zero_le i)
    unfold s at h4
    split_ifs at h4 with h5
    · exact h4
    · exfalso; exact h5 i.isLt
  · intro h i h4 _
    unfold s
    split_ifs
    exact h ⟨i, h4⟩

end forall_in

abbrev Idx := Nat -- Planed to be replaced with type argument.

section assignment

abbrev Assignment (α : Type*) := Idx -> α

variable {α : Type u} (s : Assignment α)

abbrev replace (i : Idx) (a : α) :=
  fun k => if k = i then a else s k

lemma replace_absorb (i : Idx) : replace s i (s i) = s :=
  funext fun k => by unfold replace; split_ifs with h; try rw [h]; rfl

lemma replace_comm (i j : Idx) (h : i ≠ j) (a b : α) :
    replace (replace s i a) j b = replace (replace s j b) i a := by
  funext k; unfold replace
  split_ifs with h1 h2
  · rw [←h1, ←h2] at h; contradiction
  repeat rfl

lemma replace_idempotent (i : Idx) (a b : α) :
    replace (replace s i a) i b = replace s i b := by
  funext k; unfold replace; split_ifs with h1 <;> rfl

lemma replace_of_map (f : Idx -> Idx) (hf : Function.Injective f) (i : Idx) (a : α) :
    replace (s ∘ f) i a = replace s (f i) a ∘ f := by
  unfold replace; funext k; dsimp
  split_ifs with h1 h2
  · rfl
  · exfalso; exact h2 <| congrArg f h1
  · rename_i h2; exfalso; exact h1 (hf h2)
  · rfl

end assignment

section list_ceq
variable {α : Type*}

def _root_.List.ceq (s t : List α) : Prop := ∀ x : α, x ∈ s ↔ x ∈ t

instance : Equivalence (List.ceq (α := α)) where
  refl := fun _ _ => iff_of_eq rfl
  symm := fun x y => (x y).symm
  trans := fun x y z => (x z).trans (y z)

end list_ceq

section fix
open Std in
local instance Lx1 {α : Type*} [LE α] [DecidableLE α] [Max α]
    [LawfulOrderLeftLeaningMax α] : MaxEqOr α where
  max_eq_or a b := by
    suffices min_eq : max a b = if b ≤ a then a else b by
      rw [min_eq]
      split <;> simp
    split <;> simp [*, LawfulOrderLeftLeaningMax.max_eq_left,
      LawfulOrderLeftLeaningMax.max_eq_right]

open List in
theorem max?_eq_some_iff' {α a} [Max α] [LE α] [DecidableLE α] {xs : List α} [Std.IsLinearOrder (α)]
    [Std.LawfulOrderMax α] : xs.max? = some a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → b ≤ a := by
  constructor
  · intro h; exact ⟨max?_mem h, (max?_le_iff h).1 (Std.le_refl _)⟩
  · intro ⟨h₁, h₂⟩
    cases xs with
    | nil => simp at h₁
    | cons x xs =>
      rw [List.max?]
      exact congrArg some <| Std.le_antisymm
        (h₂ _ (max?_mem (xs := x :: xs) rfl))
        ((max?_le_iff (xs := x :: xs) rfl).1 (Std.le_refl _) _ h₁)

theorem eq_nil_iff_forall_not_mem' {α} {l : List α} : l = [] ↔ ∀ a, a ∉ l := by
  cases l <;> simp only [List.not_mem_nil, not_false_eq_true, implies_true, reduceCtorEq,
    List.mem_cons, forall_eq_or_imp, imp_false, false_and]

theorem add_eq_left' {a b : Nat} : a + b = a ↔ b = 0 := by
  constructor
  · intro h
    induction a with
    | zero => rwa [Nat.zero_add] at h
    | succ n ha =>
      conv at h =>
        lhs; rw [add_assoc]
        conv => rhs; rw [add_comm]
        rw [←add_assoc]
      exact ha (add_right_cancel h)
  · intro h; rw [h]; apply Nat.add_zero
end fix

section freshable
class Freshable (α : Type*) [DecidableEq α] where
  fresh : Finset α → α
  fresh_is_new : ∀ s : Finset α, fresh s ∉ s

/-- `fresh` algorithm was originally implemented by `Finset.max` function,
    without optimal utilization of space, then `Nat.find` was selected instead.
  Not sure the time efficiency of the latter though.
  Yet both the time and space optimal algorithm will be explored in another file. -/
instance : Freshable Idx where
  fresh := fun s => Nat.find (p := (· ∉ s)) (by
    cases h : s.max with
    | bot => simp [Finset.max_eq_bot.mp h]
    | coe m =>
      use m + 1
      exact Finset.notMem_of_max_lt (a := m+1) (b := m) (by simp) h
  )
  fresh_is_new s := Nat.find_spec (p := fun i => i ∉ s) _

class LFreshable (α : Type*) where
  fresh : List α → α
  fresh_is_new : ∀ s, fresh s ∉ s
  fresh_ceq_invariance : ∀ s t, s.ceq t → fresh s = fresh t

instance : LFreshable Nat where
  fresh s := match List.max? s with | none => 0 | some n => n.succ
  fresh_is_new s := by
    cases h : s with
    | nil => simp only [List.max?, List.not_mem_nil, not_false_eq_true]
    | cons a l =>
      simp only [Nat.succ_eq_add_one, List.mem_cons, not_or, List.max?]
      constructor
      · by_cases h': l = []
        · rw [h']; unfold List.foldl
          simp only [add_eq_left', one_ne_zero, not_false_eq_true]
        · rw [List.foldl_max_eq_max h']
          omega
      · by_cases h': l = []
        · rw [h']; unfold List.foldl; simp only [List.not_mem_nil, not_false_eq_true]
        · rw [List.foldl_max_eq_max h']
          by_contra
          have := (List.max_le_iff h').mp (Nat.le_refl _) _ this
          omega
  fresh_ceq_invariance s t h := by
    match hs : s.max?, ht : t.max? with
    | none, none => rfl
    | none, some n =>
      rw [List.max?_eq_none_iff, eq_nil_iff_forall_not_mem'] at hs
      rw [max?_eq_some_iff'] at ht
      have h' := (h n).mpr ht.1
      exfalso; exact hs n h'
    | some n, none =>
      rw [List.max?_eq_none_iff, eq_nil_iff_forall_not_mem'] at ht
      rw [max?_eq_some_iff'] at hs
      have h' := (h n).mp hs.1
      exfalso; exact ht n h'
    | some m, some n =>
      simp only [Nat.succ_eq_add_one, Nat.add_right_cancel_iff]
      rw [max?_eq_some_iff'] at hs ht
      have h1 := ht.2 m <| (h m).mp hs.1
      have h2 := hs.2 n <| (h n).mpr ht.1
      exact h1.antisymm h2
end freshable

section pfun
def PartialInj {α β : Type*} (p : α -> Prop) (f : α -> β) : Prop :=
  ∀ {x y : α}, p x -> p y -> f x = f y -> x = y

variable {α β : Type*} {p : α -> Prop} {f : α -> β}

namespace PartialInj
theorem ne (hf : PartialInj p f) {x y : α} : p x → p y → x ≠ y → f x ≠ f y :=
  fun hx hy => mt fun h => hf hx hy h

theorem mem_finset_image (hf : PartialInj p f) [DecidableEq β] {s : Finset α} {a : α}
    (hs : ∀ x ∈ s, p x) : p a → (f a ∈ s.image f ↔ a ∈ s) := fun h => by
  rw [Finset.mem_image]
  constructor
  · intro ⟨b, ⟨h1, h2⟩⟩
    have := hf (hs b h1) h h2
    rwa [this] at h1
  · intro ha; use a

theorem image_erase [DecidableEq α] [DecidableEq β] (hf : PartialInj p f) (s : Finset α) (a : α)
    (hs : ∀ x ∈ s, p x) (ha : p a) : (s.erase a).image f = (s.image f).erase (f a) := by
  rw [Finset.ext_iff]; intro b
  rw [Finset.mem_image, Finset.mem_erase]
  conv => lhs; arg 1; intro; rw [Finset.mem_erase]
  conv => rhs; arg 2; rw [Finset.mem_image]
  constructor
  · intro ⟨x, h1, h2⟩
    have h3 := ne hf ha (hs x h1.right) h1.left.symm
    rw [h2] at h3
    exact ⟨h3.symm, x, h1.right, h2⟩
  · intro ⟨h1, x, h2, h3⟩
    use x
    refine ⟨⟨?_, h2⟩, h3⟩
    by_contra
    rw [this] at h3
    exact h1 h3.symm

end PartialInj

end pfun

section List
variable {α : Type*} [DecidableEq α]

section first
def _root_.List.first (l : List α) (a : α) (h : a ∈ l) : Nat :=
  match l with
  | [] => False.elim (List.not_mem_nil h)
  | b :: s => if h' : a = b then 0 else
    (first s a (Or.resolve_left (by rwa [List.mem_cons] at h) h')).succ

open List in
lemma _root_.List.first_valid {l : List α} {a : α} (h : a ∈ l) : l.first a h < l.length := by
  induction l with
  | nil => exfalso; exact not_mem_nil h
  | cons b s h1 =>
    unfold first length
    split_ifs with h2
    · apply Nat.zero_lt_succ
    · rw [Nat.succ_eq_add_one, Nat.add_lt_add_iff_right]
      rw [mem_cons] at h
      exact h1 <| Or.resolve_left h h2

open List in
theorem _root_.List.first_get {α : Type*} [DecidableEq α] {l : List α} {a : α} (h : a ∈ l) :
    l[l.first a h]? = some a := by
  induction l with
  | nil => exfalso; exact not_mem_nil h
  | cons b s h1 =>
    unfold first
    split_ifs with h2
    · simp only [length_cons, Nat.zero_lt_succ, getElem?_pos, getElem_cons_zero, Option.some.injEq]
      symm; exact h2
    · simp only [Nat.succ_eq_add_one, getElem?_cons_succ]
      rw [mem_cons] at h
      exact h1 (Or.resolve_left h h2)
end first

section expand
variable {β : Type*} [LFreshable β]
private def expand (s : List α × List β) : List α → List α × List β
  | [] => s
  | a :: l =>
    let r := expand s l;
    if a ∈ r.1 then r
    else ⟨a :: r.1, (LFreshable.fresh r.2) :: r.2⟩

private lemma expand_len (s : List α × List β) (hs : s.1.length = s.2.length)
    (l : List α) : (expand s l).1.length = (expand s l).2.length := by
  induction l with
  | nil => unfold expand; exact hs
  | cons a r h =>
    dsimp [expand]
    split_ifs with h'
    · exact h
    · dsimp; rw [h]

private lemma expand_ex (s : List α × List β) {l : List α} {a : α} (h : a ∈ l) :
    a ∈ (expand s l).1 := by
  induction l with
  | nil => exfalso; exact List.not_mem_nil h
  | cons b r h1 =>
    dsimp [expand]
    rw [List.mem_cons] at h
    split_ifs with h2
    · rcases h with h3 | h4
      · subst h3; exact h2
      · exact h1 h4
    · dsimp; rw [List.mem_cons]
      rcases h with h3 | h4
      · left; exact h3
      · right
        exact h1 h4

private lemma expand_uni2 {s : List α × List β} {l : List α}
    (hs : ∀ {m n : Nat}, ∀ hm : m < s.2.length, ∀ hn : n < s.2.length,
      s.2[m]'hm = s.2[n]'hn → m = n) :
    let r := (expand s l).2; ∀ {m n : Nat}, ∀ hm : m < r.length, ∀ hn : n < r.length,
      r[m]'hm = r[n]'hn → m = n :=
  fun {m n} hm hn hr => by
  induction l generalizing m n with
  | nil => dsimp [expand] at hm hn hr; exact hs hm hn hr
  | cons d u h =>
    dsimp [expand] at hr
    split_ifs at hr with h1
    · have h2 : expand s (d :: u) = expand s u := by
        conv => lhs; unfold expand; simp [h1]
      rw [h2] at hm hn
      exact h hm hn hr
    · simp only [List.getElem_cons] at hr
      unfold expand at hm hn
      simp only [h1, ↓reduceIte, List.length_cons,
        Nat.lt_add_one_iff, Nat.le_iff_lt_or_eq] at hm hn
      split_ifs at hr with h2 h3
      · rw [h2, h3]
      · exfalso
        have h5 := Or.elim hn
          (Nat.sub_lt_of_lt ·) (fun h' => by rw [←h']; exact Nat.sub_one_lt h3)
        have h6 := hr.symm ▸ List.getElem_mem h5
        exact LFreshable.fresh_is_new _ h6
      · by_cases h4 : n = 0
        · simp only [h4, ↓reduceDIte] at hr
          exfalso
          have h5 := Or.elim hm
            (Nat.sub_lt_of_lt ·) (fun h' => by rw [←h']; exact Nat.sub_one_lt h2)
          have h6 := hr ▸ List.getElem_mem h5
          exact LFreshable.fresh_is_new _ h6
        · simp only [h4, ↓reduceDIte] at hr
          match hm, hn with
          | .inl hm, .inl hn =>
            have h5 := Nat.sub_lt_of_lt (b := 1) hm
            have h6 := Nat.sub_lt_of_lt (b := 1) hn
            have h7 := h h5 h6 hr
            omega
          | .inr hm, .inl hn =>
            exfalso
            have h5 := Nat.sub_one_lt h2
            conv at h5 => rhs; rw [hm]
            have h6 := Nat.sub_lt_of_lt (b := 1) hn
            have h7 := h h5 h6 hr
            rw [←hm] at hn
            omega
          | .inl hm, .inr hn =>
            exfalso
            have h5 := Nat.sub_one_lt h4
            conv at h5 => rhs; rw [hn]
            have h6 := Nat.sub_lt_of_lt (b := 1) hm
            have h7 := h h6 h5 hr
            rw [←hn] at hm
            omega
          | .inr hm, .inr hn => rw [hm, hn]
end expand

section pass
variable {p : α → Prop} [DecidablePred p]

private def prePass (p : α → Prop) [DecidablePred p] : List α → List (Subtype p)
  | [] => []
  | a :: l => if h : p a then ⟨a, h⟩ :: prePass p l else prePass p l

private def pass (p : α → Prop) [DecidablePred p] (l : List α) : List (Subtype p) :=
  (prePass p l).dedup

private lemma pass_uni (p : α → Prop) [DecidablePred p] {l : List α} :
    let s := pass p l; ∀ {m n : Nat}, ∀ hm : m < s.length, ∀ hn : n < s.length,
    s[m]'hm = s[n]'hn → m = n := fun _ _ h =>
  Fin.val_inj.mpr <| (List.Nodup.get_inj_iff <| List.nodup_dedup <| prePass p l).mp h

def _root_.List.rejoin (p : α → Prop) [DecidablePred p] [LFreshable (Subtype p)]
    (l : List α) (a : α) : Subtype p :=
  if h : a ∈ l then
    let s := expand (⟨(pass p l).unattach, (pass p l)⟩) l
    have h1 : a ∈ s.1 := by dsimp [s]; exact expand_ex _ h
    have h2 : s.1.first a h1 < s.2.length := by
      dsimp [s]
      rw [←expand_len]
      · apply List.first_valid
      · dsimp; exact List.length_unattach
    s.2[s.1.first a h1]'h2
  else LFreshable.fresh []

variable {p : α → Prop} [DecidablePred p] [LFreshable (Subtype p)]

theorem _root_.List.rejoin_PartialInj (l : List α) :
    PartialInj (· ∈ l) (List.rejoin p l) := fun {x y} hx hy h => by
  dsimp at hx hy
  simp only [List.rejoin, hx, ↓reduceDIte, hy] at h
  have h1 := expand_uni2 (s := ((pass p l).unattach, pass p l))
    (fun {m n} hm hn h' => by dsimp at hm hn h'; exact pass_uni p hm hn h')
    (by rw [←expand_len _ (List.length_unattach)]; apply List.first_valid)
    (by rw [←expand_len _ (List.length_unattach)]; apply List.first_valid)
    h
  have h2 := congrArg (fun n => (expand ((pass p l).unattach, pass p l) l).1[n]?) h1
  dsimp at h2
  rwa [List.first_get (a := x), List.first_get (a := y), Option.some_inj] at h2

theorem _root_.List.rejoin_invariance (l : List α) (a : α) (hl : a ∈ l) (hp : p a) :
    l.rejoin p a = ⟨a, hp⟩ := by
  simp only [List.rejoin, hl, ↓reduceDIte]

  sorry
end pass
end List
end PrimaryLogic
