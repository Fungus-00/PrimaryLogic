import PrimaryLogic.Tool
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Finset.Union

namespace PrimaryLogic
variable {LF LP : Type}

section language

structure Lang (LF LP : Type) where
  funcs : LF -> Nat
  preds : LP -> Nat

end language

variable {L : Lang LF LP}

-- `args` in `Term.app` was typed by `Vector (Term L) L.funcs[n]` at first,
-- but Lean4 does not support recusive type parameter.
-- And `args` in `Formula.atom` continue this type design for unified pattern.
inductive Term (L : Lang LF LP) : Type
  | var (i : Idx)
  | app (n : LF) (args : Fin (L.funcs n) -> Term L)

inductive Formula (L : Lang LF LP) : Type
  | atom (n : LP) (args : Fin (L.preds n) -> Term L)
  | falsum
  | impl : Formula L -> Formula L -> Formula L
  | fall : Idx -> Formula L -> Formula L

instance : Inhabited (Term L) := ⟨.var 0⟩
instance : Inhabited (Formula L) := ⟨.falsum⟩

def Term.isConst : Term L -> Prop
  | var _ => False
  | app n _ => L.funcs n = 0

def Const (L : Lang LF LP) := { t : Term L // t.isConst }
def Term.mkConst (n : LF) (h : L.funcs n = 0) : Term L :=
  .app n <| cast (congrArg (Fin · -> Term L) h.symm) Fin.elim0

section eq
variable [DecidableEq LF]

def Term.beq : Term L → Term L → Bool
  | .var i, .var j => i == j
  | .app i ai, .app j aj =>
    if hi : i = j then by
      subst hi
      exact forallInFin (n :=  L.funcs i)
        fun k => Term.beq (ai k) (aj k)
    else false
  | _, _ => false

theorem Term.beq_iff_eq (t s : Term L) : Term.beq t s = true ↔ t = s := by
  induction t generalizing s with
  | var => cases s <;> simp [Term.beq]
  | app i ai ht => cases s with
    | var => simp [Term.beq]
    | app j aj =>
      unfold Term.beq
      split_ifs with hi
      · subst hi
        simp only [Term.app.injEq, heq_eq_eq, true_and]
        rw [forallInFin_eq (L.funcs i)]
        have (k : Fin (L.funcs i)) := ht k (aj k)
        constructor
        · intro h
          funext k
          exact (this k).mp (h k)
        · intro h k
          exact (this k).mpr (congrFun h k)
      · simp [hi]

instance : BEq (Term L) := ⟨Term.beq⟩

instance Term.decidableEq : DecidableEq (Term L) := by
  intro t s
  by_cases h : Term.beq t s
  · exact isTrue ((Term.beq_iff_eq t s).mp h)
  · exact isFalse (by intro h_eq; rw [←Term.beq_iff_eq t s] at h_eq; contradiction)

variable [DecidableEq LP]
def Formula.beq : Formula L → Formula L → Bool
  | .atom i ai, .atom j aj =>
    if h : i = j then by
      subst h
      exact forallInFin (L.preds i)
        fun k => Term.beq (ai k) (aj k)
      else false
  | .falsum, .falsum => true
  | .impl φ ψ, .impl φ' ψ' => φ.beq φ' && ψ.beq ψ'
  | .fall i φ, .fall j ψ => i == j && φ.beq ψ
  | _, _ => false

theorem Formula.beq_iff_eq (φ ψ : Formula L) : Formula.beq φ ψ = true ↔ φ = ψ := by
  induction φ generalizing ψ with
  | atom i ai => cases ψ with
    | atom j aj =>
      unfold Formula.beq
      split_ifs with hi
      · subst hi
        simp only [atom.injEq, true_and, heq_eq_eq]
        rw [forallInFin_eq (L.preds i)]
        constructor
        · intro h; funext k
          rw [←Term.beq_iff_eq (ai k) (aj k)]
          exact h k
        · intro h_eq k
          rw [Term.beq_iff_eq (ai k) (aj k), h_eq]
      · simp [hi]
    | _ => simp [Formula.beq]
  | falsum => cases ψ <;> simp [Formula.beq]
  | impl a b ha hb => cases ψ with
    | impl c d => simp [ha c, hb d, Formula.beq]
    | _ => simp [Formula.beq]
  | fall i a hi => cases ψ with
    | fall j b => simp [hi b, Formula.beq]
    | _ => simp [Formula.beq]

instance : BEq (Formula L) := ⟨Formula.beq⟩

instance Formula.decidableEq : DecidableEq (Formula L) := by
  intro t s
  by_cases h : Formula.beq t s
  · exact isTrue ((Formula.beq_iff_eq t s).mp h)
  · exact isFalse (by intro h_eq; rw [←Formula.beq_iff_eq t s] at h_eq; contradiction)

end eq

section subst

namespace Term
def vars : Term L -> Set Idx
  | var i => {i}
  | app _ s => Set.iUnion fun k => (s k).vars

def varList : Term L -> List Idx
  | var i => [i]
  | app n s => (List.finRange (L.funcs n)).flatMap fun k => (s k).varList

def funs : Term L -> Set LF
  | var _ => ∅
  | app f s => insert f <| ⋃ k, funs (s k)

def subst (i : Idx) (t : Term L) : Term L -> Term L
  | var j => if i = j then t else .var j
  | app n args => .app n fun k => t.subst i (args k)

def substFun [DecidableEq LF] (t : Term L) (f : LF) : Term L -> Term L
  | x@(.var _) => x
  | .app n s => if n = f then t else .app n fun k => substFun t f (s k)

end Term

namespace Formula
def vars : Formula L -> Set Idx
  | atom _ s => ⋃ k, (s k).vars
  | falsum => ∅
  | impl φ ψ => φ.vars ∪ ψ.vars
  | fall i φ => insert i φ.vars

def fvar : Formula L -> Set Idx
  | atom _ s => ⋃ k, (s k).vars
  | falsum => ∅
  | impl φ ψ => φ.fvar ∪ ψ.fvar
  | fall i φ => φ.fvar \ {i}

def bvar : Formula L -> Set Idx
  | atom .. | falsum => ∅
  | impl φ ψ => φ.bvar ∪ ψ.bvar
  | fall i φ => insert i φ.bvar

def funs [DecidableEq LF] : Formula L -> Set LF
  | atom _ s => ⋃ k, Term.funs (s k)
  | falsum => ∅
  | impl φ ψ => funs φ ∪ funs ψ
  | fall _ φ => funs φ

def varList : Formula L -> List Idx
  | atom n s => (List.finRange (L.preds n)).flatMap fun k => (s k).varList
  | falsum => []
  | impl φ ψ => φ.varList ++ ψ.varList
  | fall i φ => i :: φ.varList

def fvarList : Formula L -> List Idx
  | atom n s => (List.finRange (L.preds n)).flatMap fun k => (s k).varList
  | falsum => []
  | impl φ ψ => φ.fvarList ++ ψ.fvarList
  | fall i φ => φ.fvarList.removeAll [i]

def bvarList : Formula L -> List Idx
  | atom .. | falsum => []
  | impl φ ψ => φ.bvarList ++ ψ.bvarList
  | fall i φ => i :: φ.bvarList

def FreeFor (i : Idx) (t : Term L) : Formula L -> Prop
  | atom .. | falsum => True
  | impl φ ψ => φ.FreeFor i t ∧ ψ.FreeFor i t
  | fall j φ => i = j ∨ i ∉ φ.fvar ∨ j ∉ t.vars ∧ φ.FreeFor i t

theorem out_var_FreeFor_term {i : Idx} (t : Term L) {φ : Formula L} :
    i ∉ φ.fvar -> φ.FreeFor i t := by
  intro h
  induction φ with
  | atom | falsum => unfold FreeFor; exact .intro
  | impl ψ χ ha hb =>
    simp [fvar] at h
    unfold FreeFor
    exact ⟨ha h.left, hb h.right⟩
  | fall j ψ _ =>
    simp only [fvar, Set.mem_diff, Set.mem_singleton_iff, not_and, Decidable.not_not] at h
    unfold FreeFor
    by_cases h' : i = j
    · left; exact h'
    · right; left; exact fun h0 => h' (h h0)

def subst (i : Idx) (t : Term L) (φ : Formula L) (h : φ.FreeFor i t) : Formula L :=
  match φ with
  | atom n args => atom n (fun k => Term.subst i t (args k))
  | falsum => falsum
  | impl ψ χ => impl (ψ.subst i t h.left) (χ.subst i t h.right)
  | fall j ψ => if hi : i = j then fall j ψ else
    have h' : ψ.FreeFor i t := by
      unfold FreeFor at h
      rcases h with h1 | h2 | h3
      · exfalso; exact hi h1
      · exact out_var_FreeFor_term t h2
      · exact h3.right
    fall j (ψ.subst i t h')

def substFun [DecidableEq LF] (t : Term L) (f : LF) : Formula L -> Formula L
  | atom p s => .atom p fun k => Term.substFun t f (s k)
  | falsum => .falsum
  | impl φ ψ => .impl (φ.substFun t f) (ψ.substFun t f)
  | fall i φ => .fall i (φ.substFun t f)

end Formula
end subst

def Sentence (L : Lang LF LP) := { φ : Formula L // φ.fvar = ∅ }
instance : Coe (Sentence L) (Formula L) := ⟨fun x => x.val⟩

section depth

def Formula.depth : Formula L -> Nat
  | atom .. | falsum => 0
  | impl φ ψ => max (φ.depth) (ψ.depth) + 1
  | fall _ φ => φ.depth + 1

theorem Formula.subst_depth_eq (i : Idx) (t : Term L) (φ : Formula L)
    (h : FreeFor i t φ) : (φ.subst i t h).depth = φ.depth := by
  induction φ with
  | atom | falsum => unfold subst depth; rfl
  | impl x y hx hy =>
    dsimp [subst, depth]
    unfold FreeFor at h
    rw [Nat.add_right_cancel_iff]
    exact congr_arg₂ _ (hx h.left) (hy h.right)
  | fall j ψ h' =>
    dsimp [subst, depth]
    unfold FreeFor at h
    split_ifs with hi
    · conv => lhs; unfold depth
    · conv => lhs; unfold depth
      rw [Nat.add_right_cancel_iff]
      rcases h with h1 | h2 | h3
      · exfalso; exact hi h1
      · exact h' <| out_var_FreeFor_term t h2
      · exact h' h3.right

theorem Formula.substFun_depth_eq [DecidableEq LF] (f : LF) (t : Term L) (φ : Formula L) :
    φ.depth = (φ.substFun t f).depth := by
  induction φ <;> unfold substFun depth <;> omega

end depth

section Mor
structure VarContext (L : Lang LF LP) (p : Idx → Prop) where
  i : Idx := 0
  t : Term L := .var i
  φ : Formula L := .falsum
  ψ : Formula L := .falsum
  hi : p i
  ht : t.vars ⊆ p
  hx : φ.vars ⊆ p
  hy : ψ.vars ⊆ p

structure Mor (L : Lang LF LP) where
  d : Idx
  p : Idx -> Prop
  ι : Idx -> Idx
  τ : Term L -> Term L
  f : Formula L -> Formula L
  pd : p d
  inj_ι : PartInj p ι

open Formula Set in
structure MorAx (m : Mor L) (c : VarContext L m.p) : Prop where
  map_τvars : (m.τ c.t).vars = m.ι '' c.t.vars
  map_fvars : (m.f c.φ).vars = m.ι '' c.φ.vars
  map_falsum : m.f falsum = falsum
  map_impl : m.f (impl c.φ c.ψ) = impl (m.f c.φ) (m.f c.ψ)
  map_fall : m.f (fall c.i c.φ) = fall (m.ι c.i) (m.f c.φ)
  free_var : c.i ∉ c.φ.fvar → (m.ι c.i) ∉ (m.f c.φ).fvar
  free_for : FreeFor c.i c.t c.φ → FreeFor (m.ι c.i) (m.τ c.t) (m.f c.φ)
  map_subst (h) :
    m.f (subst c.i c.t c.φ h) = subst (m.ι c.i) (m.τ c.t) (m.f c.φ) (free_for h)
end Mor
end PrimaryLogic
