import PrimaryLogic.Formula

namespace PrimaryLogic

variable {LF F1 F2 F3 LP P1 P2 P3 : Type} {L1 : Lang F1 P1} {L2 : Lang F2 P2} {L3 : Lang F3 P3}

namespace Lang
structure Hom (L1 : Lang F1 P1) (L2 : Lang F2 P2) where
  funcMap : F1 -> F2
  predMap : P1 -> P2
  func_arity' : L1.funcs = L2.funcs ∘ funcMap
  pred_arity' : L1.preds = L2.preds ∘ predMap

structure Embedding (L1 : Lang F1 P1) (L2 : Lang F2 P2) extends Hom L1 L2 where
  func_inj' : Function.Injective funcMap
  pred_inj' : Function.Injective predMap

def expandConst (C : Type) (L : Lang LF LP) : Lang (LF ⊕ C) LP where
  funcs := Sum.elim L.funcs (Function.const C 0)
  preds := L.preds

instance (C : Type) (L : Lang LF LP) : Embedding L (expandConst C L) where
  funcMap := .inl
  predMap := id
  func_arity' := rfl
  pred_arity' := rfl
  func_inj' := Function.Embedding.inl.inj'
  pred_inj' := (Function.Embedding.refl LP).inj'

def expandCountable (L : Lang LF LP) : Lang (LF ⊕ Bool) LP where
  funcs := Sum.elim L.funcs Bool.toNat
  preds := L.preds

def Hom.id (L : Lang LF LP) : Lang.Hom L L :=
  ⟨_root_.id, _root_.id, rfl, rfl⟩

def Hom.comp {L1 : Lang F1 P1} {L2 : Lang F2 P2} {L3 : Lang F3 P3}
    (g : Hom L2 L3) (f : Hom L1 L2) : Hom L1 L3 where
  funcMap := g.funcMap ∘ f.funcMap
  predMap := g.predMap ∘ f.predMap
  func_arity' := by rw [f.func_arity', g.func_arity', Function.comp_assoc]
  pred_arity' := by rw [f.pred_arity', g.pred_arity', Function.comp_assoc]

end Lang

structure LangType : Type 1 where
  {LF : Type}
  {LP : Type}
  L : Lang LF LP

@[reducible]
def LangCat : CategoryTheory.Category LangType where
  Hom X Y := Lang.Hom X.L Y.L
  id X := Lang.Hom.id X.L
  comp f g := g.comp f

def Term.homLang (f : Lang.Hom L1 L2) : Term L1 -> Term L2
  | .var i => .var i
  | .app n ts => .app (f.funcMap n) fun i => homLang f <| ts <|
    cast (congrArg Fin (f.func_arity' ▸ rfl)) i

namespace Formula
def homLang (f : Lang.Hom L1 L2) : Formula L1 -> Formula L2
  | .atom n ts => .atom (f.predMap n) fun i => Term.homLang f <| ts <|
    cast (congrArg Fin (f.pred_arity' ▸ rfl)) i
  | .falsum => .falsum
  | .impl φ ψ => .impl (homLang f φ) (homLang f ψ)
  | .fall i φ => .fall i (homLang f φ)

structure Hom (L1 : Lang F1 P1) (L2 : Lang F2 P2) where
  toFun : Formula L1 -> Option (Formula L2)
  map_falsum' : toFun falsum = some falsum
  map_impl' : ∀ φ ψ, toFun (impl φ ψ) = match toFun φ, toFun ψ with
    | some φ', some ψ' => some (impl φ' ψ') | _, _ => none

def Hom.ofLang (f : Lang.Hom L1 L2) : Hom L1 L2 :=
  ⟨fun φ => some (homLang f φ), by dsimp [homLang], by simp [homLang]⟩

def Hom.id (L : Lang LF LP) : Hom L L := ⟨(some ·), by dsimp, by simp⟩

def Hom.comp (g : Hom L2 L3) (f : Hom L1 L2) : Hom L1 L3 where
  toFun X := (f.toFun X).bind g.toFun
  map_falsum' := by rw [f.map_falsum', Option.bind, g.map_falsum']
  map_impl' φ ψ := by
    rw [f.map_impl']
    match f.toFun φ, f.toFun ψ with
      | some φ', some ψ' => dsimp; rw [g.map_impl']
      | _, none | none, _ => simp

end Formula

open Formula in
@[reducible]
def FormulaCat : CategoryTheory.Category LangType where
  Hom X Y := Formula.Hom X.L Y.L
  id X := Formula.Hom.id X.L
  comp f g := g.comp f
  id_comp := by intros; dsimp only [Hom.id, Hom.comp, Option.bind_some]
  comp_id := by intros; simp only [Hom.id, Hom.comp, Option.bind_fun_some]
  assoc := by intros; simp only [Hom.comp, Option.bind_assoc]

variable {L : Lang LF LP}
lemma Term.homLang_id_eq : Term.homLang (Lang.Hom.id L) = _root_.id := by
  funext t
  induction t with
  | var i => eq_refl
  | app n s h =>
    simp only [homLang, id]
    congr; funext i; exact h i

lemma Formula.homLang_id_eq : Formula.homLang (Lang.Hom.id L) = _root_.id := by
  funext φ
  rw [id]
  induction φ with
  | atom n s =>
    simp only [homLang, atom.injEq]
    constructor
    · dsimp [Lang.Hom.id]
    · rw [Term.homLang_id_eq]
      conv => left; intro i; rw [id]
      apply heq_of_eq
      funext; congr
  | falsum => eq_refl
  | impl x y hx hy => simp only [homLang, impl.injEq]; exact ⟨hx, hy⟩
  | fall i x h => simp only [homLang, h]

theorem Formula.Hom.ofLang_id_eq : Hom.ofLang (Lang.Hom.id L) = Formula.Hom.id L := by
  simp [Hom.ofLang, Formula.Hom.id, Formula.homLang_id_eq]

lemma Term.homLang_comp_eq {f : Lang.Hom L1 L2} {g : Lang.Hom L2 L3} :
    homLang (g.comp f) = (homLang g) ∘ (homLang f) := by
  funext t
  induction t with
  | var i => dsimp [homLang]
  | app n s h =>
    simp only [homLang, Function.comp_apply, cast_cast]
    congr; funext i; apply h

lemma Formula.homLang_comp_eq {f : Lang.Hom L1 L2} {g : Lang.Hom L2 L3} :
    homLang (g.comp f) = (homLang g) ∘ (homLang f) := by
  funext φ
  induction φ with
  | atom n s =>
    simp only [homLang, Function.comp_apply, cast_cast]
    congr; funext i; rw [Term.homLang_comp_eq]; eq_refl
  | falsum => eq_refl
  | impl x y hx hy => simp only [homLang, Function.comp_apply, impl.injEq]; exact ⟨hx, hy⟩
  | fall i x h => simp only [homLang, Function.comp_apply, h]

theorem Formula.Hom.ofLang_comp_eq {f : Lang.Hom L1 L2} {g : Lang.Hom L2 L3} :
    Hom.ofLang (g.comp f) = (Hom.ofLang g).comp (Hom.ofLang f) := by
  simp [Hom.ofLang, Hom.comp, Formula.homLang_comp_eq]

def LangFormulaFunctor := @CategoryTheory.Functor.mk LangType LangCat LangType FormulaCat id
  (Formula.Hom.ofLang ·)
  (by intros; dsimp only [LangCat, FormulaCat]; exact Formula.Hom.ofLang_id_eq)
  (by intros; dsimp only [LangCat, FormulaCat]; exact Formula.Hom.ofLang_comp_eq)

end PrimaryLogic
