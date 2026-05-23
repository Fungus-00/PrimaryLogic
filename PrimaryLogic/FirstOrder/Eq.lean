import PrimaryLogic.FirstOrder.Axiom

namespace PrimaryLogic
variable {LF LP : Type} {L : Lang LF LP}

def BinPred (eq : Term L -> Term L -> Formula L) : Prop :=
  ∀ x y, (eq x y).fVars = x.vars ∪ y.vars

inductive EqAxioms (eq : Term L -> Term L -> Formula L) (h : BinPred eq) : Type
  | rfl (t : Term L)
  | sub (i : Idx) (t : Term L) (φ : Formula L) (h : φ.FreeFor i t)

variable {eq : Term L -> Term L -> Formula L} {h : BinPred eq}

instance : AxiomSchema L (EqAxioms eq h) where toFormula := fun
  | .rfl t => eq t t
  | .sub i t φ h => eq (.var i) t → φ → φ.subst i t h

inductive HilbertAxioms (eq : Term L -> Term L -> Formula L) (h : BinPred eq) : Type
  | fol : FOLAxioms L -> HilbertAxioms eq h
  | eq : EqAxioms eq h -> HilbertAxioms eq h

instance : AxiomSchema L (HilbertAxioms eq h) where toFormula := fun
  | .fol a | .eq a => AxiomSchema.toFormula (L := L) a

end PrimaryLogic
