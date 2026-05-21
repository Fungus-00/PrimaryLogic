import PrimaryLogic.FirstOrder.Axiom

namespace PrimaryLogic
variable {LF LP : Type} (L : Lang LF LP)

class HasEq (L : Lang LF LP) : Type where
  eq_i : LP
  pred_is_eq : L.preds eq_i = 2
  eq_args (t s : Term L) : Fin 2 → Term L :=
    fun | ⟨0, _⟩ => t | ⟨1, _⟩ => s
  eq_pred (t s : Term L) : Formula L := .atom eq_i
    fun k => eq_args t s <| cast (by rw [pred_is_eq]) k

variable (L : Lang LF LP) [HasEq L]

inductive EqAxioms : Type
  | rfl : Term L -> EqAxioms
  | sub (i : Idx) (t : Term L) (φ : Formula L) : φ.FreeFor i t -> EqAxioms

instance : AxiomSchema L (EqAxioms L) where toFormula := fun
  | .rfl t => HasEq.eq_pred t t
  | .sub i t φ h => .impl (HasEq.eq_pred (.var i) t)
    (.impl φ (φ.safeSub i t h))

inductive HilbertAxioms : Type
  | fol : FOLAxioms L -> HilbertAxioms
  | eq : EqAxioms L -> HilbertAxioms

instance : AxiomSchema L (HilbertAxioms L) where toFormula := fun
  | .fol a | .eq a => AxiomSchema.toFormula (L := L) a

end PrimaryLogic
