import PrimaryLogic.Formula
import Mathlib.Computability.Encoding
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Encodable.Pi

namespace PrimaryLogic
/- I referred to the code of `Mathlib.ModelTheory.Encoding`.
  The encoding is mainly used for enumeration. -/
variable {LF LP : Type} {L : Lang LF LP}

def Term.listEncode : Term L -> List (Idx ⊕ LF)
  | var i => [.inl i]
  | app f s => .inr f :: (List.finRange (L.funcs f)).flatMap fun i => (s i).listEncode

def Term.listDecode : List (Idx ⊕ LF) -> List (Term L)
  | [] => []
  | .inl i :: l => var i :: listDecode l
  | .inr f :: l =>
    letI s := listDecode l
    letI n := L.funcs f
    if h : n ≤ s.length then
      app f (fun i => s[i]) :: s.drop n
    else []

open List in
theorem Term.listDecode_encode_list (l : List (Term L)) :
    listDecode (l.flatMap listEncode) = l := by
  suffices h : ∀ (t : Term L) (l : List (Idx ⊕ LF)),
      listDecode (t.listEncode ++ l) = t :: listDecode l by
    induction l with
    | nil => eq_refl
    | cons t l lih => rw [flatMap_cons, h t (l.flatMap listEncode), lih]
  intro t l
  induction t generalizing l with
  | var => rw [listEncode, singleton_append, listDecode]
  | app f ts ih =>
    simp only [listEncode, listDecode, cons_append, Fin.getElem_fin]
    let n := L.funcs f
    have h : listDecode (((finRange n).flatMap fun i : Fin n => (ts i).listEncode) ++ l) =
        (finRange n).map ts ++ listDecode l := by
      induction finRange n with
      | nil => eq_refl
      | cons i l' l'ih => rw [flatMap_cons, append_assoc, ih, map_cons, l'ih, cons_append]
    conv =>
      lhs; lhs; ext
      conv => lhs; rhs; ext; arg 1; rw [h]
      conv => rhs; rw [h]
    split_ifs with hi
    · rw [h] at hi
      rw [length_append, length_map, length_finRange] at hi
      rw [cons.injEq, app.injEq, heq_eq_eq]
      refine ⟨⟨rfl, ?_⟩, ?_⟩
      · funext k
        rw [getElem_append_left, getElem_map, getElem_finRange, Fin.cast_mk, Fin.eta]
        rw [length_map, length_finRange]
        exact Fin.is_lt k
      · rw [drop_left']; rw [length_map, length_finRange]
    · rw [h] at hi
      rw [length_append, length_map, length_finRange] at hi
      unfold n at hi
      rw [Nat.not_le] at hi
      omega

protected def Term.encoding : Computability.Encoding (Term L) where
  Γ := Idx ⊕ LF
  encode := listEncode
  decode l := (listDecode l).head?
  decode_encode t := by
    have h := listDecode_encode_list [t]
    rw [List.flatMap_singleton] at h
    simp only [h, List.head?_cons]

instance [Encodable LF] : Encodable (Term L) :=
  Encodable.ofLeftInjection Term.listEncode (fun l => (Term.listDecode l).head?) fun t => by
    simp only
    rw [←List.flatMap_singleton Term.listEncode, Term.listDecode_encode_list]
    simp only [List.head?_cons]

abbrev PredArgs (L : Lang LF LP) := Σ p : LP, Fin (L.preds p) -> Term L
instance [Encodable LP] [Encodable LF] : Encodable (PredArgs L) := by infer_instance

def Formula.listEncode : Formula L -> List (PredArgs L ⊕ Bool ⊕ Idx)
  | atom p s => [.inl (⟨p, (s ·)⟩)]
  | falsum => [.inr (.inl false)]
  | impl φ ψ => .inr (.inl true) :: (φ.listEncode ++ ψ.listEncode)
  | fall i φ => .inr (.inr i) :: φ.listEncode

def Formula.listDecode : List (PredArgs L ⊕ Bool ⊕ Idx) -> List (Formula L)
  | .inl ⟨p, s⟩ :: l => atom p s :: listDecode l
  | .inr (.inl false) :: l => falsum :: listDecode l
  | .inr (.inl true) :: l =>
    letI s := listDecode l
    if h : s.length ≥ 2 then
      impl s[0] s[1] :: s.drop 2
    else []
  | .inr (.inr i) :: l =>
    match listDecode l with
    | [] => []
    | φ :: v => fall i φ :: v
  | _ => []

theorem Formula.listDecode_encode_list (l : List (Formula L)) :
    listDecode (l.flatMap listEncode) = l := by
  open List in
  suffices h : ∀ (φ : Formula L) (l : List (PredArgs L ⊕ Bool ⊕ Idx)),
      listDecode (φ.listEncode ++ l) = φ :: listDecode l by
    induction l with
    | nil => eq_refl
    | cons t l lih => rw [flatMap_cons, h t (l.flatMap listEncode), lih]
  intro φ l
  induction φ generalizing l with
  | atom n s | falsum => rw [listEncode, singleton_append, listDecode]
  | impl x y hx hy =>
    rw [listEncode, cons_append, listDecode]
    split_ifs with h'
    · simp [append_assoc, hx _ ,hy _, List.drop]
    · rw [append_assoc, hx _, hy _, length_cons, length_cons] at h'
      simp only [Nat.le_add_left, ge_iff_le] at h'
      contradiction
  | fall i x h =>
    rw [listEncode, cons_append, listDecode]
    cases h' : listDecode (x.listEncode ++ l) with
    | nil => simp [h l] at h'
    | cons y v =>
      simp only [cons.injEq, eq_self, fall.injEq, true_and];
      rw [h l, cons.injEq] at h'
      exact ⟨h'.left.symm, h'.right.symm⟩

protected def Formula.encoding : Computability.Encoding (Formula L) where
  Γ := PredArgs L ⊕ Bool ⊕ Idx
  encode := listEncode
  decode l := (listDecode l).head?
  decode_encode t := by
    have h := listDecode_encode_list [t]
    rw [List.flatMap_singleton] at h
    simp only [h, List.head?_cons]

instance [Encodable LF] [Encodable LP] : Encodable (Formula L) :=
  Encodable.ofLeftInjection Formula.listEncode (fun l => (Formula.listDecode l).head?) fun t => by
    dsimp only
    rw [←List.flatMap_singleton Formula.listEncode, Formula.listDecode_encode_list]
    simp only [List.head?_cons]
end PrimaryLogic
