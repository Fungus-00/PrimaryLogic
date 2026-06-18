namespace AD
variable {α : Type u}

def get (f g : List α → α) : Nat → List α × List α
  | .zero => ([f []], [g []])
  | .succ n =>
    let s := get f g n
    (f s.2 :: s.1, g s.1 :: s.2)

theorem get_valid {f g : List α → α} (n : Nat) :
    (get f g n).1 ≠ [] ∧ (get f g n).2 ≠ [] := by
  induction n with
  | zero => simp only [get, ne_eq, List.cons_ne_self, not_false_eq_true, and_self]
  | succ n => simp only [get, ne_eq, reduceCtorEq, not_false_eq_true, and_self]

def play (f g : List α → α) (n : Nat) : α × α :=
  let s := get f g n
  (s.1.head (get_valid n).1, s.2.head (get_valid n).2)

def determine : Prop := ∀ p : (Nat → α × α) → Prop,
    (∀ g, ∃ f, p (play f g)) → (∃ f, ∀ g, p (play f g))

axiom determine_Bool : determine (α := Bool)
#print axioms determine_Bool
end AD
