import Mathlib.Tactic.Ring

/-! # Extensionality -/

variable (P Q : Prop)

example : (P ∧ P) = P := and_self P

example : (P ∨ P) = P := or_self P

#check propext

example : (P = Q) → (P ↔ Q) := Eq.to_iff

theorem proof1 : 1 + 1 + 1 + 1 + 1 = 5 := rfl

theorem proof2 : 1 + 1 + 1 + 1 + 1 = 5 := sorry

example : proof1 = proof2 := rfl

theorem proof3 (x : Nat) : x + 0 = x := rfl

theorem proof4 (x : Nat) : x + 0 = x := sorry

example : proof3 = proof4 := rfl

example (x : Nat) : proof3 x = proof4 x := rfl

def function1 (x : Int) : Int := 1

def function2 (x : Int) : Int := x + 1 - x

example : function1 = function2 := by
  funext x
  rw [function1, function2, add_sub_cancel_left]



#min_imports
