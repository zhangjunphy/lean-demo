variable (p q r : Prop)

example : p ∧ q ↔ q ∧ p := 
  have reverse_and := fun {p q : Prop} (h : (p ∧ q)) => ⟨h.right, h.left⟩
  ⟨reverse_and, reverse_and⟩
example : p ∨ q ↔ q ∨ p := 
  have l2r := Or.
  
