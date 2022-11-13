section Chap5_3
variable (p q r : Prop)

syntax "triv_or_1" (colGt tactic) : tactic
macro_rules
  | `(tactic| triv_or_1 $p) => `(tactic| (first | apply Or.inl; $p | apply Or.inr; $p))
syntax "triv_or'" :tactic
macro_rules
  | `(tactic| triv_or') => `(tactic| triv_or_1 assumption)
syntax "triv_or" (colGt tactic) : tactic 
macro_rules
  | `(tactic| triv_or $p) => `(tactic| (first | triv_or_1 $p | apply Or.inl <;> triv_or $p | apply Or.inr <;> triv_or $p))

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro <;> (intro ⟨_, _⟩; trivial)
  
example : p ∨ q ↔ q ∨ p := by 
  apply Iff.intro <;> intro h <;> cases h <;> (rename_i hp <;> triv_or')

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  . intro ⟨⟨_, _⟩, _⟩; trivial
  . intro ⟨_, _, _⟩; trivial

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro <;> intro h <;> cases h <;> rename_i h' <;> 
  (first | triv_or (exact h') | cases h' <;> rename_i h'' <;> triv_or (exact h''))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro ⟨hp, hqr⟩
    cases hqr
    . apply Or.inl; trivial
    . apply Or.inr; trivial
  . intro h <;> cases h <;> rename_i h' <;> match h' with
    | ⟨_, _⟩ => constructor <;> (try assumption) <;> (try triv_or')
    
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  . intro h
    (cases h <;> rename_i h' <;> try cases h') <;> constructor <;> triv_or'
  . intro ⟨hpq, hpr⟩
    cases hpq 
    . triv_or'
    . cases hpr
      . triv_or'
      . apply Or.inr; trivial

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  . intro h
    intro ⟨hp, hq⟩
    exact h hp hq
  . intro h hp hq
    apply h; trivial

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by 
  apply Iff.intro
  . intro h
    constructor <;> intro <;> apply h <;> triv_or'
  . intro ⟨h1, h2⟩
    intro hpq
    cases hpq 
    . apply h1; assumption
    . apply h2; assumption
    
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  . intro h
    constructor <;> (intro hp; apply h; triv_or')
  . intro ⟨_, _⟩ hpq
    cases hpq <;> contradiction
    
example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h ⟨_, _⟩
  cases h <;> contradiction
  
example : ¬(p ∧ ¬p) := by
  intro ⟨_, _⟩
  contradiction

example : p ∧ ¬q → ¬(p → q) := by
  intro ⟨hp, _⟩ h
  let _ := h hp
  contradiction
  
example : ¬p → (p → q) := by
  intro _ _
  contradiction

example : (¬p ∨ q) → (p → q) := by
  intro h hp
  cases h; contradiction; assumption

example : p ∨ False ↔ p := by
  apply Iff.intro
  . intro h
    cases h; assumption; contradiction
  . intro; triv_or'

example : p ∧ False ↔ False := by
  apply Iff.intro
  . intro ⟨_, _⟩; assumption
  . intro; constructor; contradiction; assumption

example : (p → q) → (¬q → ¬p) := by
  intro h hnq hp
  let _ := h hp
  contradiction
end Chap5_3

section Chap5_3'
variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h
  by_cases hp : p
  . cases h hp
    . apply Or.inl; intro; assumption
    . apply Or.inr; intro; assumption
  . apply Or.inl; intro; contradiction
    
example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  by_cases hp : p
  . by_cases hq : q
    . let _ := And.intro hp hq; contradiction
    . triv_or'
  . triv_or'
  
example : ¬(p → q) → p ∧ ¬q := by
  intro h
  by_cases hp : p
  . by_cases hq : q
    . let _ := λ _: p => hq; contradiction
    . trivial
  . let _: (p → q) := λ _: p => by contradiction
    contradiction
  
example : (p → q) → (¬p ∨ q) := by
  intro h
  (by_cases p <;> try (rename_i hp; let _ := h hp)) <;> triv_or'

example : (¬q → ¬p) → (p → q) := by
  intro h hp
  by_cases q
  . assumption
  . rename_i hq; let _ := h hq; contradiction

example : p ∨ ¬p := by
  by_cases p <;> triv_or'

example : (((p → q) → p) → p) := by
  intros h
  by_cases p
  . trivial
  . let _ : p → q := λ p => by trivial 
    apply h
    trivial

end Chap5_3'

section Chap5_4_1
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  . intro h
    constructor <;> (intro h' ; let ⟨_, _⟩ := h h'; trivial)
  . intro h hw
    let _ := h.left hw
    let _ := h.right hw
    trivial
    
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h h' hw
  let _ := (h hw) (h' hw)
  trivial

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h hw
  cases h <;> (rename_i h'; let _ := h' hw; triv_or')
end Chap5_4_1

section Chap5_4_2
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by
  intro ha
  apply Iff.intro
  . intro h'
    exact h' ha
  . intros; trivial

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  apply Iff.intro
  . intro h
    by_cases hr : r
    . triv_or'
    . suffices ∀ (x : α), p x by triv_or'
      intro hw
      let _ := h hw
      by_cases h' : (p hw)
      . trivial 
      . let _ : ¬(p hw ∨ r) := λ h'' => h''.elim h' hr
        contradiction
  . intro h
    cases h with
    | inl h' => intro px; exact Or.inl (h' px)
    | inr _ => intro; triv_or'
    
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  apply Iff.intro
  . intro h hr hx
    exact h hx hr
  . intro h hx hr
    exact h hr hx
end Chap5_4_2

section Chap5_4_3
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  let h' := h barber
  let _ : ¬(shaves barber barber) := by
    intro h''
    let _ := h'.mp h''
    contradiction
  let _ : ¬¬(shaves barber barber) := by
    intro h''
    let _ := h'.mpr h''
    contradiction
  contradiction
end Chap5_4_3

section Chap5_4_4
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := by
  intro ⟨_, _⟩
  trivial

example (a : α) : r → (∃ x : α, r) := by
  intro hr
  exact ⟨a, hr⟩
  
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
  . intro ⟨px, h⟩
    constructor; exact ⟨px, h.left⟩; exact h.right
  . intro ⟨⟨w, hw⟩, hr⟩
    exact ⟨w, ⟨hw, hr⟩⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  apply Iff.intro
  . intro ⟨w, hw⟩
    cases hw with
    | inl hp => exact Or.inl (⟨w, hp⟩)
    | inr hq => exact Or.inr (⟨w, hq⟩)
  . intro h
    cases h <;> (rename_i h'; let ⟨w, _⟩ := h'; exists w; triv_or')

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by 
  apply Iff.intro
  . intro h ⟨w, h'⟩
    let _ := h w
    contradiction
  . intro h w
    by_cases pw: (p w) 
    . trivial
    . suffices ∃ x, ¬p x by contradiction
      exact ⟨w, pw⟩

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro ⟨w, pw⟩ h
    let _ := h w; contradiction
  . intro h
    by_cases hx : (∃ x, p x)
    . trivial
    . have _ : (∀ x, ¬ p x) := by 
           intro w pw; let _: (∃ x, p x):= ⟨w, pw⟩; contradiction
      contradiction

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro h w hp
    suffices ∃ x, p x by contradiction
    exact ⟨w, hp⟩
  . intro h ⟨w, hp⟩
    suffices ¬p w by contradiction
    exact h w
    
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  apply Iff.intro
  . intro h
    by_cases h' : ∃ x, ¬ p x
    . trivial
    . suffices ∀ x, p x by contradiction
      intro w
      by_cases h'' : p w
      . trivial 
      . suffices ∃ x, ¬p x by contradiction
        exact ⟨w, h''⟩
  . intro ⟨w, h⟩ h'
    suffices p w by contradiction
    exact h' w

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  apply Iff.intro
  . intro h ⟨w, hp⟩
    exact h w hp
  . intro h w hp
    apply h
    exact ⟨w, hp⟩
    
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  apply Iff.intro
  . intro ⟨w, h⟩ h'
    exact h (h' w)
  . intro h
    by_cases hp: p a
    . 
  
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry

end Chap5_4_4

section Chap5_2
example (p q r : Prop) (hp : p) 
  : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
    repeat (constructor; repeat (first | apply Or.inl; assumption | apply Or.inr | assumption))
end Chap5_2
