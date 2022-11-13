section Chap4_1
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
  ⟨λ hpq => ⟨λ w => (hpq w).left, λ w => (hpq w).right⟩, 
   λ hphq => λ w => ⟨hphq.left w, hphq.right w⟩⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := λ hpq => λ hp => λ w => (hpq w) (hp w)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
  fun h => Or.elim h
    (λ hpx => λ w => Or.inl (hpx w))
    (λ hqx => λ w => Or.inr (hqx w))
end Chap4_1

section Chap4_2
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α -> ((∃ _ : α, r) ↔ r) := 
  λ w => Iff.intro
    (λ ⟨_, hr⟩ => hr)
    (λ hr => ⟨w, hr⟩)
    
open Classical 
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := 
  Iff.intro 
    (λ hpxor => byCases
      (λ h' : ∀ x, p x => Or.inl h') 
      (λ h' : ¬ ∀ x, p x => 
        have ⟨w, hnpw⟩ : ∃ x, ¬ p x := byContradiction 
          λ hnpx =>
            have : ∀ x, p x := λ w => byContradiction λ hnpw => hnpx ⟨w, hnpw⟩
            h' this
        have hr : r := byContradiction λ hnr => 
          have : p w := False.elim ((hpxor w).elim hnpw hnr)
          hnpw this
        Or.inr hr))
    (λ hpxor => λ w => 
      hpxor.elim 
        (λ hpx => Or.inl (hpx w)) 
        (λ hr => Or.inr hr))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (λ hxrpx => λ hr => λ w => hxrpx w hr)
    (λ hrxpx => λ w => λ hr => hrxpx hr w)
end Chap4_2

section Chap4_3
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

-- Who would shave the barber?
-- Why ↔ instead of ∧?
example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have : ¬ ((shaves barber barber) ↔ ¬ shaves barber barber) := 
    λ h => 
      have hn : ¬ shaves barber barber := λ h' => h.mp h' h'
      have hnn : ¬ ¬ shaves barber barber := λ h' => h' (h.mpr h')
      hnn hn
  this (h barber)
end Chap4_3

section Chap4_4
def even (n : Nat) : Prop := ∃ x : Nat, 2 * x = n
def prime (n : Nat) : Prop := ¬ ∃ x y : Nat, 1 < x ∧ x < n ∧ 1 < y ∧ y < n ∧ x * y = n
def infinitely_many_primes : Prop := ∀ k : Nat, ∃ p : Nat, prime p ∧ p > k
def Fermat_prime (n : Nat) : Prop := ∃ k : Nat, 2^(2^k) + 1 = n
def infinitely_many_Fermat_primes : Prop := ∀ k : Nat, ∃ p, Fermat_prime p ∧ p > k
def goldbach_conjecture : Prop := ∀ x : Nat, x > 2 ∧ even x -> (∃ p q, prime p ∧ prime q ∧ x = p + q)
def Goldbach's_weak_conjecture : Prop := ∀ x : Nat, x > 5 ∧ ¬ even x -> (∃ p q r, prime p ∧ prime q ∧ prime r ∧ x = p + q + r)
def Fermat's_last_theorem : Prop := ∀ n : Nat, n > 2 -> ¬ (∃ a b c, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^n + b^n = c^n)

end Chap4_4

section Chap4_5
open Classical
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r := 
  λ h => h.elim (λ _ hr => hr)
  
example (a : α) : r → (∃ _ : α, r) :=
  λ h1 => ⟨a, h1⟩
  
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
  ⟨λ ⟨w, pw, hr⟩ => ⟨⟨w, pw⟩, hr⟩,
   λ ⟨⟨w, pw⟩, hr⟩ => ⟨w, pw, hr⟩⟩
   
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
  ⟨λ ⟨w, hpqx⟩ => hpqx.elim (λ hpx => Or.inl ⟨w, hpx⟩) (λ hqx => Or.inr ⟨w, hqx⟩), 
   λ hpq => hpq.elim (λ ⟨w, hpw⟩ => ⟨w, Or.inl hpw⟩) (λ ⟨w, hqw⟩ => ⟨w, Or.inr hqw⟩)⟩
   
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
  ⟨λ h => λ ⟨w, hnpx⟩ => hnpx (h w), 
   λ h => λ w => byContradiction λ hnpw => h ⟨w, hnpw⟩⟩
   
example : (∃ x, p x ) ↔ ¬ (∀ x, ¬ p x) := 
  ⟨λ ⟨w, hpw⟩ => λ hnp => (hnp w) hpw, 
   λ h => byContradiction λ (h1 : ¬ ∃ x, p x) =>
     have (h2 : ∀ x, ¬ p x) := 
       λ w =>
       λ h3 : p w => h1 ⟨w, h3⟩
     h h2⟩
     
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  ⟨λ h => byContradiction λ h1 =>
       have h2 : (∀ x, ¬ p x) :=
         λ w => λ (h3 : p w) => h ⟨w, h3⟩
       h1 h2, 
   λ h => λ ⟨w, h1⟩ => (h w) h1⟩

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  ⟨λ h => byContradiction λ h1 => 
     have h2 : ∀ x, p x := λ w => byContradiction λ hnpw => h1 ⟨w, hnpw⟩
     h h2, 
   λ ⟨w, hnpw⟩ => λ h1 => hnpw (h1 w)⟩
   
example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  ⟨λ h => λ ⟨w, hpw⟩ => (h w) hpw, 
   λ h => λ w => λ hpw => h ⟨w, hpw⟩⟩
   
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := 
  ⟨λ ⟨w, hpwr⟩ => λ hpx => hpwr (hpx w), 
   λ h => byCases
     (λ h': ∀ x, p x => ⟨a, λ _ => h h'⟩)
     (λ h': ¬ ∀ x, p x => 
       have ⟨w, hnpw⟩ : ∃ x, ¬ p x := byContradiction λ hnnpx => 
         have nh' : ∀ x, p x := λ w => byContradiction λ hnpw => hnnpx ⟨w, hnpw⟩
         h' nh'
       ⟨w, λ hpw => absurd hpw hnpw⟩)⟩
       
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  ⟨λ ⟨w, hrpw⟩ => λ hr => ⟨w, hrpw hr⟩, 
   λ hrpx => byCases 
     (λ h' : ∃ x, p x => 
       have ⟨w, pw⟩ := h'
       ⟨w, λ _ => pw⟩)
     (λ h' : ¬ ∃ x, p x => byCases
       (λ hr : r  => absurd (hrpx hr) h')
       (λ hnr : ¬r  => ⟨a, λ hr => absurd hr hnr⟩))⟩
       
end Chap4_5
