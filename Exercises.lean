section Chap3
    variable (p q r : Prop)

    -- commutativity of ∧ and ∨
    example : p ∧ q ↔ q ∧ p := 
    ⟨λ h => ⟨h.right, h.left⟩, λ h => ⟨h.right, h.left⟩⟩
    example : p ∨ q ↔ q ∨ p := 
    ⟨λ h => h.elim Or.inr Or.inl, λ h => h.elim Or.inr Or.inl⟩

    -- associativity of ∧ and ∨
    example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    ⟨λ h => ⟨h.left.left, ⟨h.left.right, h.right⟩⟩, 
    λ h => ⟨⟨h.left, h.right.left⟩, h.right.right⟩⟩
    example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
    ⟨λ h => h.elim (λ g => g.elim Or.inl (Or.inr ∘ Or.inl)) (Or.inr ∘ Or.inr), 
    λ h => h.elim (Or.inl ∘ Or.inl) (λ g => g.elim (Or.inl ∘ Or.inr) Or.inr)⟩

    -- distributivity
    example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    ⟨λ h => h.right.elim (Or.inl ∘ (λ hq => ⟨h.left, hq⟩)) (Or.inr ∘ (λ hr => ⟨h.left, hr⟩)), 
    λ h => h.elim (λ hpq => ⟨hpq.left, Or.inl hpq.right⟩) (λ hpr => ⟨hpr.left, Or.inr hpr.right⟩)⟩

    example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
    ⟨λ l => l.elim (λ hp => ⟨Or.inl hp, Or.inl hp⟩) (λ hqr => ⟨Or.inr hqr.left, Or.inr hqr.right⟩), 
    λ r => r.left.elim Or.inl (λ hq => r.right.elim Or.inl (λ hr => Or.inr ⟨hq, hr⟩))⟩

    -- other properties
    example : (p → (q → r)) ↔ (p ∧ q → r) := 
    ⟨λ p_q_r => (λ hpq => p_q_r hpq.left hpq.right), 
    λ paq_r => (λ hp => (λ hq => paq_r ⟨hp, hq⟩))⟩

    example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
    ⟨λ poq_r => ⟨poq_r ∘ Or.inl, poq_r ∘ Or.inr⟩, 
    λ pr_qr => (λ hpq => hpq.elim pr_qr.left pr_qr.right)⟩

    -- note: ¬p is equivalent to p → False
    example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
    ⟨λ npq => ⟨λ hp => npq (Or.inl hp), λ hq => npq (Or.inr hq)⟩, 
    λ npnq => (λ hpq => hpq.elim npnq.left npnq.right)⟩

    example : ¬p ∨ ¬q → ¬(p ∧ q) := 
    λ npnq => npnq.elim (λ hnp => (λ hpq => hnp hpq.left)) (λ hnq => (λ hpq => hnq hpq.right))

    example : ¬(p ∧ ¬p) := 
    λ pnp => pnp.right pnp.left

    example : p ∧ ¬q → ¬(p → q) := 
    λ pnq => (λ hpq => pnq.right (hpq pnq.left))

    -- ex falso
    example : ¬p → (p → q) := 
    λ hnp => λ hp => False.elim (hnp hp)

    example : (¬p ∨ q) → (p → q) := 
    λ npq => λ hp => npq.elim (λ np => False.elim (np hp)) id

    example : p ∨ False ↔ p := 
    ⟨λ hpf => hpf.elim id False.elim, Or.inl⟩

    example : p ∧ False ↔ False := 
    ⟨And.right, False.elim⟩

    example : (p → q) → (¬q → ¬p) := 
    λ hpq => λ hnq => λ hp => hnq (hpq hp)

    section classical
        open Classical
        variable (p q r : Prop)

        example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := 
        λ p_qr => byCases
            (λ (hq : q) => Or.inl (λ _ => hq)) 
            (λ (hnq : ¬q) => byCases 
            (λ (hr : r) => Or.inr (λ _ => hr)) 
            (λ (hnr : ¬r) => (Or.inl (λ p => (p_qr p).elim (False.elim ∘ hnq) (False.elim ∘ hnr)))))

        example : ¬(p ∧ q) → ¬p ∨ ¬q := 
        λ hnpq => byCases 
            (λ (hp : p) => byCases
            (λ (hq : q) => False.elim (hnpq ⟨hp, hq⟩))
            (λ (hnq : ¬q) => Or.inr hnq))
            (λ (hnp : ¬p) => Or.inl hnp)

        example : ¬(p → q) → p ∧ ¬q := 
        λ npq => byCases
            (λ (hq : q) => False.elim (npq (λ _ => hq)))
            (λ (hnq : ¬q) => byCases 
            (λ (hp : p) => ⟨hp, hnq⟩)
            (λ (hnp : ¬p) => False.elim (npq (λ hp => absurd hp hnp))))

        example : (p → q) → (¬p ∨ q) := 
        λ hpq => byCases 
            (λ (hq : q) => Or.inr hq)
            (λ (hnq : ¬q) => byCases 
            (λ (hp : p) => False.elim (hnq (hpq hp)))
            (λ (hnp : ¬p) => Or.inl hnp))

        example : (¬q → ¬p) → (p → q) := 
        λ hnqnp => byCases
            (λ (hq : q) => λ _ => hq)
            (λ (hnq : ¬q) => byCases 
            (λ (hp : p) => False.elim ((hnqnp hnq) hp))
            (λ (hnp : ¬p) => λ hp => absurd hp hnp))

        example : p ∨ ¬p := byCases
        (λ (hp : p) => Or.inl hp)
        (λ (hnp : ¬p) => Or.inr hnp)

        example : (((p → q) → p) → p) := byCases
        (λ (hp : p) => λ _ => hp)
        (λ (hnp : ¬p) => λ hpqp => hpqp (λ hp => absurd hp hnp))
    end classical

    example: ¬(p ↔ ¬p) :=
    λ h => 
        have hnp : ¬p := λ hp => (h.mp hp) hp;
        have hnnp : ¬¬p := λ hnp => hnp (h.mpr hnp);
        hnnp hnp
section Chap3


section Chap4_5
open Classical
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := 
  λ h => h.elim (λ _ hr => hr)
  
example (a : α) : r → (∃ e : α, r) :=
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

example : α -> ((∃ x : α, r) ↔ r) := 
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
