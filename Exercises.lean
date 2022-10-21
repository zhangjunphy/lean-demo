section
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
section


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

section
variable (p : Prop)

example: ¬(p ↔ ¬p) :=
  λ h => 
    have hnp : ¬p := λ hp => (h.mp hp) hp;
    have hnnp : ¬¬p := λ hnp => hnp (h.mpr hnp);
    hnnp hnp
end
