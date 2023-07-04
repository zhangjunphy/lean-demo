def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂
  
theorem List.isPrefix_self (as: List α) : isPrefix as as :=
  ⟨[], by simp⟩
attribute [local simp] List.isPrefix_self

example : isPrefix [1, 2, 3] [1, 2, 3] := by simp

instance : LE (List α) where 
  le := isPrefix
  
example (as : List α) : as ≤ as := ⟨[], by simp⟩

def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b : α}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : symmetric r := by
  intro a b
  intro rab
  let raa := reflr a
  let rba := euclr rab raa
  exact rba
  
theorem th2  {r : α → α → Prop} (symmr : symmetric r) (euclr : euclidean r) : transitive r := by
  intro a b c
  intro rab rbc
  let rba := symmr rab
  exact euclr rba rbc
  
theorem th3 {r : α -> α -> Prop} {reflr: reflexive r} {euclr : euclidean r} : transitive r := by
  intros a b c rab rbc
  let rba := euclr rab (reflr a)
  exact euclr rba rbc
