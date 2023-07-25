inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  deriving Repr

namespace Weekday
def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday
end Weekday

open Weekday

def next_previous (d: Weekday ) : next (previous d) = d := by
  cases d <;> rfl

def bool_inhabited : Inhabited Bool := Inhabited.mk true
def nat_inhabited : Inhabited Nat := Inhabited.mk 0
def prod_inhabited {α : Inhabited u} {β : Inhabited v} : Inhabited (u × v) := 
  match α with
  | Inhabited.mk a => 
    match β with 
    | Inhabited.mk b => Inhabited.mk (Prod.mk a b)

def func_inhabited {α : Inhabited u} : Inhabited (β → u) :=
  match α with
  | Inhabited.mk a => 
    Inhabited.mk (λ _ => a)
    
namespace Hidden
open Nat

def add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := λ k => m + n + k = m + (n + k)) k
  rfl
  (λ k (ih : m + n + k = m + (n + k)) => 
    show m + n + (succ k) = m + (n + succ k) from 
    calc 
      m + n + (succ k) = succ (m + n + k) := rfl
      _ = succ (m + (n + k)) := by rw [ih]
      _ = (m + (n + (succ k))) := rfl)
      
def add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := λ n => m + n = n + m) n
  (show m + 0 = 0 + m by simp)
  (λ n (ih : m + n = n + m) => 
    show m + succ n = succ n + m by simp [ih, succ_add, add_succ])
      
def succ_add (m n : Nat) : succ m + n = succ (m + n) := 
  Nat.recOn (motive := λ n => succ m + n = succ (m + n)) n
  (show succ m + 0 = succ (m + 0) by rw [add_zero]) 
  (λ n (ih : succ m + n = succ (m + n)) => 
    show succ m + succ n = succ (succ (m + n)) from
    calc 
      succ m + succ n = succ (succ m + n) := rfl
      _ = succ (succ (m + n)) := by rw [ih])

end Hidden

namespace Hidden
open List

def append (as bs : List α) : List α :=
  match as with
  | nil => bs
  | cons a as' => cons a (append as' bs)
  
def nil_append (as : List α) : append nil as = as :=
  by rw [append]

def cons_append (a : α) (as bs : List α) 
                : append (cons a as) bs = cons a (append as bs) :=
  by rw [append]
  
def append_nil (as : List α) : append as nil = as :=
  List.recOn (motive := λ as => append as nil = as) as 
    (show append nil nil = nil from 
     calc 
       append nil nil = nil := by rw [append]) 
    (λ a as' (ih : append as' nil = as') =>
      show append (cons a as') nil = cons a as' from 
      calc 
        append (cons a as') nil = cons a (append as' nil) := by rw [append]
        _ = cons a as' := by rw [ih])

def append_assoc (as bs cs : List α) : append (append as bs) cs = append as (append bs cs) := 
  List.recOn (motive := λ as => append (append as bs) cs = append as (append bs cs)) as 
  (show append (append nil bs) cs = append nil (append bs cs) by simp [append])
  (λ a as' (ih : append (append as' bs) cs = append as' (append bs cs)) => 
     by simp [append, ih]
     -- show append (append (cons a as') bs) cs = append (cons a as') (append bs cs) from
     -- calc 
     --   append (append (cons a as') bs) cs = cons a (append (append as' bs) cs) := by rw [append, append]
     --   _ = cons a (append as' (append bs cs)) := by rw [ih]
     --   _ = append (cons a as') (append bs cs) := by rw [append]
)

end Hidden

example (p : Nat -> Prop) (hz : p 0) (hs : ∀ n, p (Nat.succ n)) : ∀ n, p n := by
  intro n
  cases n
  . exact hz
  . apply hs

open Nat
example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
  cases n with
  | zero => apply absurd rfl h
  | succ m => calc
     succ (pred (succ m)) = succ m := by rw [pred]

namespace Hidden
open List
def Tuple (α : Type) (n : Nat) :=
  {as : List α // as.length = n}
end Hidden

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  cases m + 3 * k
  exact hz
  apply hs

example (p : Prop) (m n : Nat) (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  cases Nat.lt_or_ge m n
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge
  
example (m n : Nat) : m - n = 0 ∨ m ≠ n := by
  cases Decidable.em (m = n) with
  | inl heq => 
        let h :(m - n = 0) := by rw [heq, Nat.sub_self]
        exact Or.inl h
  | inr hne => exact Or.inr hne
  
example (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [add_succ, ih]

example (m n : Nat) : succ m + n = succ (m + n) := by
  induction n <;> simp [*, add_succ]

example  (m n : Nat) : m + n = n + m := by
  induction n <;> simp [*, add_succ, succ_add]
  
example (m n k : Nat) : m + n + k = m + (n + k) := by
  induction k <;> simp [*, add_succ]

example (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by
  induction x, y using Nat.mod.inductionOn with
  | ind x y h₁ ih => 
      rw [Nat.mod_eq_sub_mod h₁.2]
      exact ih h
  | base x y h₁ => 
      have : ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp (Decidable.not_and_iff_or_not ..) h₁
      match this with
      | Or.inl h₁ => exact absurd h h₁
      | Or.inr h₁ => 
          have hgt: y > x := Nat.gt_of_not_le h₁
          rw [← Nat.mod_eq_of_lt hgt] at hgt
          assumption

example : p ∨ q → q ∨ p := by
  intro h
  match h with
  | Or.inl _ => apply Or.inr; assumption
  | Or.inr _ => apply Or.inl; assumption
  
example : s ∧ q ∧ r → p ∧ r → q ∧ p := by
  intro ⟨_, ⟨hq, _⟩⟩ ⟨hp, _⟩
  apply And.intro
  assumption; assumption
  
example : (fun (x : Nat × Nat) (y : Nat × Nat) => x.1 + y.2) =
          (fun (x : Nat × Nat) (z : Nat × Nat) => z.2 + x.1) := by
  funext (a, _) (_, d)
  show a + d = d + a
  rw [Nat.add_comm]
  
example (m n k : Nat) (h : succ (succ m) = succ (succ n)) 
        : n + k = m + k := by
  injection h with h'
  injection h' with h''
  rw [h'']
  
example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  injection h
  
inductive Ve (α : Type u) : Nat -> Type u where
  | nil : Ve α 0
  | cons : α → {n : Nat} → Ve α n → Ve α (n + 1)

inductive Equ {α : Sort u} (a : α) : α -> Prop where
  | refl : Equ a a
  
example {α : Type u} {a b : α} (h : Eq a b) : Eq b a :=
  match h with
  | rfl => rfl
  
example {α : Type u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c := 
  by rw [h₁]; exact h₂
  
example {α β : Type u} {a b : α} (f : α → β) (h : Eq a b) : Eq (f a) (f b) :=
  by rw [h]

