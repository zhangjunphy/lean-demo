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
