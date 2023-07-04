import Exercises

def main : IO Unit :=
  IO.println s!"Hello, world!"

namespace Hidden

inductive Boo where
  | false : Boo
  | true : Boo

def and (a b : Boo) : Boo := 
  match a with
  | Boo.true => b
  | Boo.false => Boo.false
  
def prod_example (p : Bool × Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p (fun b n => cond b (2 * n) (2 * n + 1))
  
def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := fun _ => Nat) s (2 * .) (2 * . + 1)
  
inductive Exists {α : Sort u} (p : α -> Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p
  
open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x)
    n
    (show 0 + 0 = 0 from rfl)
    (fun (n : Nat) (ih : 0 + n = n) =>
      show 0 + Nat.succ n = Nat.succ n from
      calc
        0 + Nat.succ n = Nat.succ (0 + n) := rfl
                 _ = Nat.succ n := by rw [ih])
             
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    rfl
    (fun _ (ih) => by simp [Nat.add_succ, ih])
    
theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
    (show m + 0 = 0 + m by rw [Nat.add_zero, Nat.zero_add])
    (fun n (_ : m + n = n + m) => 
      calc
        m + succ n = succ (m + n) := rfl
                 _ = succ (n + m) := by rw [Nat.add_comm]
                 _ = succ n + m := by rw [Nat.succ_add])
                       
end Hidden

