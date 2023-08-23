import Std.Data.HashMap

-- P1
namespace Hidden
def pred (n : Nat) : Nat :=
  match n with 
  | 0 => 0
  | Nat.succ n' => n'
  
def add (m n : Nat) : Nat :=
  match n with
  | 0 => m
  | Nat.succ (n') => Nat.succ (add m n')
  
def sub (m n : Nat) : Nat :=
  match n with 
  | 0 => m
  | Nat.succ n' => pred (sub m n')

inductive le (n : Nat) : Nat → Prop
  | refl     : le n n
  | step {m} : le n m → le n (Nat.succ m)
  
theorem add_zero (n : Nat) : add n 0 = n := rfl
theorem zero_add (n : Nat) : add 0 n = n := 
  Nat.recOn (motive := λ x => add 0 x = x) n rfl
  (λ x (ih : add 0 x = x) => by simp [add, ih])
theorem add_succ (m n : Nat) : add m (Nat.succ n) = Nat.succ (add m n) :=
  Nat.recOn (motive := λ x => add m (Nat.succ x) = Nat.succ (add m x)) n rfl
  (λ x _ => by rfl)
theorem succ_add (m n : Nat) : add (Nat.succ m) n = Nat.succ (add m n) :=
  Nat.recOn (motive := λ x => add (Nat.succ m) x = Nat.succ (add m x)) n rfl
  (λ x (ih : add (Nat.succ m) x = Nat.succ (add m x)) => by simp [add, ih])
theorem add_comm (m n : Nat): add m n = add n m := 
  Nat.recOn (motive := λ x => add m x = add x m) n 
  (by simp [add_zero, zero_add])
  (λ x (ih : add m x = add x m) => by simp [add, ih, succ_add])
theorem add_assoc (l m n : Nat): add (add l m) n = add l (add m n) := 
  Nat.recOn (motive := λ x => add (add l m) x = add l (add m x)) n 
  rfl
  (λ x (ih : add (add l m) x = add l (add m x)) => by simp [add, ih, succ_add])

theorem sub_zero (n : Nat) : sub n 0 = n := rfl
theorem zero_sub (n : Nat) : sub 0 n = 0 := 
  Nat.recOn (motive := λ x => sub 0 x = 0) n
    rfl 
    (λ x (ih: sub 0 x = 0) => by simp [sub, ih])
end Hidden

-- P2
namespace Hidden
def length (l : List α) : Nat :=
  match l with 
  | List.nil => 0
  | List.cons _ t => 1 + length t
  
def reverse (l : List α) : List α :=
  match l with 
  | List.nil => List.nil
  | List.cons h t => reverse t ++ (List.cons h List.nil)

theorem length_add (s t : List α) : length (s ++ t) = length s + length t := 
  List.recOn (motive := λ x => length (x ++ t) = length x + length t) s 
  (by simp [length])
  (λ h tail (ih : length (tail ++ t) = length tail + length t) => 
    by calc
      length ((List.cons h tail) ++ t) = 1 + length (tail ++ t) := by simp [length]
      _ = (1 + length tail) + length t := by simp [ih, Nat.add_assoc]
      _ = length (List.cons h tail) + length t := by simp [length])
      
theorem length_reverse (t : List α) : length (reverse t) = length t :=
  List.recOn (motive := λ x => length (reverse x) = length x) t rfl 
  (λ hd tl (ih : length (reverse tl) = length tl) => 
    by calc
      length (reverse (List.cons hd tl)) = length (reverse tl ++ (List.cons hd List.nil)) := by trivial
      _ = length (reverse tl) + length (List.cons hd List.nil) := by simp [length_add]
      _ = length tl + 1 := by simp [ih, length]
      _ = length (List.cons hd tl) := by simp [length, Nat.add_comm])
      
theorem reverse_last (h : α) (l : List α) : reverse (l ++ [h]) = List.cons h (reverse l) := 
  List.recOn (motive := λ x => reverse (x ++ [h]) = List.cons h (reverse x)) l rfl 
  (λ hd tl (ih : reverse (tl ++ [h]) = List.cons h (reverse tl)) => by calc
    reverse ((List.cons hd tl) ++ [h]) = reverse (tl ++ [h]) ++ [hd] := rfl
    _ = List.cons h (reverse tl) ++ [hd] := by rw [ih]
    _ = List.cons h (reverse (List.cons hd tl)) := rfl)

theorem reverse_reverse (t : List α) : reverse (reverse t) = t :=
  List.recOn (motive := λ x => reverse (reverse x) = x) t rfl
  (λ hd tl (ih : reverse (reverse tl) = tl) => by calc
    reverse (reverse (List.cons hd tl)) = reverse (reverse tl ++ [hd]) := rfl
    _ = List.cons hd (reverse (reverse tl)) := by rw [reverse_last]
    _ = List.cons hd tl := by rw [ih])
end Hidden

-- P3
namespace Hidden
inductive Expr where
  | const (n : Nat) : Expr
  | var (v : Nat) : Expr
  | plus (l r: Expr) : Expr
  | times (l r : Expr) : Expr
  
def eval (e : Expr) (st : Std.HashMap Nat Nat) : Nat :=
  match e with
  | Expr.const n => n
  | Expr.var v => Std.HashMap.find! st v
  | Expr.plus l r => (eval l st) + (eval r st)
  | Expr.times l r => (eval l st) * (eval r st)
  
open Expr
def gen_st : Std.HashMap Nat Nat := 
  let st := Std.HashMap.empty
  Std.HashMap.insert st 0 5

#eval eval (times (plus (const 3) (var 0)) (times (const 2) (const 2))) gen_st
end Hidden
