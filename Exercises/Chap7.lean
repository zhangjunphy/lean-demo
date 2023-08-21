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
    
theorem sub_eq_zero_of_le {m n : Nat} (h : le m n) : m - n = 0 := sorry
  
#check Nat.sub_eq_zero_of_le

end Hidden
