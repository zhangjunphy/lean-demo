def fib : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => fib (n+1) + fib n
  
def fibFast (n : Nat) : Nat :=
  (loop n).2
where
  loop : Nat → Nat × Nat
    | 0 => (0, 1)
    | n + 1 => let p := loop n; (p.2, p.1 + p.2)
    
def fibFast2 (n : Nat) : Nat :=
  let rec loop : Nat → Nat × Nat
    | 0 => (0, 1)
    | n+1 => let p := loop n ; (p.2, p.1 + p.2)
  (loop n).2

def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)
  loop n []

example (n : Nat) (a : α) : (replicate n a).length = n := by 
  let rec aux (n : Nat) (as : List α) 
              : (replicate.loop a n as).length = n + as.length := by
        match n with 
        | 0 => simp [replicate.loop]
        | n+1 => (calc 
                   (replicate.loop a (n+1) as).length = 
                     (replicate.loop a n (a::as)).length  := by simp [replicate.loop]
                   _ = n + (a::as).length := by simp [aux n]
                   _ = n + (as.length + 1) := by simp [List.length]
                   _ = n + (1 + as.length) := by simp [Nat.add_comm]
                   _ = n + 1 + as.length := by simp [Nat.add_assoc])
  exact aux n []

example (n : Nat) (a : α) : (replicate n a).length = n := by 
  exact aux n []
  where
    aux (n : Nat) (as : List α) 
              : (replicate.loop a n as).length = n + as.length := by
        match n with 
        | 0 => simp [replicate.loop]
        | n+1 => simp [replicate.loop, aux n, List.length, Nat.add_succ, Nat.succ_add]
        
noncomputable def f {α : Sort u}
  (r : α -> α -> Prop)
  (h : WellFounded r)
  (C : α -> Sort v)
  (F : (x : α) -> ((y : α) -> r y x -> C y) -> C x)
  : (x : α) -> C x := WellFounded.fix h F

namespace Hidden
theorem div_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun h => Nat.sub_lt (Nat.lt_of_lt_of_le h.left h.right) h.left
  
def div.F (x : Nat) (f : (x₁ : Nat) → x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    f (x - y) (div_lemma h) y + 1
  else
    0
    
--noncomputable def div := WellFounded.fix (measure id).wf div.F
def div (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    div (x - y) y + 1
  else
    0
decreasing_by apply div_lemma; assumption;

example (x y : Nat) : div x y = if 0 < y ∧ y ≤ x then div (x - y) y + 1 else 0 := by
  conv => lhs; unfold div
  
example (x y : Nat) (h : 0 < y ∧ y ≤ x) : div x y = div (x - y) y + 1 := by
  conv => lhs; unfold div
  simp [h]

def natToBin : Nat → List Nat
  | 0 => [0]
  | 1 => [1]
  | n + 2 =>
    have : (n + 2) / 2 < n + 2 := sorry
    natToBin ((n + 2) / 2) ++ [n % 2]

def ack : Nat → Nat -> Nat
    | 0, y => y + 1
    | x+1, 0 => ack x 1
    | x+1, y+1 => ack x (ack (x+1) y)
termination_by ack x y => (x, y)
decreasing_by 
  simp_wf
  first | apply Prod.Lex.right; simp_arith
        | apply Prod.Lex.left; simp_arith

def takeWhile (p : α → Bool) (as : Array α) : Array α :=
  go 0 #[]
where
  go (i : Nat) (r : Array α) : Array α :=
     if h : i < as.size then
       let a := as.get ⟨i, h⟩
       if p a then
         go (i+1) (r.push a)
       else
         r
     else
       r
termination_by go i r => as.size - i

end Hidden

mutual
  def even : Nat → Bool
    | 0 => true
    | n+1 => odd n
  def odd : Nat → Bool
    | 0 => false
    | n+1 => even n
end

example : ∀ a, even a = not (odd a) := by
  intro a; induction a
  . trivial
  . simp [even, odd, *]    
  
mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : ∀ n, Odd n → Even (n + 1)
    
  inductive Odd : Nat → Prop where
    | odd_succ : ∀ n, Even n → Odd (n + 1)
end

open Even Odd

theorem not_odd_zero : ¬ Odd 0 := 
  fun h => nomatch h
  
theorem even_of_odd_succ : ∀ n, Odd (n + 1) → Even n
  | _, odd_succ n h => h
  
inductive Term where
  | const : String → Term
  | app : String → List Term → Term

namespace Term 
mutual 
  def numConsts : Term → Nat
    | const _ => 1
    | app _ cs => numConstsLst cs
    
  def numConstsLst : List Term → Nat
    | [] => 0
    | c :: cs => numConsts c + numConstsLst cs
end

mutual
  def replaceConst (a b : String) : Term → Term
    | const c => if a == c then const b else const c
    | app f cs => app f (replaceConstsLst a b cs)
  def replaceConstsLst (a b : String) : List Term → List Term
    | [] => []
    | c :: cs => (replaceConst a b c) :: (replaceConstsLst a b cs)
end

mutual 
theorem numConsts_replaceConst (a b : String) (e : Term)
        : numConsts (replaceConst a b e) = numConsts e := by
  match e with
  | const c => simp [replaceConst]; split <;> simp [numConsts]
  | app f cs => simp [replaceConst, numConsts, numConsts_replaceConstsLst a b cs]
  
theorem numConsts_replaceConstsLst (a b : String) (cs : List Term)
        : numConstsLst (replaceConstsLst a b cs) = numConstsLst cs := by
  match cs with
  | [] => trivial
  | c :: cs => simp [numConstsLst, replaceConstsLst, 
                     numConsts_replaceConst a b c, 
                     numConsts_replaceConstsLst a b cs]
end

end Term

namespace Hidden
inductive Vector (α : Type u) : Nat → Type u
  | nil : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

def tailAux (v : Vector α m) : m = n + 1 → Vector α n :=
  Vector.casesOn (motive := fun x _ => x = n + 1 → Vector α n) v
    (fun h : 0 = n + 1 => Nat.noConfusion h)
    (fun (a : α) (m : Nat) (as : Vector α m) =>
      fun (h : m + 1 = n + 1) => Nat.noConfusion h (fun h1 : m = n => h1 ▸ as))
      
def tail (v : Vector α (n+1)) : Vector α n :=
  tailAux v rfl
  
open Vector
def head : {n : Nat} → Vector α (n + 1) -> α
  | n, cons a as => a
  
def map (f : α → β → γ) : {n : Nat} → Vector α n → Vector β n → Vector γ n
  | 0, nil, nil => nil
  | n+1, cons a as, cons b bs => cons (f a b) (map f as bs)
  
def mapAux1 (v : Vector α m) : m = n + 1 → α × (Vector α n) :=
  Vector.casesOn (motive := fun x _ => x = n + 1 → α × Vector α n) v
  (fun h : 0 = n + 1 => Nat.noConfusion h)
  (fun (a : α) (m : Nat) (as : Vector α m) => 
    fun (h : m + 1 = n + 1) => Nat.noConfusion h (fun h1 : m = n => (a, h1 ▸ as)))
    
def mapAux2 (v : Vector α m) (u : Vector β m) : 
            m = n + 1 → α × β × (Vector α n) × (Vector β n) :=
  fun h =>
    let x := mapAux1 v h
    let y := mapAux1 u h
    (x.fst, y.fst, x.snd, y.snd)
    
def mapAux (v : Vector α (n+1)) (u : Vector β (n+1)) : 
           α × β × (Vector α n) × (Vector β n) :=
  mapAux2 v u rfl
    
noncomputable def map' (f : α → β → γ) : Vector α n → Vector β n → Vector γ n :=
  Nat.recOn (motive := λ x => Vector α x → Vector β x → Vector γ x) n
  (λ _ _ => nil)
  (λ n (h: Vector α n → Vector β n → Vector γ n) => 
    fun v u => 
      let (a, b, as, bs) := mapAux v u
      cons (f a b) (h as bs))
  
end Hidden

inductive ImageOf {α β : Type u} (f : α → β) : β → Type u where
  | imf : (a : α) → ImageOf f (f a)
  
open ImageOf

def inverse {f : α → β} : (b : β) → ImageOf f b → α
  | .(f a), imf a => a

namespace Hidden
def add : Nat -> Nat -> Nat
  | m, 0 => m
  | m, n+1 => add (m+1) n
  
def mul : Nat -> Nat -> Nat
  | 0, _ => 0
  | m+1, n => add n (mul m n)
  
def exp : Nat -> Nat -> Nat
  | _, 0 => 1
  | m, n+1 => mul m (exp m n)
  
theorem add_one : add n 1 = Nat.succ n := rfl
theorem one_add : add 1 n = Nat.succ n := 
  Nat.recOn (motive := λ x => add 1 x = Nat.succ x) n
  rfl
  (λ x h => by calc
    add 1 (Nat.succ x) = add 1 (add 1 x) := by simp [h])
theorem add_zero : add n 0 = n := rfl
theorem zero_add : add 0 n = n := 
  Nat.recOn (motive := λ x => add 0 x = x) n
  rfl
  (λ _ h => by simp [add, h])
  
theorem add_succ : add m (Nat.succ n) = Nat.succ (add m n) := 
  Nat.recOn (motive := λ x => add m (Nat.succ x) = Nat.succ (add m x)) n
  (by simp [add, Nat.succ])
  (λ x h => by calc
    add (x+1) (n+1) = add x (n+1+1) := by simp [add]
    )
  
theorem succ_add : add (Nat.succ m) n = Nat.succ (add m n) := 
  Nat.recOn (motive := λ x => add (Nat.succ x) n = Nat.succ (add x n)) m
  (by trivial)
  (λ x h => by calc
    add ((x + 1) + 1) n = add (x + 1) (n + 1) := by simp [add]
    _ = Nat.succ (add x (n+1)) := by apply [h])
  
theorem add_comm : add m n = add n m :=
  Nat.recOn (motive := λ x => add x n = add n x) m
  (let h : add 0 n = add n 0 := 
    Nat.recOn (motive := λ x => add 0 x = add x 0) n
    (by trivial)
    (λ x h => by calc
      add 0 (Nat.succ x) = Nat.succ x := by simp [add]
      _ = Nat.succ (add x 0) := by simp [add, ←h]
      _ = add (Nat.succ x) 0 := sorry)
   h) 
  sorry
  
example : exp a (add b c) = mul (exp a b) (exp a c) := 
  sorry

end Hidden
