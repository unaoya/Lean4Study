#check 1
#check 1 + 1

def y := 1
#check y
#print y
#eval y

def x : Nat := 1

def h : 1 + 1 = 2 := rfl

def h2 : 1 = 1 := rfl

def h21 : 1 = 1 := Eq.refl 1

def h22 : Eq 1 1 := Eq.refl 1

#check h2
#check h21
#check h22
#print h2
#print h21
#print h22

def h3 : 123 + 234  = 357 := rfl

def h4 (x : Nat) : x + 0 = x := by sorry

def h5 : ∀ x, x + 0 = x := by sorry

#check h4
#check h5
#print h4
#print h5

def h6 (x : Nat) : x + 0 = x := rfl

def h7 : ∀ x, x + 0 = x := rfl

def h8 : ∀ x, x + 0 = x := fun x ↦ rfl

def h9 : ∀ x, x + 0 = x := fun _ ↦ rfl

inductive Eqq : Nat → Nat → Prop where
  | r a : Eqq a a

#check Eqq
#check Eqq 1 1
#check Eqq 1 2
#check Eqq.r 1

def h10 : Eqq 1 1 := Eqq.r 1

#check Eqq (1 + 1) 2

def h11 : Eqq (1 + 1) 2 := Eqq.r 2

def h12 (x : Nat) : Eqq x (x + 0) := Eqq.r x

def h13 (x y : Nat) : x + y = y + x :=
  Nat.add_comm x y

def h14 (x y : Nat) : x + y = y + x := by
  exact Nat.add_comm x y

def h15 (x y : Nat) : x + y = y + x := by
  apply Nat.add_comm

def h16 (x y : Nat) : x + y = y + x := by
  rw [Nat.add_comm]

#check Eq
#print Eq
#check Eq.refl
#print Eq.refl

#check Eq.symm
#check Eq.trans

-- theoremなのかdefなのか？
theorem Eqq.symm {a b : Nat} (h : Eqq a b) : Eqq b a :=
  match h with
  | Eqq.r a => Eqq.r a

example (h : Eqq 1 x) : Eqq x 1 := Eqq.symm h

namespace MyEq

#check Eq
#check MyEq.Eq

inductive Eq (a : Nat) : Nat → Prop where
  | r : Eq a a

#check MyEq.Eq
#check Eq

variable {a b c : Nat}

theorem symm (h : Eq a b) : Eq b a :=
  match h with
  | Eq.r => Eq.r

theorem trans (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  match h₁ with
  | Eq.r =>
    match h₂ with
    | Eq.r => Eq.r

theorem congr (f : Nat → Nat) (h : Eq a b) : Eq (f a) (f b) :=
  match h with
  | Eq.r => Eq.r

def add_one (x : Nat) : Nat := x + 1

example (h : Eq a b) : Eq (add_one a) (add_one b) :=
  congr add_one h

-- Eq a bとa=bが同値なことを証明できるか？
