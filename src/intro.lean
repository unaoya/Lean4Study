#check 0
#check 1
#check 2

#check Nat
#check Type
#check Type 1

def x : Nat := 1
#check x

def y := 1
#check y

-- def a : Nat

def z : Type := Nat
#check z

def f : Nat → Nat := fun x ↦ x + 1
#check f
#check f 1
#check f x

def g (x : Nat) : Nat := x + 1
#check g

#check f (g x)
#eval f (g x)
-- #check f g x

def h (x : Nat) : Nat := f (g x)
#check h

#check Prop
#check 1 = 1
#check 1 = 2
#check True
#check False

def h1 : 1 + 1 = 2 := rfl

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

#check x + y

#check 2 * 2 = 1 + 3

example : 2 * 2 + 3 = 1 + 3 * 2 := rfl

#check Nat.zero
#print Nat.zero

#check Nat.succ Nat.zero
#print Nat.succ


def f_eq_g : f = g := rfl

def f_eq_g2 : f = g := asdfg

theorem f_eq_g3 : f = g := rfl

#check f
#check f = g
#check f_eq_g
#check f_eq_g3
#check Prop
#check rfl
#print rfl

def f_eq_g4 (x : Nat) : f x = g x := rfl

def f_eq_g5 : ∀ x, f x = g x := rfl

def F (x : Nat) : Nat := x + x

def G (x : Nat) : Nat := 2 * x

def H (x : Nat) : Nat := (1 + 1) * x

example : F = G := by
  funext x
  rw [F]
  rw [G]
  sorry

variable (x : Nat)

example : H = G := rfl

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
