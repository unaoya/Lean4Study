example : ∀ (x : Nat), x * 1 = x :=
  fun x ↦ Eq.trans rfl (Nat.zero_add x)

example : ∀ (x : Nat), x * 1 = x :=
  fun x ↦ Nat.zero_add x

example : ∀ (x : Nat), x * 1 = x :=
  Nat.zero_add

example : ∀ (x : Nat), x * 1 = x :=
  fun x ↦ Nat.mul_one x

example : ∀ (x : Nat), x * 1 = x :=
  Nat.mul_one

example : ∀ (x : Nat), x = x * 1 :=
  fun x ↦ Eq.symm (Nat.mul_one x)

example : ∀ (x : Nat), x * 1 = 0 + x :=
  fun _ ↦ rfl

example : ∀ (x : Nat), 0 + x = x :=
  fun x ↦ Nat.zero_add x

example : ∀ (x : Nat), x + 0 = x :=
  fun _ ↦ rfl

example : ∀ (x : Nat), x * 2 = x + x :=
  fun x ↦ Eq.trans rfl (congrArg (fun y ↦ y + x) (Nat.zero_add x))

example : ∀ (x : Nat), x * 2 = x + x :=
  fun x ↦ (congrArg (fun y ↦ y + x) (Nat.zero_add x))
