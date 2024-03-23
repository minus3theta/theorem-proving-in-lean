section ex1
namespace Hidden
open Nat

@[simp] def add : Nat → Nat → Nat
  | x, 0 => x
  | x, succ y => succ (add x y)

@[simp] def mul : Nat → Nat → Nat
  | _, 0 => 0
  | x, succ y => add x (mul x y)

@[simp] def pow : Nat → Nat → Nat
  | _, 0 => 1
  | x, succ y => mul x (pow x y)

@[simp] theorem add_assoc : ∀ a b c : Nat, add a (add b c) = add (add a b) c
  | _, _, 0 => by simp
  | a, b, succ c => by simp[add_assoc]

@[simp] theorem zero_add : ∀ x : Nat, add 0 x = x
  | 0 => by simp
  | succ x => by simp[zero_add]

@[simp] theorem succ_add : ∀ x y : Nat, add (succ x) y = succ (add x y)
  | _, 0 => by simp
  | x, succ y => by simp[succ_add]

@[simp] theorem add_comm : ∀ a b : Nat, add a b = add b a
  | _, 0 => by simp
  | x, succ y => by
    calc add x (succ y)
      _ = succ (add x y) := by simp
      _ = succ (add y x) := by rw[add_comm]
      _ = add (succ y) x := by simp

@[simp] theorem zero_mul : ∀ x : Nat, mul 0 x = 0
  | 0 => by simp
  | succ x => by simp[zero_mul]

@[simp] theorem succ_mul : ∀ x y : Nat, mul (succ x) y = add y (mul x y)
  | _, 0 => by simp
  | x, succ y => by simp[succ_mul]

@[simp] theorem left_distrib : ∀ a b c : Nat, mul a (add b c) = add (mul a b) (mul a c)
  | 0, _, _ => by simp
  | succ a, b, c => by simp[left_distrib]

theorem mul_assoc : ∀ a b c : Nat, mul a (mul b c) = mul (mul a b) c
  | _, _, 0 => by simp
  | a, b, succ c => by simp[mul_assoc]

end Hidden
end ex1
