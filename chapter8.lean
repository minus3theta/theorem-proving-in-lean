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

@[simp] theorem mul_assoc : ∀ a b c : Nat, mul a (mul b c) = mul (mul a b) c
  | _, _, 0 => by simp
  | a, b, succ c => by simp[mul_assoc]

@[simp] theorem right_distrib : ∀ a b c : Nat, mul (add a b) c = add (mul a c) (mul b c)
  | _, _, 0 => by simp
  | _, _, succ _ => by simp[right_distrib]

@[simp] theorem mul_comm : ∀ a b : Nat, mul a b = mul b a
  | _, 0 => by simp
  | a, succ b => by
      calc mul a (succ b)
        _ = add a (mul a b) := rfl
        _ = add a (mul b a) := by rw[mul_comm]
        _ = _ := by simp

theorem exp_distrib : ∀ a b c : Nat, pow a (add b c) = mul (pow a b) (pow a c)
  | _, _, 0 => by simp
  | a, b, succ c => by simp[exp_distrib]

end Hidden
end ex1

section ex2
namespace Hidden
open List

@[simp] def append : List α → List α → List α
  | nil, bs => bs
  | cons a as, bs => cons a (append as bs)

@[simp] def reverse : List α → List α
  | nil => nil
  | cons a as => append (reverse as) [a]

@[simp] theorem append_nil : ∀ xs : List α, append xs nil = xs
  | nil => rfl
  | cons x xs => by simp[append_nil]

@[simp] theorem reverse_assoc :
  ∀ xs ys zs : List α, append xs (append ys zs) = append (append xs ys) zs
  | nil, _, _ => rfl
  | x :: xs, ys, zs => by simp[reverse_assoc]

@[simp] theorem reverse_append :
  ∀ xs ys : List α, reverse (append xs ys) = append (reverse ys) (reverse xs)
  | nil, ys => by simp
  | x :: xs, ys => by simp[reverse_append]

@[simp] theorem reverse_reverse : ∀ xs : List α, reverse (reverse xs) = xs
  | nil => rfl
  | cons x xs => by simp[reverse_reverse]

end Hidden
end ex2

section ex4

inductive Vector (α : Type u) : Nat → Type u
  | nil : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
deriving Repr

open Vector
open Nat
namespace Vector

#check Nat.noConfusionType

def append : {m n o: Nat} → (m + n = o) → Vector α m → Vector α n → Vector α o
  | 0, n, o, h, nil, bs => by
      have : n = o := by rw[Nat.zero_add] at h; assumption
      rw[this] at bs
      exact bs
  | succ m, n, succ o, h, cons a as, bs =>
      have : succ m + n = succ (m + n) := by rw[Nat.succ_add]
      have : m + n = o := by
        rw[this] at h
        injection h
      let cs := cons a (append this as bs)
      cs
  | Nat.succ m, n, 0, h, _, _ => by
      rw[succ_add] at h
      contradiction

#eval append rfl (cons 1 nil) (cons 2 (cons 3 nil))

#check @append

def append_2 : {m n : Nat} → Vector α m → Vector α n → Vector α (m+n)
  | _, _, as, bs => append rfl as bs

#check append_2 (cons 1 nil) (cons 2 (cons 3 nil))
#eval append_2 (cons 1 nil) (cons 2 (cons 3 nil))

end Vector

end ex4

section ex5

inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr

open Expr

def sampleExpr : Expr :=
  plus (times (var 0) (const 7)) (times (const 2) (var 1))

def eval (v : Nat → Nat) : Expr → Nat
  | const n => n
  | var n => v n
  | plus e₁ e₂ => eval v e₁ + eval v e₂
  | times e₁ e₂ => eval v e₁ * eval v e₂

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

#eval eval sampleVal sampleExpr

def simpConst : Expr → Expr
  | plus (const n₁) (const n₂) => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e => e

def fuse : Expr → Expr
  | plus e₁ e₂ => simpConst (plus (fuse e₁) (fuse e₂))
  | times e₁ e₂ => simpConst (times (fuse e₁) (fuse e₂))
  | e => e

theorem simpConst_eq (v : Nat → Nat)
  : ∀ e : Expr, eval v (simpConst e) = eval v e
  | const n => rfl
  | var n => rfl
  | plus (const n₁) (const n₂) => by simp[eval, simpConst]
  | plus (var _) _ => rfl
  | plus (plus _ _) _ => rfl
  | plus (times _ _) _ => rfl
  | plus (const _) (var _) => rfl
  | plus (const _) (plus _ _) => rfl
  | plus (const _) (times _ _) => rfl
  | times (const n₁) (const n₂) => by simp[eval, simpConst]
  | times (var _) _ => rfl
  | times (plus _ _) _ => rfl
  | times (times _ _) _ => rfl
  | times (const _) (var _) => rfl
  | times (const _) (plus _ _) => rfl
  | times (const _) (times _ _) => rfl

theorem fuse_eq (v : Nat → Nat)
  : ∀ e : Expr, eval v (fuse e) = eval v e
  | plus e₁ e₂ => by -- simp[simpConst, fuse, simpConst_eq, eval, fuse_eq]
      calc eval v (fuse (plus e₁ e₂))
        _ = eval v (simpConst (plus (fuse e₁) (fuse e₂))) := by simp[simpConst, fuse]
        _ = eval v (plus (fuse e₁) (fuse e₂)) := by simp[simpConst_eq]
        _ = eval v (fuse e₁) + eval v (fuse e₂) := by simp[fuse, eval]
        _ = eval v e₁ + eval v e₂ := by simp[fuse_eq]
  | times e₁ e₂ => by
      calc eval v (fuse (times e₁ e₂))
        _ = eval v (simpConst (times (fuse e₁) (fuse e₂))) := by simp[simpConst, fuse]
        _ = eval v (times (fuse e₁) (fuse e₂)) := by simp[simpConst_eq]
        _ = eval v (fuse e₁) * eval v (fuse e₂) := by simp[eval, fuse]
        _ = eval v e₁ * eval v e₂ := by simp[fuse_eq]
  | const _ => rfl
  | var _ => rfl

end ex5
