section ex
open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x)
    n
    (show 0 + 0 = 0 from rfl)
    (fun (n : Nat) (ih : 0 + n = n) =>
      show 0 + succ n = succ n from
      calc 0 + succ n
        _ = succ (0 + n) := rfl
        _ = succ n := by rw [ih])

example (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x) n
    rfl
    (fun n ih => by simp [add_succ, ih])

theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    (show m + n + 0 = m + (n + 0) from rfl)
    (fun k ih =>
      show m + n + succ k = m + (n + succ k) from
      by simp[Nat.add_succ, ih])

theorem succ_add (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    rfl
    fun m ih => by simp only [add_succ, ih]

theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
    (by simp)
    fun m ih => by simp [add_succ, _root_.succ_add, ih]

namespace Hidden
inductive List (α : Type u) where
| nil  : List α
| cons : α → List α → List α
namespace List
def append (as bs : List α) : List α :=
 match as with
 | nil       => bs
 | cons a as => cons a (append as bs)
theorem nil_append (as : List α) : append nil as = as :=
 rfl
theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
 rfl

#check List.recOn

theorem append_nil (as : List α) : append as nil = as :=
  List.recOn (motive := fun as => append as nil = as) as
    rfl
    fun m as ih => by simp [cons_append, ih]

theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) :=
  List.recOn (motive := fun as => append (append as bs) cs = append as (append bs cs)) as
    (by simp [nil_append])
    fun a as ih => by simp [cons_append, ih]

end List
end Hidden

theorem zero_add_1 (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]

example (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by
  induction x, y using Nat.mod.inductionOn with
  | ind x y h₁ ih =>
    rw [Nat.mod_eq_sub_mod h₁.2]
    exact ih h
  | base x y h₁ =>
    have : ¬ 0 < y \/ ¬ y ≤ x := Iff.mp (Decidable.not_and_iff_or_not ..) h₁
    match this with
    | Or.inl h₁ => exact absurd h h₁
    | Or.inr h₁ =>
      have hgt : y > x := Nat.gt_of_not_le h₁
      rw [← Nat.mod_eq_of_lt hgt] at hgt
      assumption

theorem symm {α : Type u} {a b : α} (h : Eq a b) : Eq b a :=
  match h with
  | rfl => rfl

theorem trans {α : Type u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  match h₁ with
  | rfl => match h₂ with
    | rfl => rfl

theorem congr₁ {α β : Type u} {a b : α} (f : α → β) (h : Eq a b) : Eq (f a) (f b) :=
  match h with
  | rfl => rfl
end ex

section
namespace Hidden₁
open List

def length (as : List α) : Nat :=
  match as with
  | nil => 0
  | cons _ as => Nat.succ $ length as

def reverse (as : List α) : List α :=
  match as with
  | nil => nil
  | cons a as => reverse as ++ cons a nil

theorem length_append : length (s ++ t) = length s + length t := by
  induction s with
  | nil => simp [append_nil, length]
  | cons _ _ ih => simp [ih, length, Nat.succ_add]

theorem length_reverse : length (reverse t) = length t := by
  induction t with
  | nil => simp [length]
  | cons _ _ ih => simp [ih, length, reverse, length_append]

theorem reverse_append : reverse (s ++ t) = reverse t ++ reverse s := by
  induction s with
  | nil => simp [reverse]
  | cons head tail ih =>
    calc reverse (head :: tail ++ t)
      _ = reverse (head :: (tail ++ t)) := by simp
      _ = reverse (tail ++ t) ++ [head] := by simp [reverse]
      _ = reverse t ++ reverse tail ++ [head] := by simp [ih]
      _ = reverse t ++ (reverse tail ++ reverse [head]) := by simp [reverse, append_assoc]
      _ = reverse t ++ reverse (head :: tail) := by simp [reverse]

theorem reverse_reverse : reverse (reverse t) = t := by
  induction t with
  | nil => rfl
  | cons x t ih => simp [ih, reverse_append, reverse]
end Hidden₁
end

section
inductive Expr where
| const (n : Nat)
| var (n : Nat)
| plus (s : Expr) (t : Expr)
| times (s : Expr) (t : Expr)

namespace Expr
def eval (e : Expr) (env : Nat → Nat) : Nat :=
match e with
| const n => n
| var n => env n
| plus s t => eval s env + eval t env
| times s t => eval s env * eval t env
end Expr
end
