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
