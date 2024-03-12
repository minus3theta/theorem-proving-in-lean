import Init.Tactics

theorem test (p q : Prop) (hp : p) (hq : q) : p /\ q /\ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

example (p q : Prop) (hp : p) (hq : q) : p /\ q /\ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp

example (p q r : Prop) : p /\ (q \/ r) ↔ (p /\ q) \/ (p /\ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim h.right
    . intro hq
      apply Or.inl
      apply And.intro
      . exact h.left
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact h.left
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact hpq.left
      . apply Or.inl
        exact hpq.right
    . intro hpr
      apply And.intro
      . exact hpr.left
      . apply Or.inr
        exact hpr.right

example : ∀ a b c : Nat, a = b -> a = c -> c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption

def f (x y z : Nat) : Nat :=
  match x, y, z with
  | 5, _, _ => y
  | _, 5, _ => y
  | _, _, 5 => y
  | _, _, _ => 1

example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w -> f x y w = 1 := by
  intros
  simp [f]
  split <;> first | contradiction | rfl

syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (h : p) : p := by
  triv

macro_rules
  | `(tactic| triv) => `(tactic| rfl)

example (x : α) : x = x := by
  triv

example (x : α) (h : p) : x = x /\ p := by
  apply And.intro <;> triv


example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat (first | assumption | apply And.intro | apply Or.inl; assumption | apply Or.inr)

section ex_chapter_3

variable (p q r : Prop)

-- ∧ と ∨ の可換性
example : p ∧ q ↔ q ∧ p := by
  constructor <;> intro ⟨_, _⟩ <;> constructor <;> assumption

example : p ∨ q ↔ q ∨ p := by
  constructor <;> intro h <;> cases h <;> (first | apply Or.inl ; assumption | apply Or.inr ; assumption)

-- ∧ と ∨ の結合性
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  all_goals intro h
  any_goals constructor
  any_goals constructor
  all_goals cases h with
  | intro a b => any_goals (repeat (first | assumption | cases a | cases b))

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor <;> intro h
  . cases h with
    | inl h₁ => cases h₁ with
      | inl _ => apply Or.inl; assumption
      | inr _ => apply Or.inr; apply Or.inl; assumption
    | inr h₂ => apply Or.inr; apply Or.inr; assumption
  . cases h with
    | inl h₁ => apply Or.inl; apply Or.inl; assumption
    | inr h₂ => cases h₂ with
      | inl _ => apply Or.inl; apply Or.inr; assumption
      | inr _ => apply Or.inr; assumption

-- 分配性
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  . intro ⟨hp, hqr⟩
    cases hqr
    . apply Or.inl; constructor <;> assumption
    . apply Or.inr; constructor <;> assumption
  . intro h
    cases h with
    | inl hpq => cases hpq ; constructor ; assumption ; apply Or.inl ; assumption
    | inr hpr => cases hpr ; constructor ; assumption ; apply Or.inr ; assumption

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  . intro h
    constructor
    . cases h with
      | inl => apply Or.inl ; assumption
      | inr hpq => apply Or.inr ; exact hpq.left
    . cases h with
      | inl => apply Or.inl ; assumption
      | inr hqr => apply Or.inr ; exact hqr.right
  . intro ⟨hpq, hpr⟩
    cases hpq
    . apply Or.inl ; assumption
    . cases hpr
      . apply Or.inl ; assumption
      . apply Or.inr ; constructor <;> assumption


-- 他の性質
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  . intro h ⟨hp, hq⟩
    apply h <;> assumption
  . intros f _ _
    apply f ; constructor <;> assumption

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  . intro h ; constructor <;> intro <;> apply h <;>
    first | apply Or.inl ; assumption | apply Or.inr ; assumption
  . intros f h
    cases f with
    | intro f₁ f₂ => cases h with
      | inl => apply f₁ ; assumption
      | inr => apply f₂ ; assumption

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  . intro lhs
    constructor <;> intro <;> apply lhs
    . apply Or.inl ; assumption
    . apply Or.inr ; assumption
  . intro ⟨hnp, hnq⟩ hpq
    cases hpq
    . apply hnp ; assumption
    . apply hnq ; assumption

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h ⟨hp, hq⟩
  cases h with
  | inl h => apply h ; assumption
  | inr h => apply h ; assumption

example : ¬(p ∧ ¬p) := by
  intro ⟨hp, hnp⟩
  apply hnp ; assumption

example : p ∧ ¬q → ¬(p → q) := by
  intro ⟨hp, hnq⟩ hpq
  apply hnq ; apply hpq ; assumption

example : ¬p → (p → q) := by
  intro hnp hp
  apply False.elim ; apply hnp ; assumption

example : (¬p ∨ q) → (p → q) := by
  intro h hp
  cases h with
  | inl hnp => apply False.elim ; apply hnp ; assumption
  | inr => assumption

example : p ∨ False ↔ p := by
  constructor
  . intro h
    cases h
    . assumption
    . contradiction
  . exact Or.inl

example : p ∧ False ↔ False := by
  constructor
  . intro ⟨_, _⟩ ; contradiction
  . intro ; contradiction

example : (p → q) → (¬q → ¬p) := by
  intro hpq hnq hp
  apply hnq ; apply hpq ; assumption

section
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h
  apply byCases
  . intro (_ : p → q)
    apply Or.inl ; assumption
  . intro hnpq
    apply Or.inr ; intro hp
    cases h hp with
    | inl hq => have := fun _: p => hq ; apply absurd this hnpq
    | inr => assumption

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro hnpq
  apply byContradiction
  intro hnnpnq
  apply hnpq
  constructor
  . apply byContradiction
    intro hnp ; apply hnnpnq ; apply Or.inl ; assumption
  . apply byContradiction
    intro hnq ; apply hnnpnq ; apply Or.inr ; assumption

example : ¬(p → q) → p ∧ ¬q := by
  intro h
  constructor
  . apply byContradiction
    intro hnp
    apply h
    intro
    contradiction
  . intro ; apply h ; intro ; assumption

example : (p → q) → (¬p ∨ q) := by
  intro h
  apply byCases
  . intro (hp: p)
    apply Or.inr ; apply h ; assumption
  . intro hnp
    apply Or.inl ; assumption

example : (¬q → ¬p) → (p → q) := by
  intro h hp
  apply byContradiction ; intro hnq ; apply absurd hp (h hnq)

example : p ∨ ¬p := by
  apply em

-- example : (((p → q) → p) → p) := by
--   intro h
--   let not_not : ∀ r, r ↔ ¬ ¬ r := fun _ => Iff.intro not_not_intro Decidable.of_not_not
--   conv at h =>
--     lhs
--     rw[not_not p]
--   sorry
-- end

example : ¬ (p ↔ ¬ p) := by
  intro ⟨h₁, h₂⟩
  have hnp : ¬ p := by
    . intro hnp
      exact h₁ hnp hnp
  exact hnp (h₂ hnp)

end
end ex_chapter_3

section ex_chapter_4

section
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor
  . intro h
    constructor
    . intro x
      exact (h x).left
    . intro x
      exact (h x).right
  . intro ⟨h₁, h₂⟩ x
    constructor
    . exact h₁ x
    . exact h₂ x

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h hp x
  apply h x
  exact hp x

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h x
  cases h with
  | inl h' => apply Or.inl ; exact h' x
  | inr h' => apply Or.inr ; exact h' x

end

section
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by
  intro a
  constructor
  . intro h ; apply h ; assumption
  . intros ; assumption

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  constructor
  . intro h
    apply Classical.byCases
    . intro (hpx : ∀ x, p x)
      apply Or.inl ; assumption
    . intro hnpx
      apply Or.inr ; apply Classical.byContradiction ; intro
      apply hnpx
      intro x
      cases h x
      . assumption
      . contradiction
  . intro h x
    cases h with
    | inl h' => apply Or.inl ; exact h' x
    | inr h' => apply Or.inr ; assumption

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  constructor
  . intro h _ x
    apply h x
    assumption
  . intro h _ _
    apply h
    assumption
end
end ex_chapter_4
