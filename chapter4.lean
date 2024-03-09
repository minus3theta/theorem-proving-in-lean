example (α : Type) (p q : α → Prop) : (∀ x : α, p x /\ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x /\ q x =>
  fun y : α =>
  show p y from (h y).left

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩

def is_even (a : Nat) : Prop := ∃ b : Nat, a = 2 * b

theorem even_plus_even {a b : Nat} (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  Exists.elim h1 (fun w1 hw1 =>
  Exists.elim h2 (fun w2 hw2 =>
    Exists.intro (w1 + w2)
      (calc a + b
        _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
        _ = 2 * (w1 + w2) := by rw [Nat.mul_add])))

theorem even_plus_even3 (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  let ⟨w1, hw1⟩ := h1
  let ⟨w2, hw2⟩ := h2
  ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r :=
  fun ⟨_, hr⟩ => hr

example (a : α) : r → (∃ x : α, r) :=
  fun h => ⟨a, h⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  ⟨
    fun ⟨x, hpx, hr⟩ => ⟨⟨x, hpx⟩, hr⟩,
    fun ⟨⟨x, hpx⟩, hr⟩ => ⟨x, hpx, hr⟩,
  ⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  ⟨
    fun ⟨x, hpq⟩ => hpq.elim (fun hp => Or.inl ⟨x, hp⟩) (fun hq => Or.inr ⟨x, hq⟩),
    fun h => h.elim (fun ⟨x, hp⟩ => ⟨x, Or.inl hp⟩) (fun ⟨x, hq⟩ => ⟨x, Or.inr hq⟩)
  ⟩

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  ⟨
    fun hp ⟨x, hnp⟩ => hnp (hp x),
    fun rhs x => byContradiction
      fun hnpx => rhs ⟨x, hnpx⟩
  ⟩

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  ⟨
    fun ⟨x, hpx⟩ nrhs => nrhs x hpx,
    fun rhs => byContradiction
     fun hnpx => rhs fun x hpx => hnpx ⟨x, hpx⟩,
  ⟩

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  ⟨
    fun lhs x hpx => lhs ⟨x, hpx⟩,
    fun rhs ⟨x, hpx⟩ => rhs x hpx
  ⟩

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  ⟨
    fun lhs => byContradiction
      fun nrhs => lhs
        fun x => byContradiction
          fun hnpx => nrhs ⟨x, hnpx⟩,
    fun ⟨x, hnpx⟩ hxpx => hnpx (hxpx x)
  ⟩

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  ⟨
    fun lhs ⟨x, hpx⟩ => lhs x hpx,
    fun rhs x hpx => rhs ⟨x, hpx⟩
  ⟩

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  ⟨
    fun ⟨x, h⟩ hxpx => h (hxpx x),
    fun h => byCases
      (fun hap : ∀ x, p x => ⟨a, fun _ => h hap⟩)
      (fun hnap => byContradiction
        fun h1 => hnap fun x =>
          byContradiction fun hnpx => h1 ⟨x, fun hpx => absurd hpx hnpx⟩)
  ⟩

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  ⟨
    fun ⟨x, hrpx⟩ hr => ⟨x, hrpx hr⟩,
    fun rhs => byCases
      (fun hxpx : ∃ x, p x =>
        let ⟨x, hpx⟩ := hxpx
        ⟨x, fun _ => hpx⟩)
      fun hnxpx =>
        show _ from
        have : ¬ r := fun hr => hnxpx (rhs hr)
        have : r -> p a := fun hr => absurd hr this
        ⟨a, this⟩
  ⟩

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  ⟨
    fun lhs => ⟨fun x => (lhs x).left, fun x => (lhs x).right⟩,
    fun ⟨h1, h2⟩ x => ⟨h1 x, h2 x⟩
  ⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun hpq hp x => hpq x (hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun hpq x => hpq.elim
    (fun hp => Or.inl (hp x))
    (fun hq => Or.inr (hq x))

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  fun a => Iff.intro
    (fun h => h a)
    (fun h _ => h)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun lhs => byCases
      (fun h : ∀ x, p x => Or.inl h)
      fun hnxpx : ¬ ∀ x, p x =>
        let hr : r := byContradiction
          fun hnr => hnxpx fun x => (lhs x).elim
            id
            (fun hr => absurd hr hnr)
        Or.inr hr)
    (fun rhs x =>
      rhs.elim
        (fun hpx => Or.inl $ hpx x)
        Or.inr)

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun lhs hr x => lhs x hr)
    fun rhs x hr => rhs hr x

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  let ⟨l, r⟩ := (h barber)
  byCases
    (fun h1 : shaves barber barber => l h1 h1)
    (fun h2 => h2 $ r h2)
