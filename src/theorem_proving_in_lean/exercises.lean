import data.nat.basic
import data.nat.pow
import data.int.basic
import data.real.basic
import data.list


-- ### Exercise 2

namespace exercise_2

-- Functions
def double : ℕ → ℕ := λ x, x + x
def square : ℕ → ℕ := λ x, x * x
def do_twice : (ℕ → ℕ) → (ℕ → ℕ) := λ f x, f (f x)
def Do_Twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) := λ f g, (f (f g))
#reduce Do_Twice do_twice double 2

def curry {α β γ : Type*} (f : α × β → γ) : α → β → γ := λ a b, f (a, b)
def uncurry {α β γ : Type*} (f : α → β → γ) : α × β → γ := λ ⟨a, b⟩, f a b

-- "Vector" type former & related dependent functions
universe u
constant vec : Type u → ℕ → Type u

namespace vec
  constant empty : Π (α : Type u), vec α 0
  constant cons : Π {α : Type u} {n : ℕ}, α → vec α n → vec α (n + 1)
  constant append : Π {α : Type u} {n m : ℕ}, vec α m → vec α n → vec α (n + m)
  constant add : Π {α : Type u} {n : ℕ}, vec α n → vec α n → vec α n
  constant reverse : Π {α : Type u} {n : ℕ}, vec α n → vec α n
end vec

#check vec.empty ℕ
noncomputable def v0 := vec.empty ℕ -- TODO: what is `noncomputable`?
#check v0
noncomputable def v1 := vec.cons 0 v0
#check v1
variable v3 : vec ℕ 3
#check vec.add v3 v3
#check vec.reverse v3

-- "Matrix" type former & related dependent functions
constant matrix : Type u → ℕ → ℕ → Type u

namespace matrix
  constant add : Π {α : Type u} {n m : ℕ}, matrix α m n → matrix α m n → matrix α m n
  constant mul : Π {α : Type u} {n m k : ℕ}, matrix α m k → matrix α k n → matrix α m n
  constant mulvec : Π {α : Type u} {n m : ℕ}, matrix α m n → vec α n → vec α m
end matrix

#check matrix ℕ 5 3
variable m : matrix ℕ 5 3
variable m' : matrix ℕ 3 2
#check matrix.mulvec m v3
#check matrix.mul m m'

end exercise_2


-- ### Exercise 3

namespace exercise_3_1

variables p q r : Prop

-- Commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  iff.intro
    (λ ⟨hp, hq⟩, ⟨hq, hp⟩)
    (λ ⟨hq, hp⟩, ⟨hp, hq⟩)
example : p ∨ q ↔ q ∨ p :=
  iff.intro
    (λ h, or.elim h (λ hp, or.inr hp) (λ hq, or.inl hq))
    (λ h, or.elim h (λ hq, or.inr hq) (λ hp, or.inl hp))

-- Associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  iff.intro
    (λ ⟨⟨hp, hq⟩, hr⟩, ⟨hp, ⟨hq, hr⟩⟩)
    (λ ⟨hp, ⟨hq, hr⟩⟩, ⟨⟨hp, hq⟩, hr⟩)
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  iff.intro
    (λ h, h.elim
      (λ hpq, hpq.elim or.inl (or.inr ∘ or.inl))
      (or.inr ∘ or.inr))
    (λ h, h.elim
      (or.inl ∘ or.inl)
      (λ hqr, hqr.elim (or.inl ∘ or.inr) or.inr))

-- Distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  iff.intro
    (λ ⟨hp, hqr⟩, hqr.elim (λ hq, or.inl ⟨hp, hq⟩) (λ hr, or.inr ⟨hp, hr⟩))
    (λ h, h.elim (λ ⟨hp, hq⟩, ⟨hp, or.inl hq⟩) (λ ⟨hp, hr⟩, ⟨hp, or.inr hr⟩))
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  iff.intro
    (λ h, h.elim (λ hp, ⟨or.inl hp, or.inl hp⟩) (λ ⟨hq, hr⟩, ⟨or.inr hq, or.inr hr⟩))
    (λ ⟨hpq, hpr⟩, hpq.elim or.inl (λ hq, hpr.elim or.inl (λ hr, or.inr ⟨hq, hr⟩)))

-- Other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  iff.intro
    (λ f ⟨hp, hq⟩, f hp hq)
    (λ f hp hq, f ⟨hp, hq⟩)
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  iff.intro
    (λ h, ⟨h ∘ or.inl, h ∘ or.inr⟩)
    (λ ⟨hpr, hqr⟩ hpq, hpq.elim hpr hqr)
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
  iff.intro
    (λ h, ⟨h ∘ or.inl, h ∘ or.inr⟩)
    (λ ⟨hnp, hnq⟩, (λ h, h.elim hnp hnq))
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  (λ h ⟨hp, hq⟩, h.elim (λ hnp, hnp hp) (λ hnq, hnq hq))
example : ¬(p ∧ ¬p) := (λ ⟨hp, hnp⟩, hnp hp)
example : p ∧ ¬q → ¬(p → q) := (λ ⟨hp, hnq⟩ hpq, hnq (hpq hp))
example : ¬p → (p → q) := (λ hnp hp, (hnp hp).elim)
example : (¬p ∨ q) → (p → q) := (λ h, h.elim (λ hnp hp, (hnp hp).elim) (λ hq _, hq))
example : p ∨ false ↔ p := iff.intro (λ h, h.elim id false.elim) or.inl
example : p ∧ false ↔ false := iff.intro and.right false.elim
example : (p → q) → (¬q → ¬p) := (λ hpq hnq hp, hnq (hpq hp))

end exercise_3_1
namespace exercise_3_2


variables p q r s : Prop

-- These require classical reasoning.
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
  (λ h, (em p).elim
    (λ hp, (h hp).elim (λ hr, or.inl (λ _, hr)) (λ hs, or.inr (λ _, hs)))
    (λ hnp, or.inl (λ hp, (hnp hp).elim)))
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  (λ h, (em p).elim
    (λ hp, or.inr (λ hq, h ⟨hp, hq⟩))
    or.inl)
example : ¬(p → q) → p ∧ ¬q :=
  (λ h, and.intro
    ((em q).elim
      (λ hq, (h (λ _, hq)).elim)
      (λ hnq, (em p).elim id (λ hnp, (h (λ hp, (hnp hp).elim)).elim)))
    (λ hq, h (λ _, hq)))
example : (p → q) → (¬p ∨ q) :=
  (λ hpq, (em p).elim (or.inr ∘ hpq) or.inl)
example : (¬q → ¬p) → (p → q) :=
  (λ h, (em q).elim (λ hq _, hq) (λ hnq hp, (h hnq hp).elim))
example : p ∨ ¬p := em p
example : (((p → q) → p) → p) :=
  (em p).elim
    (λ hp _, hp)
    (λ hnp, (em q).elim
      (λ hq h, h (λ _, hq))
      (λ hnq h, h (λ hp, (hnp hp).elim)))

-- Prove ¬(p ↔ ¬p) without using classical logic.
example : ¬(p ↔ ¬p) :=
  (λ ⟨h₁, h₂⟩,
    (λ hp, h₁ hp hp) -- "Don't eliminate cuts!" (will make the proof longer)
      (h₂ (λ hp, h₁ hp hp)))

end exercise_3_2


-- ### Exercise 4

namespace exercise_4

section
  variables (α : Type*) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    iff.intro
      (λ h, ⟨(λ x, (h x).left), (λ x, (h x).right)⟩)
      (λ ⟨h₁, h₂⟩ x, ⟨h₁ x, h₂ x⟩)
  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
    λ h₁ h₂ x, h₁ x (h₂ x)
  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
    λ h x, h.elim (λ h₁, or.inl (h₁ x)) (λ h₁, or.inr (h₁ x))
end

section
  variables (α : Type*) (p q : α → Prop)
  variable r : Prop

  -- One direction of the second of these requires classical logic
  example : α → ((∀ x : α, r) ↔ r) :=
    λ x, (iff.intro (λ h, h x) (λ h _, h))
  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
    iff.intro
      (λ h, (classical.em r).elim (or.inr) (λ hnr, or.inl (λ x, (h x).elim id (λ hr, (hnr hr).elim))))
      (λ h, h.elim (λ h₁ x, or.inl (h₁ x)) (λ h₂ x, or.inr h₂))
  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
    iff.intro
      (λ h hr x, h x hr)
      (λ h x hr, h hr x)
end

section
  variables (men : Type*) (barber : men)
  variable  (shaves : men → men → Prop)

  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
    (h barber).elim
      (λ (h₁ : shaves barber barber → ¬shaves barber barber) h₂,
        (λ hs, h₁ hs hs) (h₂ (λ hs, h₁ hs hs)))
end

-- See: https://discord.com/channels/679792285910827018/707609591940382830/733322519112712362
section
  def prime (n : ℕ) : Prop :=
    ∀ (x : ℕ), (∃ y, n = x * y) → x = 1 ∨ x = n

  def infinitely_many_primes : Prop :=
    ∀ (x : ℕ), prime x → (∃ y, prime y ∧ x < y)

  def Fermat_prime (n : ℕ) : Prop :=
    prime n ∧ ∃ (x : ℕ), n = 2 ^ (2 ^ x) + 1

  def infinitely_many_Fermat_primes : Prop :=
    ∀ (x : ℕ), Fermat_prime x → (∃ y, Fermat_prime y ∧ x < y)

  def goldbach_conjecture : Prop :=
    ∀ (n : ℕ), even n → (2 < n) → (∃ p₁ p₂, prime p₁ ∧ prime p₂ ∧ n = p₁ + p₂)

  def Goldbach's_weak_conjecture : Prop :=
    ∀ (n : ℕ), odd n → (5 < n) → (∃ p₁ p₂ p₃, prime p₁ ∧ prime p₂ ∧ prime p₃ ∧ n = p₁ + p₂ + p₃)

  def Fermat's_last_theorem : Prop :=
    ∀ (n : ℕ), (2 < n) → ∀ (a b c : ℕ), 0 < a → 0 < b → a ^ n + b ^ n ≠ c ^ n
end

section
  variables (α : Type*) (p q : α → Prop)
  variable r : Prop

  example : (∃ x : α, r) → r :=
    λ ⟨x, hx⟩, hx
  example (a : α) : r → (∃ x : α, r) :=
    λ h, ⟨a, h⟩
  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
    iff.intro
      (λ ⟨x, hx, hr⟩, ⟨⟨x, hx⟩, hr⟩)
      (λ ⟨⟨x, hx⟩, hr⟩, ⟨x, ⟨hx, hr⟩⟩)
  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    iff.intro
      (λ ⟨x, hx⟩, hx.elim (λ hpx, or.inl ⟨x, hpx⟩) (λ hqx, or.inr ⟨x, hqx⟩))
      (λ h, h.elim (λ ⟨x, hx⟩, ⟨x, or.inl hx⟩) (λ ⟨x, hx⟩, ⟨x, or.inr hx⟩))

  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
    iff.intro
      (λ h ⟨x, hx⟩, hx (h x))
      (λ h x, by_contra (λ hx, h ⟨x, hx⟩))
  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
    iff.intro
      (λ ⟨x, hx⟩ h, h x hx)
      (λ h, by_contra (λ h₁, h (λ x hx, h₁ ⟨x, hx⟩)))
  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
    iff.intro
      (λ h x hx, h ⟨x, hx⟩)
      (λ h ⟨x, hx⟩, h x hx)
  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
    iff.intro
      (λ h, by_contra (λ h₁, h (λ x, by_contra (λ hx, h₁ ⟨x, hx⟩))))
      (λ ⟨x, hx⟩ h, hx (h x))

  example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
    iff.intro
      (λ h ⟨x, hx⟩, h x hx)
      (λ h x hx, h ⟨x, hx⟩)
  example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
    iff.intro
      (λ ⟨x, hx⟩ h, hx (h x))
      (λ h, (em (∀ x, p x)).elim
        (λ h₁, ⟨a, λ _, h h₁⟩)
        (λ h₁,
          have h₂ : (∃ (x : α), ¬(p x)),
          from by_contra
            (λ h₂, h₁ (λ x, by_contra
              (λ h₃, h₂ ⟨x, h₃⟩))),
          let ⟨w, hw⟩ := h₂ in
            ⟨w, (λ hw₁, (hw hw₁).elim)⟩))
  example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
    iff.intro
      (λ ⟨x, hx⟩ h, ⟨x, hx h⟩)
      (λ h, (em r).elim
        (λ hr, exists.elim (h hr) (λ a ha, ⟨a, (λ _, ha)⟩))
        (λ hnr, ⟨a, (λ hr, (hnr hr).elim)⟩))
end

section
  variables log exp    : ℝ → ℝ
  variable  log_exp_eq : ∀ x, log (exp x) = x
  variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
  variable  exp_pos    : ∀ x, exp x > 0
  variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

  -- this ensures the assumptions are available in tactic proofs
  include log_exp_eq exp_log_eq exp_pos exp_add

  example (x y z : ℝ) : exp (x + y + z) = exp x * exp y * exp z :=
  by rw [exp_add, exp_add]

  example (y : real) (h : y > 0) : exp (log y) = y :=
    exp_log_eq h

  theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
    log (x * y) = log x + log y :=
  by calc log (x * y)
        = log (exp (log x) * exp (log y)) : by rw [exp_log_eq hx, exp_log_eq hy]
    ... = log (exp (log x + log y)) : by rw exp_add
    ... = log x + log y : by rw log_exp_eq
end

section
  example (x : ℤ) : x * 0 = 0 :=
  by calc x * 0
        = x * 0 + x * 0 + -(x * 0) : by rw [add_assoc, add_neg_self, add_zero]
    ... = x * (0 * 1 + 0 * 1) + -(x * 0) : by rw [mul_one, mul_add]
    ... = x * 0 + -(x * 0) : by rw [mul_one, add_zero]
    ... = 0 : by rw add_neg_self
end

end exercise_4


-- ### Exercise 5

namespace exercise_5_1

variables p q r : Prop

-- Commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
begin
  split,
  { intros h, exact let ⟨hp, hq⟩ := h in ⟨hq, hp⟩, },
  { intros h, exact let ⟨hq, hp⟩ := h in ⟨hp, hq⟩, },
end
example : p ∨ q ↔ q ∨ p :=
begin
  apply iff.intro,
  { exact (λ h, h.elim or.inr or.inl), },
  { exact (λ h, h.elim or.inr or.inl), },
end

-- Associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by {
  split,
  { rintros ⟨⟨hp, hq⟩, hr⟩, exact ⟨hp, hq, hr⟩, },
  { rintros ⟨hp, hq, hr⟩, exact ⟨⟨hp, hq⟩, hr⟩, },
}
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by {
  split,
  { assume h,
      cases h, cases h,
        exacts [or.inl h, or.inr (or.inl h), or.inr (or.inr h)], },
  { assume h,
      cases h, swap, cases h,
        exacts [or.inl (or.inr h), or.inr h, or.inl (or.inl h)], },
}

-- Distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by {
  split,
  { rintros ⟨hp, hq | hr⟩,
      left, exact ⟨hp, hq⟩,
      right, exact ⟨hp, hr⟩, },
  { rintros (⟨hp, hq⟩ | ⟨hp, hr⟩),
      exact ⟨hp, or.inl hq⟩,
      exact ⟨hp, or.inr hr⟩, },
}
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by {
  split,
  { rintros (hp | ⟨hq, hr⟩),
      exacts [⟨or.inl hp, or.inl hp⟩, ⟨or.inr hq, or.inr hr⟩], },
  { rintros ⟨hp | hq, hp | hr⟩,
      exacts [or.inl hp, or.inl hp, or.inl hp, or.inr ⟨hq, hr⟩], },
}

-- Other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by {
  split,
  { rintros f ⟨hp, hq⟩, exact f hp hq, },
  { rintros f hp hq, exact f ⟨hp, hq⟩, },
}
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by {
  split,
  { intros f, split, exacts [f ∘ or.inl, f ∘ or.inr], },
  { rintros ⟨f, g⟩ (hp | hq), exacts [f hp, g hq], },
}
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by sorry -- More examples to experiment on later
example : ¬p ∨ ¬q → ¬(p ∧ q) := by sorry
example : ¬(p ∧ ¬p) := by sorry
example : p ∧ ¬q → ¬(p → q) := by sorry
example : ¬p → (p → q) := by sorry
example : (¬p ∨ q) → (p → q) := by sorry
example : p ∨ false ↔ p := by sorry
example : p ∧ false ↔ false := by sorry
example : (p → q) → (¬q → ¬p) := by sorry

end exercise_5_1
namespace exercise_5_2


variables p q r s : Prop

-- These require classical reasoning.
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := by sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := by sorry
example : ¬(p → q) → p ∧ ¬q := by sorry
example : (p → q) → (¬p ∨ q) := by sorry
example : (¬q → ¬p) → (p → q) := by sorry
example : p ∨ ¬p := by sorry
example : (((p → q) → p) → p) := by sorry

-- Prove ¬(p ↔ ¬p) without using classical logic.
example : ¬(p ↔ ¬p) := by {
  rintros ⟨h₁, h₂⟩,
  apply h₁,
  { apply h₂, intros hp, exact h₁ hp hp, },
  { apply h₂, intros hp, exact h₁ hp hp, },
}

end exercise_5_2
namespace exercise_5_3

section
  variables (α : Type*) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by sorry -- More examples to experiment on later
  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by sorry
  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by sorry
end

section
  variables (α : Type*) (p q : α → Prop)
  variable r : Prop

  -- One direction of the second of these requires classical logic
  example : α → ((∀ x : α, r) ↔ r) := by sorry
  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by sorry
  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by sorry
end

section
  variables (α : Type*) (p q : α → Prop)
  variable r : Prop

  example : (∃ x : α, r) → r := by sorry
  example (a : α) : r → (∃ x : α, r) := by sorry
  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by sorry
  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by sorry

  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by sorry
  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by sorry
  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by sorry
  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by sorry

  example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by sorry
  example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by sorry
  example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by sorry
end

end exercise_5_3

/-
Note:
  `tauto` (and `tauto!` for classical) seems to use sequent calculus (elim then intro);
  `finish` seems to use SMT? (TODO: what is SMT...)
  Both are complete for propositional logic...?
-/


-- ### Exercise 7

namespace exercise_7

inductive myempty : Type

inductive myunit : Type
| star : myunit

inductive mybool : Type
| ff : mybool
| tt : mybool

namespace mybool

  def bnot : mybool → mybool :=
    @mybool.rec (λ _, mybool) tt ff
  
  def band : mybool → mybool → mybool :=
    λ a b, @mybool.rec (λ _, mybool) ff b a
  
  def bor : mybool → mybool → mybool :=
    λ a b, @mybool.rec (λ _, mybool) b tt a

end mybool

universe u

-- Standard definition for equality
inductive myeq {α : Sort u} (l : α) : α → Prop
| refl [] : myeq l

namespace myeq

  lemma symm : Π {α : Sort u} {x y : α} (h : myeq x y), myeq y x :=
    λ α x y h, @myeq.rec α x -- The subject is `myeq {α} x`
      (λ r, myeq r x) -- Make a more general claim: given `myeq x r` then `myeq r x`
      (myeq.refl x)   -- Now given `myeq x x` (implicit), prove `myeq x x`
        y h           -- Then we could specialise `r` to `y`, and give a `myeq x y` to make `myeq y x`
  
  lemma trans : Π {α : Sort u} {x y z : α} (h₁ : myeq x y) (h₂ : myeq y z), myeq x z :=
    λ α x y z h₁ h₂, @myeq.rec α y -- The subject is `myeq {α} y`
      (λ r, myeq x r) -- Make a more general claim: given `myeq y r` then `myeq x r`
      h₁              -- Now given `myeq y y` (implicit), prove `myeq x y`
        z h₂          -- Then we could specialise `r` to `z`, and give a `myeq y z` to make `myeq x z`
  
  lemma congr : Π {α β : Sort u} {x y : α} (f : α → β) (h : myeq x y), myeq (f x) (f y) :=
    λ α β x y f h, @myeq.rec α x
      (λ r, myeq (f x) (f r))
      (myeq.refl (f x))
        y h
  
  lemma subst : Π {α : Sort u} {x y : α} (p : α → Prop) (h₁ : myeq x y) (h₂ : p x), p y :=
    λ α x y p h₁ h₂, @myeq.rec α x
      (λ r, p r)
      h₂
        y h₁
  
  -- Simplify by removing `@` and abbreviating arguments
  lemma symm' {α : Sort u} {x y : α} (h : myeq x y) : myeq y x :=
    myeq.rec (myeq.refl x) h
  lemma trans' {α : Sort u} {x y z : α} (h₁ : myeq x y) (h₂ : myeq y z) : myeq x z :=
    myeq.rec h₁ h₂
  lemma congr' {α β : Sort u} {x y : α} (f : α → β) (h : myeq x y) : myeq (f x) (f y) :=
    myeq.rec (myeq.refl (f x)) h
  lemma subst' {α : Sort u} {x y : α} (p : α → Prop) (h₁ : myeq x y) (h₂ : p x) : p y :=
    myeq.rec h₂ h₁

end myeq

namespace mybool

  lemma em : Π (a : mybool), myeq (bor a (bnot a)) tt :=
    @mybool.rec
      (λ x, myeq (bor x (bnot x)) tt)
      (myeq.refl tt) -- Lean refers to definitions and does the calculation automatically
      (myeq.refl tt) -- So `myeq (bor tt (bnot tt)) tt` unifies with `myeq tt tt`!
  
  lemma de_morgan : Π (a b : mybool), myeq (bnot (band a b)) (bor (bnot a) (bnot b)) :=
    λ a b, @mybool.rec -- By cases on `a`
      (λ a', myeq (bnot (band a' b)) (bor (bnot a') (bnot b)))
      (@mybool.rec     -- By cases on `b`
        (λ b', myeq (bnot (band ff b')) (bor (bnot ff) (bnot b')))
        (myeq.refl tt)
        (myeq.refl tt)
          b)
      (@mybool.rec     -- By cases on `b`
        (λ b', myeq (bnot (band tt b')) (bor (bnot tt) (bnot b')))
        (myeq.refl tt)
        (myeq.refl ff)
          b)
        a
  
  -- Simplify by removing `@` and abbreviating arguments
  lemma de_morgan' (a b : mybool) : myeq (bnot (band a b)) (bor (bnot a) (bnot b)) :=
    mybool.rec_on b
      (mybool.rec_on a (myeq.refl _) (myeq.refl _))
      (mybool.rec_on a (myeq.refl _) (myeq.refl _))

end mybool

inductive maybe (α : Type u) : Type u
| nothing :     maybe
| just    : α → maybe

inductive inhabited (α : Type u) : Type u
| mk : α → inhabited

namespace maybe

  -- The "monad operation"
  def bind : Π {α β : Type u}, maybe α → (α → maybe β) → maybe β :=
    λ α β ma f, @maybe.rec α
      (λ _, maybe β)
      (nothing)
      (λ a, f a)
        ma
  
  -- Partial function composition
  def compose : Π {α β γ : Type u}, (β → maybe γ) → (α → maybe β) → α → maybe γ :=
    λ α β γ g f a, @maybe.rec β
      (λ _, maybe γ)
      (nothing)
      (λ b, g b)
        (f a)
  
  -- Simplified versions
  def bind' {α β : Type u} (ma : maybe α) (f : α → maybe β) : maybe β :=
    maybe.rec nothing f ma
  def compose' {α β γ : Type u} (g : β → maybe γ) (f : α → maybe β) (a : α) : maybe γ :=
    maybe.rec nothing g (f a)
  def compose'' {α β γ : Type u} (g : β → maybe γ) (f : α → maybe β) (a : α) : maybe γ :=
    bind' (f a) g

end maybe

section
  def is_even (x : ℕ) : bool := nat.rec_on x tt (λ _, @bool.rec (λ _, bool) bool.tt bool.ff)
  def filter (x : ℕ) : maybe ℕ := bool.cases_on (is_even x) (maybe.just x.succ) maybe.nothing
  #reduce filter 3
  #reduce (maybe.compose'' filter filter) 3
end

section
  #check inhabited      -- The type former
  #check @inhabited.mk  -- The constructor

  def inhabited_bool : inhabited bool := inhabited.mk tt
  def inhabited_nat  : inhabited nat  := inhabited.mk 0

  def inhabited_prod_of_inhabited : Π {α β : Type u}
    (i₁ : inhabited α) (i₂ : inhabited β),
    inhabited (prod α β) :=
      λ α β i₁ i₂, inhabited.mk (inhabited.rec id i₁, inhabited.rec id i₂)
  
  def inhabited_of_function_to_inhabited : Π {α β : Type u}
    (i : inhabited β),
    inhabited (α → β) :=
      λ α β i, inhabited.mk (λ _, inhabited.rec id i)
   
  def inhabited_of_function_to_inhabited' : Π {α : Type u} {τ : α → Type u}
    (i : Π (a : α), inhabited (τ a)),
    inhabited (Π (a : α), τ a) :=
      λ α τ i, inhabited.mk (λ a, inhabited.rec id (i a))
end

inductive mylist (α : Type u) : Type u
| nil  :              mylist
| cons : α → mylist → mylist

namespace mylist
  variable {α : Type u}

  def append (s t : mylist α) : mylist α :=
    mylist.rec_on s t (λ a _, λ st', cons a st')

  local notation h :: t := cons h t -- ?
  local notation s ++ t := append s t -- ?
  local notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l -- ?????

  section
    open nat
    #check [1, 2, 3, 4, 5]
    #check ([1, 2, 3, 4, 5] : mylist int)
  end

  theorem nil_append (t : mylist α) : nil ++ t = t := eq.refl t
  theorem cons_append (x : α) (s t : mylist α) : x::s ++ t = x::(s ++ t) := eq.refl _

  -- Manual equational rewriting!
  theorem append_nil (t : mylist α) : t ++ nil = t :=
    @mylist.rec_on α
      (λ l, l ++ nil = l) t
      (eq.refl nil)
      (λ a as, λ ih, (@eq.subst _ (λ x, a::as ++ nil = a::x) _ _ ih (eq.refl _)))
  
  -- Tip: have a notepad open, keep track of the current "state"...
  theorem append_assoc (r s t : mylist α) : r ++ s ++ t = r ++ (s ++ t) :=
    @mylist.rec_on α
      (λ l, (l ++ s) ++ t = l ++ (s ++ t)) r
      (eq.refl (s ++ t))
      (λ a as, λ ih,
        (@eq.subst _ (λ x, (a::as ++ s) ++ t = a::x) _ _ ih
          (@eq.subst _ (λ x, (a::as ++ s) ++ t = x) _ _ (cons_append a (as ++ s) t)
            (@eq.subst _ (λ x, (a::as ++ s) ++ t = x ++ t) _ _ (cons_append a as s)
              (eq.refl ((a::as ++ s) ++ t)))))) -- Read bottom up
  
  -- Simplify by ignoring steps that can be completed by `rfl` (`eq.refl _`)
  theorem append_assoc' (r s t : mylist α) : r ++ s ++ t = r ++ (s ++ t) :=
    @mylist.rec_on α
      (λ l, (l ++ s) ++ t = l ++ (s ++ t)) r
      rfl
      (λ a as, λ ih, (@eq.subst _ (λ x, (a::as ++ s) ++ t = a::x) _ _ ih rfl))

end mylist

inductive mynat : Type
| zero :                mynat
| succ : Π (n : mynat), mynat

namespace mynat
  def one   : mynat := zero.succ
  def two   : mynat := zero.succ.succ
  def three : mynat := zero.succ.succ.succ

  -- `mynat.rec` is primitive recursion!

  def add : mynat → mynat → mynat :=
    λ a, @mynat.rec
      (λ r, mynat)
      a
      (λ r, λ ar, succ ar)

  #reduce add one two

  def mul : mynat → mynat → mynat :=
    λ a, @mynat.rec
      (λ r, mynat)
      zero
      (λ r, λ ar, add ar a)

  #reduce mul two three
  #reduce mul three two

  def pred : mynat → mynat :=
    @mynat.rec
      (λ r, mynat)
      zero
      (λ r, λ predr, r)

  #reduce pred zero
  #reduce pred one
  #reduce pred two
  #reduce pred three

  def monus : mynat → mynat → mynat :=
    λ a, @mynat.rec
      (λ r, mynat)
      a
      (λ r, λ ar, pred ar)

  #reduce monus three two
  #reduce monus two three

  def pow : mynat → mynat → mynat :=
    λ a, @mynat.rec
      (λ _, mynat)
      one
      (λ r, λ ar, mul ar a)

  #reduce pow two three
  #reduce pow three two

  lemma add_zero : Π (a : mynat), add a zero = a :=
    λ a, rfl

  lemma add_succ : Π (a b : mynat), add a (succ b) = succ (add a b) :=
    λ a b, rfl

  -- More manual equational rewriting...
  lemma succ_add : Π (a b : mynat), add (succ a) b = succ (add a b) :=
    λ a b, @mynat.rec_on
      (λ n, add (succ a) n = succ (add a n)) b
      rfl
      (λ n, λ ih,
        (@eq.subst _ (λ x, add (succ a) (succ n) = succ x) _ _ ih
          (eq.refl (add (succ a) (succ n)))))

  lemma zero_add : Π (a : mynat), add zero a = a :=
    λ a, @mynat.rec_on
      (λ n, add zero n = n) a
      rfl
      (λ n, λ ih,
        (@eq.subst _ (λ x, succ (add zero n) = succ x) _ _ ih
          (eq.refl (succ (add zero n)))))

  lemma add_comm : Π (a b : mynat), add a b = add b a :=
    λ a b, @mynat.rec_on
      (λ n, add a n = add n a) b
      (eq.symm (zero_add a))
      (λ n, λ ih,
        (@eq.subst _ (λ x, succ (add a n) = x) _ _ (eq.symm (succ_add n a))
          (@eq.subst _ (λ x, succ (add a n) = succ x) _ _ ih
            (eq.refl (succ (add a n))))))

  -- See: https://leanprover.zulipchat.com/#narrow/streams/public/search/stupid.20triangle
  #print notation ▸

  -- `rw` is incredible...!
  lemma add_comm' : Π (a b : mynat), add a b = add b a :=
  begin
    intros a b,
    induction b with b ih,
    { rw zero_add, refl, },
    { rw [succ_add, ← ih], refl, },
  end

  -- This will lead to the Natural Number Game...
  -- https://github.com/ImperialCollegeLondon/natural_number_game/
  
  -- Also see: Part 7 of *Logic and Structures* (van Dalen)
end mynat

namespace mylist
  variable {α : Type u}

  local notation h :: t := cons h t -- ?
  local notation s ++ t := append s t -- ?
  local notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l -- ?????
  
  def length : mylist α → ℕ :=
    λ l, mylist.rec 0 (λ _ _, λ (l' : ℕ), l'.succ) l
  
  def reverse : mylist α → mylist α :=
    λ l, mylist.rec nil (λ a l, λ l', l' ++ (cons a nil)) l
  
  #reduce length [1, 2, 3, 4, 5]
  #reduce reverse [1, 2, 3, 4, 5]

  -- Even more manual equational rewriting...
  -- (TODO: make clear about Lean's heuristics for second-order unification?)
  lemma length_append : Π (s t : mylist α), length (s ++ t) = length s + length t :=
    λ s t, @mylist.rec_on α
      (λ l, length (l ++ t) = length l + length t) s
      (eq.symm (nat.zero_add t.length))
      (λ a l, λ ih,
        (@eq.subst _ (λ x, length (a::l ++ t) = x) _ _ (eq.symm (nat.succ_add (length l) (length t)))
          (@eq.subst _ (λ x, length (a::l ++ t) = nat.succ x) _ _ ih
            (@eq.subst _ (λ x, length (a::l ++ t) = length x) _ _ (cons_append a l t)
              (eq.refl (a::l ++ t).length)))))

  lemma length_reverse : Π (t : mylist α), length (reverse t) = length t :=
    λ t, @mylist.rec_on α
      (λ l, length (reverse l) = length l) t
      rfl
      (λ a l, λ ih,
        (@eq.subst _ (λ x, x = (a::l).length) _ _ (eq.symm (length_append l.reverse [a]))
          (@eq.subst _ (λ x, nat.succ x = (a::l).length) _ _ (eq.symm ih)
            (eq.refl (a::l).length))))

  lemma append_reverse_eq_reverse_append : Π (s t : mylist α), reverse (s ++ t) = reverse t ++ reverse s :=
    λ s t, @mylist.rec_on α
      (λ x, reverse (x ++ t) = reverse t ++ reverse x) s
      (@eq.subst _ (λ x, reverse t = x) _ _ (eq.symm (append_nil t.reverse)) (eq.refl t.reverse))
      (λ a l, λ ih,
        (@eq.subst _ (λ x, reverse (a::l ++ t) = x) _ _ (append_assoc t.reverse l.reverse [a])
          (@eq.subst _ (λ x, reverse (a::l ++ t) = x ++ [a]) _ _ ih
            (@eq.subst _ (λ x, reverse (a::l ++ t) = reverse x) _ _ (cons_append a l t)
              (eq.refl (a::l ++ t).reverse)))))

  lemma reverse_reverse_eq_self : Π (t : mylist α), reverse (reverse t) = t :=
    λ t, @mylist.rec_on α
      (λ x, reverse (reverse x) = x) t
      rfl
      (λ a l, λ ih,
        (@eq.subst _ (λ x, (a::l).reverse.reverse = [a] ++ x) _ _ ih
          (@eq.subst _ (λ x, (a::l).reverse.reverse = x) _ _ (append_reverse_eq_reverse_append l.reverse [a])
            (eq.refl (a::l).reverse.reverse))))

end mylist

inductive arith_expr : Type
| const : ℕ →                       arith_expr
| var   : ℕ →                       arith_expr
| plus  : arith_expr → arith_expr → arith_expr
| times : arith_expr → arith_expr → arith_expr

namespace arith_expr
  #check const 2
  #check var 5
  #check plus (const 2) (var 0)

  def eval : (ℕ → ℕ) → arith_expr → ℕ :=
    λ as e, @arith_expr.rec_on (λ _, ℕ) e
      id
      as
      (λ e1 e2, λ v1 v2, v1 + v2)
      (λ e1 e2, λ v1 v2, v1 * v2)

  #reduce eval id (plus (const 2) (var 0))

end arith_expr

inductive boolean_expr : Type
| const : bool →                        boolean_expr
| var   : ℕ →                           boolean_expr
| not   : boolean_expr →                boolean_expr
| and   : boolean_expr → boolean_expr → boolean_expr
| or    : boolean_expr → boolean_expr → boolean_expr

namespace boolean_expr
  #check const tt
  #check var 5
  #check and (const ff) (var 0)

  def eval : (ℕ → bool) → boolean_expr → bool :=
    λ as e, @boolean_expr.rec_on (λ _, bool) e
      id
      as
      (λ e', λ v', bnot v')
      (λ e1 e2, λ v1 v2, band v1 v2)
      (λ e1 e2, λ v1 v2, bor v1 v2)

  def size : boolean_expr → ℕ :=
    λ e, @boolean_expr.rec_on (λ _, ℕ) e
      (λ _, 1)
      (λ _, 1)
      (λ e', λ ne', ne' + 1)
      (λ e1 e2, λ ne1 ne2, ne1 + ne2 + 1)
      (λ e1 e2, λ ne1 ne2, ne1 + ne2 + 1)

  def depth : boolean_expr → ℕ :=
    λ e, @boolean_expr.rec_on (λ _, ℕ) e
      (λ _, 1)
      (λ _, 1)
      (λ e', λ ne', ne' + 1)
      (λ e1 e2, λ ne1 ne2, max ne1 ne2 + 1)
      (λ e1 e2, λ ne1 ne2, max ne1 ne2 + 1)
  
  #reduce size  (and (or (const tt) (not (var 0))) (not (var 2)))
  #reduce depth (and (or (const tt) (not (var 0))) (not (var 2)))

  def replace_all : boolean_expr → ℕ → boolean_expr → boolean_expr :=
    λ sub ind e, @boolean_expr.rec_on (λ _, boolean_expr) e
      (λ b, const b)
      (λ v, ite (v = ind) sub (var v))
      (λ _, λ e', not e')
      (λ _ _, λ e1' e2', and e1' e2')
      (λ _ _, λ e1' e2', or e1' e2')

  #reduce replace_all
    (const ff)
    2
    (and (or (const tt) (not (var 0))) (not (var 2)))

end boolean_expr

inductive even_odd : bool → ℕ → Prop
| even_zero :                            even_odd ff 0
| even_succ : Π {n : ℕ}, even_odd ff n → even_odd tt n.succ
| odd_succ  : Π {n : ℕ}, even_odd tt n → even_odd ff n.succ

namespace even_odd
  #check even_zero
  #check even_succ even_zero
  -- Does not typecheck
  -- #check even_succ (even_succ even_zero)
  -- Typechecks
  #check odd_succ (even_succ even_zero)
  #check (even_succ ∘ odd_succ ∘ even_succ ∘ odd_succ ∘ even_succ) even_zero
end even_odd

end exercise_7


-- ### Exercise 8

namespace exercise_8

section
  open function
  #print surjective

  universes u v w
  variables {α : Type u} {β : Type v} {γ : Type w}
  open function

  lemma surjective_comp {g : β → γ} {f : α → β}
    (hg : surjective g) (hf : surjective f) : surjective (g ∘ f) :=
    λ c,
      match hg c with (Exists.intro b hb) :=
        match hf b with (Exists.intro a ha) :=
          ⟨a, (ha.symm ▸ hb : g (f a) = c)⟩ end end
end

namespace hidden
  open nat

  def add : ℕ → ℕ → ℕ
  | a 0        := a
  | a (succ b) := succ (add a b)

  lemma zero_add : Π (a : ℕ), add 0 a = a
  | 0        := rfl
  | (succ b) := congr_arg succ (zero_add b)

  lemma succ_add : Π (a b : ℕ), add (succ a) b = succ (add a b)
  | a 0        := rfl
  | a (succ b) := congr_arg succ (succ_add a b)

  lemma add_comm : Π (a b : ℕ), add a b = add b a
  | a 0        := (zero_add a).symm
  | a (succ b) := eq.trans (@@congr_arg succ (add_comm a b)) (succ_add b a).symm

  lemma add_assoc : Π (a b c : ℕ), add a (add b c) = add (add a b) c
  | a b 0        := rfl
  | a b (succ c) := congr_arg succ (add_assoc a b c)

end hidden

namespace hidden
  open list
  variable {α : Type*}

  def length : list α → ℕ
  | []        := 0
  | (x :: xs) := length xs + 1
  
  def reverse : list α → list α
  | []        := []
  | (x :: xs) := reverse xs ++ [x]
  
  lemma length_append : Π (s t : list α), length (s ++ t) = length s + length t
  | []        t := (nat.zero_add _).symm
  | (x :: xs) t :=
    show length (xs ++ t) + 1 = length xs + 1 + length t,
      by rw [nat.add_assoc, nat.add_comm 1, ← nat.add_assoc, length_append]

  lemma length_reverse : Π (t : list α), length (reverse t) = length t
  | []        := rfl
  | (x :: xs) := 
    show length (reverse xs ++ [x]) = length xs + 1,
      by rw [length_append, length_reverse]; refl

  lemma append_reverse_eq_reverse_append : Π (s t : list α), reverse (s ++ t) = reverse t ++ reverse s
  | [] t        := (append_nil (reverse t)).symm
  | (x :: xs) t :=
    show reverse (xs ++ t) ++ [x] = reverse t ++ (reverse xs ++ [x]),
      by rw [append_reverse_eq_reverse_append, append_assoc]

  lemma reverse_reverse_eq_self : Π (t : list α), reverse (reverse t) = t
  | []        := rfl
  | (x :: xs) :=
    show reverse (reverse xs ++ [x]) = x :: xs,
      by rw [append_reverse_eq_reverse_append, reverse_reverse_eq_self]; refl

end hidden

section
  #check @well_founded.fix

  -- Structural recursion on `acc r`, given element `hwf.apply x`.
  def well_founded.fix' {α : Sort*} {C : α → Sort*} {r : α → α → Prop}
    (hwf : well_founded r) (R : Π (x : α), (Π (y : α), r y x → C y) → C x) :
      Π (x : α), C x :=
        λ x, @acc.rec_on α r C x (hwf.apply x) (λ x' hx', R x')
end

inductive vector (α : Type) : ℕ → Type
| vnil  :                           vector 0
| vcons : Π {n : ℕ}, α → vector n → vector n.succ

namespace vector
  def vec1 := vcons 1 (vcons 2 (vcons 3 vnil))
  def vec2 := vcons 4 (vcons 5 vnil)

  -- Using EC
  def tail {α : Type} {n : ℕ} : vector α (n + 1) → vector α n
  | (vcons a as) := as
  
  -- Using recursor
  -- (See: https://leanprover.github.io/theorem_proving_in_lean/induction_and_recursion.html#dependent-pattern-matching)
  def tail_aux {α : Type*} {n n' : ℕ} (v : vector α n') : n' = n + 1 → vector α n :=
    vector.cases_on v -- Cases on `v` first so you could use that equality
      (λ (h : 0 = n + 1), nat.no_confusion h)
      (λ n' (a : α) (as : vector α n') (h : n' + 1 = n + 1),
        nat.no_confusion h (λ h₁ : n' = n, eq.rec_on h₁ as))

  def tail' {α : Type*} {n : ℕ} (v : vector α (n + 1)) : vector α n :=
    tail_aux v rfl

  -- Using EC
  def append {α : Type} : Π {m : ℕ} (u : vector α m) {n : ℕ} (v : vector α n), vector α (n + m)
  | nat.zero      vnil         n v := v
  | (nat.succ m') (vcons a as) n v := vcons a (append as v)

  #reduce append vec1 vec2

  -- Using recursor (without using an auxiliary function???)
  def append' {α : Type} : Π {m : ℕ} (u : vector α m) {n : ℕ} (v : vector α n), vector α (n + m) :=
    λ m u n v,
      @vector.rec_on _ (λ m' _, vector α (n + m')) _ u
        v
        (λ m' a as acc, vcons a acc)

  #reduce append' vec1 vec2

  -- (TODO: the real challenge???)
  -- (See: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/more.20more.20basics/near/190957263)
end vector

section
  inductive aexpr : Type
  | const : ℕ             → aexpr
  | var   : ℕ             → aexpr
  | plus  : aexpr → aexpr → aexpr
  | times : aexpr → aexpr → aexpr

  open aexpr

  def sample_aexpr : aexpr := plus (times (var 0) (const 7)) (times (const 2) (var 1))
  
  def aeval (v : ℕ → ℕ) : aexpr → ℕ
  | (const n)     := n
  | (var n)       := v n
  | (plus e₁ e₂)  := aeval e₁ + aeval e₂
  | (times e₁ e₂) := aeval e₁ * aeval e₂

  def sample_val : ℕ → ℕ
  | 0 := 5
  | 1 := 6
  | _ := 0

  #eval aeval sample_val sample_aexpr

  def simp_const : aexpr → aexpr
  | (plus (const n₁) (const n₂))  := const (n₁ + n₂)
  | (times (const n₁) (const n₂)) := const (n₁ * n₂)
  | e                             := e

  def fuse : aexpr → aexpr
  | (const n)     := (const n)
  | (var n)       := (var n)
  | (plus e₁ e₂)  := simp_const (plus (fuse e₁) (fuse e₂))
  | (times e₁ e₂) := simp_const (times (fuse e₁) (fuse e₂))

  theorem simp_const_eq (v : ℕ → ℕ) : ∀ e : aexpr, aeval v (simp_const e) = aeval v e
  | (const n)     := rfl
  | (var n)       := rfl
  | (plus e₁ e₂)  := by { cases e₁; cases e₂; refl }
  | (times e₁ e₂) := by { cases e₁; cases e₂; refl }

  theorem fuse_eq (v : ℕ → ℕ) : ∀ e : aexpr, aeval v (fuse e) = aeval v e
  | (const n)     := rfl
  | (var n)       := rfl
  | (plus e₁ e₂)  :=
    show aeval v (simp_const (plus (fuse e₁) (fuse e₂))) = aeval v (plus e₁ e₂),
      by { rw simp_const_eq, unfold aeval, rw [fuse_eq, fuse_eq] }
  | (times e₁ e₂) :=
    show aeval v (simp_const (times (fuse e₁) (fuse e₂))) = aeval v (times e₁ e₂),
      by { rw simp_const_eq, unfold aeval, rw [fuse_eq, fuse_eq] }

end

end exercise_8



