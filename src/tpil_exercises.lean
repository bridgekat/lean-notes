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
noncomputable def v0 := vec.empty ℕ -- What is `noncomputable`?
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
-- Intuitionistic: de Morgan 里面是 ∧ 的时候不能把 ¬ 移进去?
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
    (λ hp, h₁ hp hp) -- Don't eliminate cuts!
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
  `finish` seems to use SMT?
  Both are complete for propositional logic.
-/


-- ### Exercise 6

-- Complete reading: https://leanprover.github.io/theorem_proving_in_lean/interacting_with_lean.html


-- ### Exercise 7

namespace exercise_7

inductive myempty : Type

inductive myunit : Type
| star : myunit

inductive mybool : Type
| ff : mybool
| tt : mybool

section
  open mybool

  def bnot : mybool → mybool :=
    @mybool.rec (λ _, mybool) tt ff
  
  def band : mybool → mybool → mybool :=
    λ a b, @mybool.rec (λ _, mybool) ff b a
  
  def bor : mybool → mybool → mybool :=
    λ a b, @mybool.rec (λ _, mybool) b tt a
end

universe u

-- Standard definition for equality
inductive myeq {α : Sort u} (l : α) : α → Prop
| refl [] : myeq l

namespace myeq
  def myeq_symm : Π {α : Sort u} {x y : α} (h : myeq x y), myeq y x :=
    λ α x y h, @myeq.rec α x -- The subject is `myeq {α} x`
      (λ r, myeq r x) -- Make a more general claim: given `myeq x r` then `myeq r x`
      (myeq.refl x)   -- Now given `myeq x x` (implicit), prove `myeq x x`
        y h           -- Then we could specialise `r` to `y`, and give a `myeq x y` to make `myeq y x`
  
  def myeq_trans : Π {α : Sort u} {x y z : α} (h₁ : myeq x y) (h₂ : myeq y z), myeq x z :=
    λ α x y z h₁ h₂, @myeq.rec α y -- The subject is `myeq {α} y`
      (λ r, myeq x r) -- Make a more general claim: given `myeq y r` then `myeq x r`
      h₁              -- Now given `myeq y y` (implicit), prove `myeq x y`
        z h₂          -- Then we could specialise `r` to `z`, and give a `myeq y z` to make `myeq x z`
  
  def myeq_congr : Π {α β : Sort u} {x y : α} (f : α → β) (h : myeq x y), myeq (f x) (f y) :=
    λ α β x y f h, @myeq.rec α x
      (λ r, myeq (f x) (f r))
      (myeq.refl (f x))
        y h
  
  def myeq_subst : Π {α : Sort u} {x y : α} (p : α → Prop) (h₁ : myeq x y) (h₂ : p x), p y :=
    λ α x y p h₁ h₂, @myeq.rec α x
      (λ r, p r)
      h₂
        y h₁
  
  -- Simplify by removing `@` and abbreviating arguments
  def myeq_symm' {α : Sort u} {x y : α} (h : myeq x y) : myeq y x :=
    myeq.rec (myeq.refl x) h
  def myeq_trans' {α : Sort u} {x y z : α} (h₁ : myeq x y) (h₂ : myeq y z) : myeq x z :=
    myeq.rec h₁ h₂
  def myeq_congr' {α β : Sort u} {x y : α} (f : α → β) (h : myeq x y) : myeq (f x) (f y) :=
    myeq.rec (myeq.refl (f x)) h
  def myeq_subst' {α : Sort u} {x y : α} (p : α → Prop) (h₁ : myeq x y) (h₂ : p x) : p y :=
    myeq.rec h₂ h₁
end myeq

--------------------------------------------------------------------------------
-- **Definitions**

inductive mynat : Type
| zero :                mynat
| succ : Π (n : mynat), mynat

open mynat

def one   : mynat := zero.succ
def two   : mynat := zero.succ.succ
def three : mynat := zero.succ.succ.succ

-- Addition
def add : mynat → mynat → mynat :=
  λ a, @mynat.rec
    (λ r, mynat)
    a
    (λ r, λ ar, succ ar)

#reduce add one two

-- Multiplication
def mul : mynat → mynat → mynat :=
  λ a, @mynat.rec
    (λ r, mynat)
    zero
    (λ r, λ ar, add ar a)

#reduce mul two three
#reduce mul three two

-- Predecessor
def pred : mynat → mynat :=
  @mynat.rec
    (λ r, mynat)
    zero
    (λ r, λ predr, r)

#reduce pred zero
#reduce pred one
#reduce pred two
#reduce pred three

-- Truncated subtraction
def monus : mynat → mynat → mynat :=
  λ a, @mynat.rec
    (λ r, mynat)
    a
    (λ r, λ ar, pred ar)

#reduce monus three two
#reduce monus two three

-- Exponentiation
def pow : mynat → mynat → mynat :=
  λ a, @mynat.rec
    (λ _, mynat)
    one
    (λ r, λ ar, mul ar a)

#reduce pow two three
#reduce pow three two

--------------------------------------------------------------------------------
-- **Theorems**





end exercise_7






