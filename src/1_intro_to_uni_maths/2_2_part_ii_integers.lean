import tactic
import .«2_1_part_ii_natural_numbers»

namespace notes

-- Add this line in the beginning of each file to override the default ℕ
local notation `ℕ` : 1024 := mynat

universe u

--------------------------------------------------------------------------------
-- # Integers

namespace myint

-- The equivalence relation
  def eqv : ℕ × ℕ → ℕ × ℕ → Prop :=
    λ ⟨a, b⟩ ⟨c, d⟩, a + d = c + b

  local infix `∼` : 50 := eqv

  lemma eqv_refl : ∀ x, x ∼ x :=
    λ ⟨a, b⟩, rfl

  lemma eqv_symm : ∀ x y, x ∼ y → y ∼ x :=
    λ ⟨a, b⟩ ⟨c, d⟩ h, h.symm

  lemma eqv_trans : ∀ x y z, x ∼ y → y ∼ z → x ∼ z :=
    λ ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ h₁ h₂, by
    { unfold eqv at *,
      have h : a + d + c + f = e + d + c + b,
      { rw [h₁, ← h₂], sorry },
      sorry }

  lemma eqv_equivalence_relation : is_equivalence_relation (∼) :=
    ⟨eqv_refl, eqv_symm, eqv_trans⟩

end myint

-- Definition of ℤ as a quotient type
-- (i.e. equivalence classes under the equivalence relation)
def myint : Type :=
  @quot (ℕ × ℕ) myint.eqv

-- Add this line in the beginning of each file to override the default ℤ
local notation `ℤ` : 1024 := myint

namespace myint
section
  local infix ` ∼ ` : 50 := eqv

-- Addition
  def add_fn : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ :=
    λ ⟨a, b⟩ ⟨c, d⟩, (a + c, b + d)

  lemma add_respects_fst :
    ∀ (x₁ x₂ y : ℕ × ℕ), (x₁ ∼ x₂) → (add_fn x₁ y ∼ add_fn x₂ y)
  :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨c, d⟩ h,
    unfold add_fn at *,
    unfold eqv at *,
    sorry
  end

  lemma add_respects_snd :
    ∀ (x y₁ y₂ : ℕ × ℕ), (y₁ ∼ y₂) → (add_fn x y₁ ∼ add_fn x y₂)
  :=
  begin
    rintros ⟨a, b⟩ ⟨c₁, d₁⟩ ⟨c₂, d₂⟩ h,
    unfold add_fn at *,
    unfold eqv at *,
    sorry
  end

  def add : ℤ → ℤ → ℤ :=
    quot.map₂ add_fn add_respects_snd add_respects_fst
  instance : has_add ℤ := ⟨add⟩

-- Negation
  def neg_fn : ℕ × ℕ → ℕ × ℕ :=
    λ ⟨a, b⟩, (b, a)
  
  lemma neg_respects :
    ∀ (x₁ x₂ : ℕ × ℕ), (x₁ ∼ x₂) → (neg_fn x₁ ∼ neg_fn x₂)
  :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h,
    unfold neg_fn at *,
    unfold eqv at *,
    rw [mynat.add_comm, ← h, mynat.add_comm]
  end

  def neg : ℤ → ℤ :=
    quot.map neg_fn neg_respects
  instance : has_neg ℤ := ⟨neg⟩

-- Multiplication
  def mul_fn : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ :=
    λ ⟨a, b⟩ ⟨c, d⟩, (a * c + b * d, a * d + b * c)

  lemma mul_respects_fst :
    ∀ (x₁ x₂ y : ℕ × ℕ), (x₁ ∼ x₂) → (mul_fn x₁ y ∼ mul_fn x₂ y)
  :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨c, d⟩ h,
    unfold mul_fn at *,
    unfold eqv at *,
    sorry
  end

  lemma mul_respects_snd :
    ∀ (x y₁ y₂ : ℕ × ℕ), (y₁ ∼ y₂) → (mul_fn x y₁ ∼ mul_fn x y₂)
  :=
  begin
    rintros ⟨a, b⟩ ⟨c₁, d₁⟩ ⟨c₂, d₂⟩ h,
    unfold mul_fn at *,
    unfold eqv at *,
    sorry
  end

  def mul : ℤ → ℤ → ℤ :=
    quot.map₂ mul_fn mul_respects_snd mul_respects_fst
  instance : has_mul ℤ := ⟨mul⟩

-- Less or equal than
  def le_fn : ℕ × ℕ → ℕ × ℕ → Prop :=
    λ ⟨a, b⟩ ⟨c, d⟩, a + d ≤ c + b

  lemma le_respects_fst :
    ∀ (x₁ x₂ y : ℕ × ℕ), x₁ ∼ x₂ → le_fn x₁ y = le_fn x₂ y
  :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨c, d⟩ h,
    unfold le_fn at *,
    unfold eqv at *,
    apply propext,
    split,
    { intros h₁, sorry },
    { intros h₁, sorry }
  end

  lemma le_respects_snd :
    ∀ (x y₁ y₂ : ℕ × ℕ), (y₁ ∼ y₂) → le_fn x y₁ = le_fn x y₂
  :=
  begin
    rintros ⟨a, b⟩ ⟨c₁, d₁⟩ ⟨c₂, d₂⟩ h,
    unfold le_fn at *,
    unfold eqv at *,
    sorry
  end

  def le : ℤ → ℤ → Prop :=
    quot.lift₂ le_fn le_respects_snd le_respects_fst
  instance : has_le ℤ := ⟨le⟩

-- Less than
  def lt_fn : ℕ × ℕ → ℕ × ℕ → Prop :=
    λ ⟨a, b⟩ ⟨c, d⟩, a + d < c + b

  lemma lt_respects_fst :
    ∀ (x₁ x₂ y : ℕ × ℕ), x₁ ∼ x₂ → lt_fn x₁ y = lt_fn x₂ y
  :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨c, d⟩ h,
    unfold lt_fn at *,
    unfold eqv at *,
    sorry
  end

  lemma lt_respects_snd :
    ∀ (x y₁ y₂ : ℕ × ℕ), (y₁ ∼ y₂) → lt_fn x y₁ = lt_fn x y₂
  :=
  begin
    rintros ⟨a, b⟩ ⟨c₁, d₁⟩ ⟨c₂, d₂⟩ h,
    unfold lt_fn at *,
    unfold eqv at *,
    sorry
  end

  def lt : ℤ → ℤ → Prop :=
    quot.lift₂ lt_fn lt_respects_snd lt_respects_fst
  instance : has_lt ℤ := ⟨lt⟩

end

section
-- TODO: ℕ as a subset of ℤ

  def zero : ℤ := quot.mk eqv (0, 0)
  def one : ℤ := quot.mk eqv (1, 0)

  instance : has_zero ℤ := ⟨zero⟩
  instance : has_one ℤ := ⟨one⟩
end

section
  local infix ` ∼ ` : 50 := eqv
  variables (x y z : ℤ)

  @[simp]
  theorem add_assoc :
    (x + y) + z = x + (y + z)
  :=
  begin
    sorry
  end

  @[simp]
  theorem zero_add :
    zero + x = x
  :=
  begin
    sorry
  end

  @[simp]
  theorem add_zero :
    x + zero = x
  :=
  begin
    sorry
  end

  @[simp]
  theorem neg_add :
    (-x) + x = zero
  :=
  begin
    sorry
  end

  @[simp]
  theorem add_neg :
    x + (-x) = zero
  :=
  begin
    sorry
  end

  --@[simp]
  theorem add_comm :
    x + y = y + x
  :=
  begin
    sorry
  end

  @[simp]
  theorem mul_assoc :
    (x * y) * z = x * (y * z)
  :=
  begin
    sorry
  end

  @[simp]
  theorem one_mul :
    one * x = x
  :=
  begin
    sorry
  end

  @[simp]
  theorem mul_one :
    x * one = x
  :=
  begin
    sorry
  end

  --@[simp]
  theorem mul_comm :
    x * y = y * x
  :=
  begin
    sorry
  end

  @[simp]
  theorem add_mul :
    (x + y) * z = x * z + y * z
  :=
  begin
    sorry
  end

  @[simp]
  lemma mul_add : x * (y + z) = x * y + x * z :=
    by rw [mul_comm, add_mul, mul_comm y x, mul_comm z x]

end

section
  local infix ` ∼ ` : 50 := eqv
  variables (x y z : ℤ)

  theorem add_right_cancel :
    x + z = y + z → x = y
  :=
  begin
    sorry
  end

  lemma add_left_cancel : z + x = z + y → x = y :=
    by { rw [add_comm z x, add_comm z y], exact add_right_cancel _ _ _ }

  theorem mul_right_cancel :
    z ≠ zero → x * z = y * z → x = y
  :=
  begin
    sorry
  end

  lemma mul_left_cancel : z ≠ zero → z * x = z * y → x = y :=
    by { rw [mul_comm z x, mul_comm z y], exact mul_right_cancel _ _ _ }

end

-- TODO: lemmas related to le, lt...

end myint

--------------------------------------------------------------------------------

end notes
