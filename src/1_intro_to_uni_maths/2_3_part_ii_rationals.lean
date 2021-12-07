import tactic
import .«2_2_part_ii_integers»

namespace notes

-- Add this line in the beginning of each file to override the default ℕ
local notation `ℕ` : 1024 := mynat
-- Add this line in the beginning of each file to override the default ℤ
local notation `ℤ` : 1024 := myint
-- Nonzero integers
def nzint : Type := {x : ℤ // x ≠ 0}
local notation `ℤ*` : 1024 := nzint

universe u

--------------------------------------------------------------------------------
-- # Rationals

namespace myrat

-- The equivalence relation
  def eqv : ℤ × ℤ* → ℤ × ℤ* → Prop :=
    λ ⟨a, b, _⟩ ⟨c, d, _⟩, a * d = c * b

  local infix `∼` : 50 := eqv

  lemma eqv_refl : ∀ x, x ∼ x :=
    λ ⟨a, b, hb⟩, rfl

  lemma eqv_symm : ∀ x y, x ∼ y → y ∼ x :=
    λ ⟨a, b, hb⟩ ⟨c, d, hd⟩ h, h.symm

  lemma eqv_trans : ∀ x y z, x ∼ y → y ∼ z → x ∼ z :=
    λ ⟨a, b, hb⟩ ⟨c, d, hd⟩ ⟨e, f, hf⟩ h₁ h₂, by
    { unfold eqv at *,
      have h : a * d * c * f = e * d * c * b,
      { rw [h₁, ← h₂], sorry },
      sorry }

  lemma eqv_equivalence_relation : is_equivalence_relation (∼) :=
    ⟨eqv_refl, eqv_symm, eqv_trans⟩

end myrat

-- Definition of ℝ as a quotient type
-- (i.e. equivalence classes under the equivalence relation)
def myrat : Type :=
  @quot (ℤ × ℤ*) myrat.eqv

-- Add this line in the beginning of each file to override the default ℝ
local notation `ℚ` : 1024 := myrat

namespace myrat
section
  local infix ` ∼ ` : 50 := eqv

-- Addition
  def add_fn : ℤ × ℤ* → ℤ × ℤ* → ℤ × ℤ* :=
    λ ⟨a, b, hb⟩ ⟨c, d, hd⟩, (a * d + c * b, ⟨b * d, sorry⟩)

  lemma add_respects_fst :
    ∀ (x₁ x₂ y : ℤ × ℤ*), (x₁ ∼ x₂) → (add_fn x₁ y ∼ add_fn x₂ y)
  :=
  begin
    rintros ⟨a₁, b₁, hb₁⟩ ⟨a₂, b₂, hb₂⟩ ⟨c, d, hd⟩ h,
    unfold add_fn at *,
    unfold eqv at *,
    sorry
  end

  lemma add_respects_snd :
    ∀ (x y₁ y₂ : ℤ × ℤ*), (y₁ ∼ y₂) → (add_fn x y₁ ∼ add_fn x y₂)
  :=
  begin
    rintros ⟨a, b, hb⟩ ⟨c₁, d₁, hd₁⟩ ⟨c₂, d₂, hd₂⟩ h,
    unfold add_fn at *,
    unfold eqv at *,
    sorry
  end

  def add : ℚ → ℚ → ℚ :=
    quot.map₂ add_fn add_respects_snd add_respects_fst
  instance : has_add ℚ := ⟨add⟩

-- Negation
  def neg_fn : ℤ × ℤ* → ℤ × ℤ* :=
    λ ⟨a, b, hb⟩, (-a, ⟨b, hb⟩)
  
  lemma neg_respects :
    ∀ (x₁ x₂ : ℤ × ℤ*), (x₁ ∼ x₂) → (neg_fn x₁ ∼ neg_fn x₂)
  :=
  begin
    rintros ⟨a₁, b₁, hb₁⟩ ⟨a₂, b₂, hb₂⟩ h,
    unfold neg_fn at *,
    unfold eqv at *,
    sorry
  end

  def neg : ℚ → ℚ :=
    quot.map neg_fn neg_respects
  instance : has_neg ℚ := ⟨neg⟩

-- Multiplication
  def mul_fn : ℤ × ℤ* → ℤ × ℤ* → ℤ × ℤ* :=
    λ ⟨a, b, hb⟩ ⟨c, d, hd⟩, (a * c, ⟨b * d, sorry⟩)

  lemma mul_respects_fst :
    ∀ (x₁ x₂ y : ℤ × ℤ*), (x₁ ∼ x₂) → (mul_fn x₁ y ∼ mul_fn x₂ y)
  :=
  begin
    rintros ⟨a₁, b₁, hb₁⟩ ⟨a₂, b₂, hb₂⟩ ⟨c, d, hd⟩ h,
    unfold mul_fn at *,
    unfold eqv at *,
    sorry
  end

  lemma mul_respects_snd :
    ∀ (x y₁ y₂ : ℤ × ℤ*), (y₁ ∼ y₂) → (mul_fn x y₁ ∼ mul_fn x y₂)
  :=
  begin
    rintros ⟨a, b, hb⟩ ⟨c₁, d₁, hd₁⟩ ⟨c₂, d₂, hd₂⟩ h,
    unfold mul_fn at *,
    unfold eqv at *,
    sorry
  end

  def mul : ℚ → ℚ → ℚ :=
    quot.map₂ mul_fn mul_respects_snd mul_respects_fst
  instance : has_mul ℚ := ⟨mul⟩

-- Inversion (TODO: complete)
  def inv_fn : ℤ × ℤ* → ℤ × ℤ* := sorry

  lemma inv_respects :
    ∀ (x₁ x₂ : ℤ × ℤ*), (x₁ ∼ x₂) → (inv_fn x₁ ∼ inv_fn x₂)
  :=
  begin
    rintros ⟨a₁, b₁, hb₁⟩ ⟨a₂, b₂, hb₂⟩ h,
    unfold inv_fn at *,
    unfold eqv at *,
    sorry
  end

  def inv : ℚ → ℚ :=
    quot.map inv_fn inv_respects
  instance : has_inv ℚ := ⟨inv⟩

-- Less or equal than
  def le_fn : ℤ × ℤ* → ℤ × ℤ* → Prop :=
    λ ⟨a, b, hb⟩ ⟨c, d, hd⟩, a * d ≤ c * b

  lemma le_respects_fst :
    ∀ (x₁ x₂ y : ℤ × ℤ*), x₁ ∼ x₂ → le_fn x₁ y = le_fn x₂ y
  :=
  begin
    rintros ⟨a₁, b₁, hb₁⟩ ⟨a₂, b₂, hb₂⟩ ⟨c, d, hd⟩ h,
    unfold le_fn at *,
    unfold eqv at *,
    apply propext,
    split,
    { intros h₁, sorry },
    { intros h₁, sorry }
  end

  lemma le_respects_snd :
    ∀ (x y₁ y₂ : ℤ × ℤ*), (y₁ ∼ y₂) → le_fn x y₁ = le_fn x y₂
  :=
  begin
    rintros ⟨a, b, hb⟩ ⟨c₁, d₁, hd₁⟩ ⟨c₂, d₂, hd₂⟩ h,
    unfold le_fn at *,
    unfold eqv at *,
    sorry
  end

  def le : ℚ → ℚ → Prop :=
    quot.lift₂ le_fn le_respects_snd le_respects_fst
  instance : has_le ℚ := ⟨le⟩

-- Less than
  def lt_fn : ℤ × ℤ* → ℤ × ℤ* → Prop :=
    λ ⟨a, b, hb⟩ ⟨c, d, hd⟩, a * d < c * b

  lemma lt_respects_fst :
    ∀ (x₁ x₂ y : ℤ × ℤ*), x₁ ∼ x₂ → lt_fn x₁ y = lt_fn x₂ y
  :=
  begin
    rintros ⟨a₁, b₁, hb₁⟩ ⟨a₂, b₂, hb₂⟩ ⟨c, d, hd⟩ h,
    unfold lt_fn at *,
    unfold eqv at *,
    sorry
  end

  lemma lt_respects_snd :
    ∀ (x y₁ y₂ : ℤ × ℤ*), (y₁ ∼ y₂) → lt_fn x y₁ = lt_fn x y₂
  :=
  begin
    rintros ⟨a, b, hb⟩ ⟨c₁, d₁, hd₁⟩ ⟨c₂, d₂, hd₂⟩ h,
    unfold lt_fn at *,
    unfold eqv at *,
    sorry
  end

  def lt : ℚ → ℚ → Prop :=
    quot.lift₂ lt_fn lt_respects_snd lt_respects_fst
  instance : has_lt ℚ := ⟨lt⟩

end

section
-- TODO: ℤ as a subset of ℚ

  def zero : ℚ := quot.mk eqv (0, ⟨1, myint.zero_ne_one.symm⟩)
  def one : ℚ := quot.mk eqv (1, ⟨1, myint.zero_ne_one.symm⟩)

  instance : has_zero ℚ := ⟨zero⟩
  instance : has_one ℚ := ⟨one⟩

  lemma zero_ne_one :
    zero ≠ one
  :=
    sorry
end

section
  local infix ` ∼ ` : 50 := eqv
  variables (x y z : ℚ)

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

  -- TODO: `inv_mul` and `mul_inv`

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
  variables (x y z : ℚ)

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

end myrat

--------------------------------------------------------------------------------

end notes
