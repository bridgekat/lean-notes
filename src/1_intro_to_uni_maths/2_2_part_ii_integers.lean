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
      have h : (d + c) + (a + f) = (d + c) + (e + b),
      { -- `rewrite_search` is my dream tactic!
        /- rewrite_search? [h₁, h₂] -/
        conv_lhs { congr, skip, erw [mynat.add_comm] },
        conv_lhs { erw [mynat.add_assoc, mynat.add_comm] },
        conv_lhs { congr, erw [←mynat.add_assoc] },
        conv_lhs { erw [mynat.add_assoc] },
        conv_lhs { congr, erw [h₂] },
        conv_rhs { erw [←mynat.add_assoc] },
        conv_rhs { congr, erw [mynat.add_comm, ←mynat.add_assoc] },
        conv_rhs { erw [mynat.add_assoc] },
        conv_rhs { congr, skip, erw [←h₁] }
        /- end -/ },
      exact mynat.add_left_cancel _ _ _ h }

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
    /- rewrite_search? [h] -/
    conv_lhs { congr, erw [mynat.add_comm] },
    conv_lhs { erw [mynat.add_assoc] },
    conv_lhs { congr, skip, erw [←mynat.add_assoc] },
    conv_lhs { congr, skip, congr, erw [h] },
    ac_refl
    /- end -/
  end

  lemma add_respects_snd :
    ∀ (x y₁ y₂ : ℕ × ℕ), (y₁ ∼ y₂) → (add_fn x y₁ ∼ add_fn x y₂)
  :=
  begin
    rintros ⟨a, b⟩ ⟨c₁, d₁⟩ ⟨c₂, d₂⟩ h,
    unfold add_fn at *,
    unfold eqv at *,
    /- rewrite_search? [h] -/
    conv_lhs { congr, skip, erw [mynat.add_comm] },
    conv_lhs { erw [mynat.add_assoc] },
    conv_lhs { congr, skip, erw [←mynat.add_assoc] },
    conv_lhs { congr, skip, congr, erw [h] },
    conv_rhs { congr, skip, erw [mynat.add_comm] },
    ac_refl
    /- end -/
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
    have : (a₁ + b₂) * c + (a₂ + b₁) * d = (a₂ + b₁) * c + (a₁ + b₂) * d,
    { rw h },
    calc  a₁ * c + b₁ * d + (a₂ * d + b₂ * c)
        = (a₁ + b₂) * c + (a₂ + b₁) * d : by
        { /- rewrite_search? -/
          conv_lhs { congr, skip, erw [mynat.add_comm] },
          conv_lhs { erw [mynat.add_assoc] },
          conv_lhs { congr, skip, erw [mynat.add_comm, mynat.add_assoc] },
          conv_rhs { congr, erw [mynat.add_mul], skip, erw [mynat.add_mul] },
          conv_rhs { erw [mynat.add_assoc] }
          /- end -/ }
    ... = (a₂ + b₁) * c + (a₁ + b₂) * d : by rw h
    ... = a₂ * c + b₂ * d + (a₁ * d + b₁ * c) : by
        { /- rewrite_search? -/
          conv_lhs { congr, erw [mynat.add_mul], skip, erw [mynat.add_mul] },
          conv_lhs { erw [mynat.add_assoc] },
          conv_rhs { erw [mynat.add_assoc] },
          conv_rhs { congr, skip, erw [←mynat.add_assoc, mynat.add_comm] },
          conv_rhs { congr, skip, congr, skip, erw [mynat.add_comm] }
          /- end -/ }
  end

  lemma mul_respects_snd :
    ∀ (x y₁ y₂ : ℕ × ℕ), (y₁ ∼ y₂) → (mul_fn x y₁ ∼ mul_fn x y₂)
  :=
  begin
    rintros ⟨a, b⟩ ⟨c₁, d₁⟩ ⟨c₂, d₂⟩ h,
    have : mul_fn ⟨a, b⟩ ⟨c₁, d₁⟩ = mul_fn ⟨c₁, d₁⟩ ⟨a, b⟩,
    { unfold mul_fn at *, cc },
    rw this,
    have : mul_fn ⟨a, b⟩ ⟨c₂, d₂⟩ = mul_fn ⟨c₂, d₂⟩ ⟨a, b⟩,
    { unfold mul_fn at *, cc },
    rw this,
    exact mul_respects_fst _ _ _ h,
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

  lemma zero_ne_one :
    (0 : ℤ) ≠ 1
  :=
  begin
    intros h,
    let f : ℕ × ℕ → Prop := λ ⟨a, b⟩, ite (b = 0) false true,
    sorry
  end
end

section
  local infix ` ∼ ` : 50 := eqv
  variables (x y z : ℤ)

  @[simp, rewrite]
  theorem add_assoc :
    (x + y) + z = x + (y + z)
  :=
  begin
    revert x y z, rintros ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩,
    change (quot.mk eqv (a + c + e, b + d + f) =
            quot.mk eqv (a + (c + e), b + (d + f))),
    rw [add_assoc, add_assoc]
  end

  @[simp, rewrite]
  theorem zero_add :
    0 + x = x
  :=
  begin
    revert x, rintros ⟨a, b⟩,
    change (quot.mk eqv (0 + a, 0 + b) = quot.mk eqv (a, b)),
    rw [zero_add, zero_add]
  end

  @[simp, rewrite]
  theorem add_zero :
    x + 0 = x
  :=
  begin
    revert x, rintros ⟨a, b⟩,
    change (quot.mk eqv (a + 0, b + 0) = quot.mk eqv (a, b)),
    refl
  end

  @[simp, rewrite]
  theorem neg_add :
    (-x) + x = 0
  :=
  begin
    revert x, rintros ⟨a, b⟩,
    change (quot.mk eqv (b + a, a + b) = quot.mk eqv (0, 0)),
    rw add_comm,
    apply quot.sound,
    unfold eqv,
    simp
  end

  @[simp, rewrite]
  theorem add_neg :
    x + (-x) = 0
  :=
  begin
    revert x, rintros ⟨a, b⟩,
    change (quot.mk eqv (a + b, b + a) = quot.mk eqv (0, 0)),
    rw add_comm,
    apply quot.sound,
    unfold eqv,
    simp
  end

  @[rewrite]
  theorem add_comm :
    x + y = y + x
  :=
  begin
    revert x y, rintros ⟨a, b⟩ ⟨c, d⟩,
    change (quot.mk eqv (a + c, b + d) = quot.mk eqv (c + a, d + b)),
    rw [add_comm a c, add_comm b d]
  end

  @[simp, rewrite]
  theorem mul_assoc :
    (x * y) * z = x * (y * z)
  :=
  begin
    revert x y z, rintros ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩,
    change (quot.mk eqv ((a * c + b * d) * e + (a * d + b * c) * f, (a * c + b * d) * f + (a * d + b * c) * e) =
            quot.mk eqv (a * (c * e + d * f) + b * (c * f + d * e), a * (c * f + d * e) + b * (c * e + d * f))),
    simp only [mynat.mul_assoc, mynat.add_assoc, mynat.mul_add, mynat.add_mul],
    apply quot.sound,
    unfold eqv,
    simp only [mynat.add_assoc, add_right_inj],
    /- TODO: how to automate here? -/
    conv_lhs { rw mynat.add_comm }, simp only [mynat.add_assoc],
    conv_lhs { congr, skip, congr, skip, rw mynat.add_comm, congr, rw mynat.add_comm, congr, rw mynat.add_comm, congr, rw mynat.add_comm }, simp only [mynat.add_assoc],
    conv_lhs { congr, skip, congr, skip, congr, skip, rw mynat.add_comm, congr, rw mynat.add_comm, congr, rw mynat.add_comm }, simp only [mynat.add_assoc],
    conv_lhs { congr, skip, congr, skip, congr, skip, congr, skip, rw mynat.add_comm, congr, rw mynat.add_comm }, simp only [mynat.add_assoc],
    conv_lhs { congr, skip, congr, skip, congr, skip, congr, skip, congr, skip, rw mynat.add_comm },
    /- `rhs: a * (d * f) + (b * (c * f) + (b * (d * e) + (a * (c * f) + (b * (d * f) + (a * (d * e) + b * (c * e))))))` -/
  end

  @[simp, rewrite]
  theorem one_mul :
    1 * x = x
  :=
  begin
    revert x, rintros ⟨a, b⟩,
    change (quot.mk eqv (1 * a + 0 * b, 1 * b + 0 * a) = quot.mk eqv (a, b)),
    simp
  end

  @[simp, rewrite]
  theorem mul_one :
    x * 1 = x
  :=
  begin
    revert x, rintros ⟨a, b⟩,
    change (quot.mk eqv (a * 1 + b * 0, a * 0 + b * 1) = quot.mk eqv (a, b)),
    simp
  end

  @[rewrite]
  theorem mul_comm :
    x * y = y * x
  :=
  begin
    revert x y, rintros ⟨a, b⟩ ⟨c, d⟩,
    change (quot.mk eqv (a * c + b * d, a * d + b * c) =
            quot.mk eqv (c * a + d * b, c * b + d * a)),
    rw [mul_comm a c, mul_comm b d, mul_comm a d, mul_comm b c, mynat.add_comm (d * a)]
  end

  @[simp, rewrite]
  theorem add_mul :
    (x + y) * z = x * z + y * z
  :=
  begin
    revert x y z, rintros ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩,
    change (quot.mk eqv ((a + c) * e + (b + d) * f, (a + c) * f + (b + d) * e) =
            quot.mk eqv ((a * e + b * f) + (c * e + d * f), (a * f + b * e) + (c * f + d * e))),
    simp only [add_mul],
    ac_refl,
  end

  @[simp, rewrite]
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
    intros h,
    calc  x
        = x + z + -z : by rw [add_assoc, add_neg, add_zero]
    ... = y + z + -z : by rw h
    ... = y          : by rw [add_assoc, add_neg, add_zero]
  end

  lemma add_left_cancel : z + x = z + y → x = y :=
    by { rw [add_comm z x, add_comm z y], exact add_right_cancel _ _ _ }

  theorem mul_right_cancel :
    z ≠ 0 → x * z = y * z → x = y
  :=
  begin
    revert x y z, rintros ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ hef h,
    change (quot.mk eqv (a * e + b * f, a * f + b * e) =
            quot.mk eqv (c * e + d * f, c * f + d * e)) at h,
    
  end

  lemma mul_left_cancel : x ≠ 0 → x * y = x * z → y = z :=
    by { rw [mul_comm x y, mul_comm x z], exact mul_right_cancel _ _ _ }

end

-- TODO: lemmas related to le, lt...

end myint

--------------------------------------------------------------------------------

end notes
