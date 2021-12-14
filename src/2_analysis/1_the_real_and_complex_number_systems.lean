/-
# Formalising *Principles of Mathematical Analysis* (Walter Rudin) in Lean

I will be using the mathlib version of `nat`, `int`, `rat` and `real` here...

Note that they are defined differently from those in IUM:

* The integers are defined as an inductive type with two constructors (nonneg, neg);
* The rationals are defined as an inductive type holding the numerator and denominator;
* The reals are defined as equivalence classes of Cauchy sequences.
-/

import data.nat.basic
import data.int.basic
import data.rat.basic
import data.real.basic
import data.list

import tactic
import tactic.rewrite_search.frontend

noncomputable theory

--------------------------------------------------------------------------------
-- **The real field** in Lean

section
  variables (x y z : ℝ)

  #check real.field
  #check real.linear_order
  #check real.linear_ordered_field

-- Field axioms
  #check add_assoc x y z                --  x + y + z = x + (y + z)
  #check add_zero x                     --/ x + 0 = x
  #check zero_add x                     --\ 0 + x = x
  #check add_right_neg x                --/ x + -x = 0
  #check add_left_neg x                 --\ -x + x = 0
  #check add_comm x y                   --  x + y = y + x

  #check mul_assoc x y z                --  x * y * z = x * (y * z)
  #check @zero_ne_one ℝ _ _             --/ 0 ≠ 1
  #check @one_ne_zero ℝ _ _             --\ 1 ≠ 0
  #check mul_one x                      --/ x * 1 = x
  #check one_mul x                      --\ 1 * x = x
  #check @mul_inv_cancel _ _ x          --/ x ≠ 0 → x * x⁻¹ = 1
  #check @inv_mul_cancel _ _ x          --\ x ≠ 0 → x⁻¹ * x = 1
  #check mul_comm x y                   --  x * y = y * x

  #check mul_add x y z                  --/ x * (y + z) = x * y + x * z
  #check add_mul x y z                  --\ (x + y) * z = x * z + y * z

-- Conversion between lt and le
  #check @le_iff_lt_or_eq _ _ x y       --/ x ≤ y ↔ x < y ∨ x = y
  #check @lt_iff_le_and_ne _ _ x y      --\ x < y ↔ x ≤ y ∧ x ≠ y

-- Total order axioms (lt)
  #check lt_irrefl x                    --  ¬x < x
  #check @lt_trans _ _ x y z            --  x < y → y < z → x < z
  #check lt_trichotomy x y              --  x < y ∨ x = y ∨ y < x
-- Ordered field axioms (lt)
  #check @add_lt_add_right _ _ _ _ x y  --/ x < y → ∀ (z : ℝ), x + z < y + z
  #check @add_lt_add_left _ _ _ _ y z   --\ y < z → ∀ (x : ℝ), x + y < x + z
  #check @mul_pos _ _ x y               --  0 < x → 0 < y → 0 < x * y

-- Total order axioms (le)
  #check le_refl x                      --  x ≤ x
  #check @le_trans _ _ x y z            --  x ≤ y → y ≤ z → x ≤ z
  #check @le_antisymm _ _ x y           --  x ≤ y → y ≤ x → x = y
  #check le_total x y                   --  x ≤ y ∨ y ≤ x
-- Ordered field axioms (le)
  #check @add_le_add_right _ _ _ _ x y  --/ x ≤ y → ∀ (z : ℝ), x + z ≤ y + z
  #check @add_le_add_left _ _ _ _ y z   --\ y ≤ z → ∀ (x : ℝ), x + y ≤ x + z
  #check @mul_nonneg _ _ x y            --  0 ≤ x → 0 ≤ y → 0 ≤ x * y

-- Completeness axiom (existence & uniqueness of supremum)
  #check real.has_Sup
  #check Sup (λ x : ℝ, x < 1)           --  ℝ (noncomputable?)

-- Miscellaneous
-- Conversion between minus and negation
  #check sub_eq_add_neg x y             --  x - y = x + -y
-- Conversion between division and inverse
  #check div_eq_mul_inv x y             --  x / y = x * y⁻¹
-- "smul by integer" as repeated addition
  #check nsmul 3 x                      --  ℝ (noncomputable?)
  #check gsmul (-3) x                   --  ℝ (noncomputable?)
-- "pow by integer" as repeated multiplication
  #check npow 3 x                       --  ℝ (noncomputable?)
  #check gpow (-3) x                    --  ℝ (noncomputable?)
-- Maximum and minimum (?)
end


namespace notes

--------------------------------------------------------------------------------
-- **Ordered sets**

section

  def is_upper_bound {α : Type} [linear_order α] (E : set α) (a : α) : Prop :=
    ∀ e, e ∈ E → e ≤ a
  
  def is_lower_bound {α : Type} [linear_order α] (E : set α) (a : α) : Prop :=
    ∀ e, e ∈ E → a ≤ e

  @[class]
  structure bounded_above {α : Type} [linear_order α] (E : set α) : Type :=
    mk :: (a : α) (h : is_upper_bound E a)
  
  @[class]
  structure bounded_below {α : Type} [linear_order α] (E : set α) : Type :=
    mk :: (a : α) (h : is_lower_bound E a)

  -- (TODO: complete)

end

--------------------------------------------------------------------------------
-- **Fields**
-- The following can be done using `simp` or `norm_num`

section

  variables (α : Type) [field α]
  variables (x y z : α)

  section propositions_1_14

    #check @add_left_cancel _ _ x y z           -- x + y = x + z → y = z
    #check @add_right_cancel _ _ x y z          -- x + y = z + y → x = z
    example : x + y = x + z → y = z := by
    { intros h,
      calc  y
          = -x + (x + y) : by rw [← add_assoc, add_left_neg, zero_add]
      ... = -x + (x + z) : by rw h
      ... = z            : by rw [← add_assoc, add_left_neg, zero_add] }

    example : x + y = x → y = 0 := by
    { intros h,
      calc  y
          = -x + (x + y) : by rw [← add_assoc, add_left_neg, zero_add]
      ... = -x + x       : by rw h
      ... = 0            : by rw add_left_neg }

    example : x + y = 0 → y = -x := by
    { intros h,
      calc  y
          = -x + (x + y) : by rw [← add_assoc, add_left_neg, zero_add]
      ... = -x           : by rw [h, add_zero] }

    #check neg_neg x                            -- -(-x) = x
    example : -(-x) = x := by
    { calc  -(-x)
          = x + -x + -(-x) : by rw [add_right_neg, zero_add]
      ... = x              : by rw [add_assoc, add_right_neg, add_zero] }

  end propositions_1_14

  section propositions_1_15

    #check @mul_left_cancel₀ _ _ x y z          -- x ≠ 0 → x * y = x * z → y = z
    #check @mul_right_cancel₀ _ _ x y z         -- y ≠ 0 → x * y = z * y → x = z
    example : x ≠ 0 → x * y = x * z → y = z := by
    { intros hx h,
      calc  y
          = x⁻¹ * (x * y) : by rw [← mul_assoc, inv_mul_cancel hx, one_mul]
      ... = x⁻¹ * (x * z) : by rw h
      ... = z             : by rw [← mul_assoc, inv_mul_cancel hx, one_mul] }

    example : x ≠ 0 → x * y = x → y = 1 := by
    { intros hx h,
      calc  y
          = x⁻¹ * (x * y) : by rw [← mul_assoc, inv_mul_cancel hx, one_mul]
      ... = x⁻¹ * x       : by rw h
      ... = 1             : by rw [inv_mul_cancel hx] }

    example : x ≠ 0 → x * y = 1 → y = x⁻¹ := by
    { intros hx h,
      calc  y
          = x⁻¹ * (x * y) : by rw [← mul_assoc, inv_mul_cancel hx, one_mul]
      ... = x⁻¹           : by rw [h, mul_one] }

    #check inv_inv₀ x                           -- x⁻¹⁻¹ = x
    example : x ≠ 0 → x⁻¹⁻¹ = x := by
    { intros hx,
      calc  x⁻¹⁻¹
          = x * x⁻¹ * x⁻¹⁻¹ : by rw [mul_inv_cancel hx, one_mul]
      ... = x               : by simp [hx] }    -- tql (alternatively, prove x⁻¹ = 0 → false by x * x⁻¹ = 0 = 1)

  end propositions_1_15

  section propositions_1_16

    #check zero_mul x                           -- 0 * x = 0
    #check mul_zero x                           -- x * 0 = 0
    example : 0 * x = 0 := by
    { calc  0 * x
          = 0 * x + 1 * x + -(1 * x) : by rw [add_assoc, add_right_neg, add_zero]
      ... = (0 + 1) * x + -(1 * x)   : by rw add_mul
      ... = 0                        : by rw [zero_add, add_right_neg] }

    #check @mul_ne_zero _ _ _ x y               -- x ≠ 0 → y ≠ 0 → x * y ≠ 0
    example : x ≠ 0 → y ≠ 0 → x * y ≠ 0 := by
    { intros hx hy h,
      have : (1 : α) = 0,
      { calc  1
            = x⁻¹ * x * (y⁻¹ * y) : by rw [inv_mul_cancel hx, inv_mul_cancel hy, mul_one]
        ... = x⁻¹ * y⁻¹ * (x * y) : by rw [mul_assoc, ← mul_assoc x, mul_comm x, mul_assoc y⁻¹, ← mul_assoc]
        ... = 0                   : by rw [h, mul_zero] },
      exact one_ne_zero this }

    #check neg_eq_neg_one_mul x                 -- -x = -1 * x
    example : -x = -1 * x := by
    { calc  -x
          = -x + (1 + -1) * x : by rw [add_right_neg, zero_mul, add_zero]
      ... = -x + x + -1 * x   : by rw [add_mul, one_mul, ← add_assoc]
      ... = -1 * x            : by rw [add_left_neg, zero_add] }

    example : -x * y = -(x * y) := by
    { calc  -x * y
          = -1 * x * y : by simp
      ... = -(x * y)   : by simp }

    example : x * -y = -(x * y) := by
    { calc  x * -y
          = x * -1 * y : by simp
      ... = -1 * x * y : by simp
      ... = -(x * y)   : by simp }

    example : -x * -y = x * y := by
    { calc  -x * -y
          = -1 * x * -1 * y : by simp
      ... = -(-1) * x * y   : by simp
      ... = x * y           : by simp }

  end propositions_1_16

  variables [linear_ordered_field α]

  section propositions_1_18

    #check @neg_lt_zero _ _ _ _ x               -- -x < 0 ↔ 0 < x
    example : 0 < x ↔ -x < 0 := by
    { split,
      { intros h,
        calc  -x
            = -x + 0 : by rw add_zero
        ... < -x + x : add_lt_add_left h (-x)
        ... = 0      : by rw add_left_neg },
      { intros h,
        calc  0
            = x + -x : by rw add_right_neg
        ... < x + 0  : add_lt_add_left h x
        ... = x      : by rw add_zero }}

    

  end propositions_1_18

end

--------------------------------------------------------------------------------
-- **The real field**

section



end

end notes
