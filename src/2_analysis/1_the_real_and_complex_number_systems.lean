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
  variables (S : set ℝ)

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
  #check real.is_lub_Sup S              --  S.nonempty → bdd_above S → is_lub S (Sup S)

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
-- The following can be done using `simp` or `norm_num` (or even `library_search`!)
-- I did most by hand just to gain familiarity with field axioms (and their Lean names...)

-- (It would be better if we had an UI that completely avoids the use of "names" to refer to theorems...
--  i.e. use type ascriptions only, relying more heavily on library_search and unification algorithms)

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

end

section

  variables (α : Type) [linear_ordered_field α]
  variables (x y z : α)

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

    #check @mul_lt_mul_left _ _ y z x           -- 0 < x → (x * y < x * z ↔ y < z)
    #check @mul_lt_mul_right _ _ y z x          -- 0 < x → (y * x < z * x ↔ y < z)
    example : 0 < x → y < z → x * y < x * z := by
    { intros hx h,
      let a := z + -y,
      have ha : 0 < a,
      { have := add_lt_add_right h (-y),
        rw add_right_neg at this,
        exact this },
      have h₁ : x * y < x * y + x * a,
      { have : 0 < x * a := mul_pos hx ha,
        replace this := add_lt_add_left this (x * y),
        rw add_zero at this,
        exact this },
      calc  x * y
          < x * (y + a)        : by { rw mul_add, exact h₁ }
      ... = x * (y + (z + -y)) : rfl
      ... = x * z              : by { rw [add_comm z, ← add_assoc, add_right_neg, zero_add] }}

    #check @mul_lt_mul_left_of_neg _ _ y z x    -- x < 0 → (x * y < x * z ↔ z < y)
    #check @mul_lt_mul_right_of_neg _ _ y z x   -- x < 0 → (y * x < z * x ↔ z < y)
    example : x < 0 → y < z → x * z < x * y := by
    { intros hx h,
      let a := z + -y,
      have ha : 0 < a,
      { have := add_lt_add_right h (-y),
        rw add_right_neg at this,
        exact this },
      have h₁ : x * y + x * a < x * y,
      { have : 0 < -x * a,
        { have hnx : 0 < -x,
          { calc  0
                = -x + x : by rw add_left_neg
            ... < -x + 0 : add_lt_add_left hx (-x)
            ... = -x     : by rw add_zero },
          exact mul_pos hnx ha },
        replace this := add_lt_add_left this (x * y),
        rw add_zero at this,
        replace this := add_lt_add_right this (x * a),
        rw [add_assoc, ← add_mul, add_left_neg, zero_mul, add_zero] at this,
        exact this },
      calc  x * z
          = x * (y + (z + -y)) : by { rw [add_comm z, ← add_assoc, add_right_neg, zero_add] }
      ... = x * (y + a)        : rfl
      ... < x * y              : by { rw mul_add, exact h₁ }}

    #check @mul_self_pos _ _ x                  -- x ≠ 0 → 0 < x * x
    example : x ≠ 0 → 0 < x * x := by
    { intros hx',
      rcases lt_trichotomy x 0 with (hx|hx|hx),
      { have : x * 0 < x * x := (mul_lt_mul_left_of_neg hx).mpr hx,
        rw mul_zero at this,
        exact this },
      { exfalso, exact hx' hx },
      { have : x * 0 < x * x := (mul_lt_mul_left hx).mpr hx,
        rw mul_zero at this,
        exact this }}
    
    #check zero_lt_one                          -- 0 < 1
    #check neg_one_lt_zero                      -- -1 < 0
    example : (0 : α) < 1 := by
    { have : (0 : α) < 1 * 1 := mul_self_pos one_ne_zero,
      rw mul_one at this,
      exact this }

    #check @inv_pos _ _ x                       -- 0 < x⁻¹ ↔ 0 < x
    example : 0 < x → 0 < x⁻¹ := by
    { intros hx,
      have hx₀ : x ≠ 0, { intros hx', rw hx' at hx, exact lt_irrefl 0 hx },
      rcases lt_trichotomy x⁻¹ 0 with (h|h|h),
      { exfalso,
        have := (mul_lt_mul_left hx).mpr h,
        rw [mul_inv_cancel hx₀, mul_zero] at this,
        exact lt_irrefl _ (lt_trans zero_lt_one this) },
      { exfalso,
        have : x * x⁻¹ = 0, { rw [h, mul_zero] },
        rw mul_inv_cancel hx₀ at this,
        exact one_ne_zero this },
      { exact h }}

-- example (hx : 0 < x) (h : x < y) : y⁻¹ < x⁻¹ := by library_search!
    example : 0 < x → x < y → y⁻¹ < x⁻¹ := by
    { intros hx h,
      have hy := lt_trans hx h,
      have := (mul_lt_mul_left (inv_pos.mpr hx)).mpr h,
      rw inv_mul_cancel (λ hx' : x = 0, by { rw hx' at hx, exact lt_irrefl _ hx }) at this,
      replace this := (mul_lt_mul_right (inv_pos.mpr hy)).mpr this,
      rw mul_assoc at this,
      rw mul_inv_cancel (λ hy' : y = 0, by { rw hy' at hy, exact lt_irrefl _ hy }) at this,
      rw [one_mul, mul_one] at this,
      exact this }

  end propositions_1_18

-- Some other useful lemmas

  lemma le_iff_not_gt : x ≤ y ↔ ¬ y < x := by
  { split,
    { intros h h',
      rcases le_iff_lt_or_eq.mp h with (h₁|h₁),
      { exact lt_irrefl _ (lt_trans h' h₁) }, { rw h₁ at h', exact lt_irrefl _ h' }},
    { intros h,
      apply le_iff_lt_or_eq.mpr,
      rcases lt_trichotomy x y with (h₁|h₁|h₁),
      { exact or.inl h₁ }, { exact or.inr h₁ }, { exfalso, exact h h₁ }}}

  #check @lt_iff_not_ge _ _ x y                 -- x < y ↔ ¬y ≤ x (def eq)
  #check @le_iff_not_gt _ _ x y                 -- x ≤ y ↔ ¬y < x

end

--------------------------------------------------------------------------------
-- **The real field**

section
-- (TODO: `has_coe ℚ ℝ`)

  variables (x y z : ℝ)

  #check real.archimedean.arch
  theorem real.archimedean' : 0 < x → ∃ n : ℕ, y < n • x := by
-- Proof using the least-upper-bound property
  { intros hx,
    -- Assume otherwise...
    by_contra,
    -- Let A be the set of all nx's...
    let A : set ℝ := (λ z : ℝ, ∃ n : ℕ, z = n • x),
    -- Clearly A is nonempty, and bounded above by y...
    have hne  : A.nonempty := ⟨1 • x, ⟨1, rfl⟩⟩,
    have hbdd : bdd_above A,
    { use y,
      rintros z ⟨n, hn⟩,
      apply (le_iff_not_gt _ _ _).mpr,
      intros hyz,
      apply h, use n,
      rw ← hn, exact hyz },
    -- So we let a := sup A...
    let a := Sup A,
    rcases (real.is_lub_Sup A hne hbdd) with ⟨ha₁, ha₂⟩,
    unfold lower_bounds at ha₂,
    -- And let b := a - x...
    let b := a + -x,
    -- Then b < mx for some m : ℕ (since a is least)...
    have hb : ∃ m : ℕ, b < m • x,
    { by_contra,
      have hb' : b ∈ upper_bounds A,
      { rintros z ⟨mz, hz⟩,
        apply (le_iff_not_gt _ _ _).mpr,
        intros hbz,
        apply h, use mz, rw ← hz, exact hbz },
      replace hb' := ha₂ hb',
      change Sup A ≤ Sup A - x at hb',
      linarith [hb', hx] },
    rcases hb with ⟨m, hb⟩,
    -- Then a < (m + 1) x, contradiction (since a is upper bound)...
    have h₁ : a < (m + 1) • x,
    { rw [add_smul, one_smul],
      have : a + -x < m • x + x + -x,
      { rw [add_assoc, add_right_neg, add_zero], exact hb },
      replace this := add_lt_add_right this x,
      simp only [add_assoc, add_left_neg, add_zero] at this,
      exact this },
    have : (m + 1) • x ∈ A := ⟨m + 1, rfl⟩,
    specialize ha₁ this,
    change Sup A < (m + 1) • x at h₁,
    linarith [h₁, ha₁] }

  theorem real.rat_dense' : x < y → ∃ p : ℚ, x < ↑p ∧ ↑p < y := by
-- Proof using the Archimedean property
  { intros h,
    -- Since y - x > 0, we have an n : ℕ such that n (y - x) > 1...
    -- (1 / n < y - x will be our "unit")
    have hyx : 0 < y + -x,
    { have := add_lt_add_right h (-x),
      rw add_right_neg at this,
      exact this },
    rcases real.archimedean' _ 1 hyx with ⟨n, hn⟩,
    -- Also, there are (m₁ m₂ : ℕ) such that -m₁ < nx < m₂...
    rcases real.archimedean' 1 (-(n • x)) zero_lt_one with ⟨m₁, hm₁⟩,
    rw [nat.smul_one_eq_coe] at hm₁,
    replace hm₁ : - ↑m₁ < n • x,
    { replace hm₁ := (mul_lt_mul_left_of_neg neg_one_lt_zero).mpr hm₁,
      simp only [← neg_eq_neg_one_mul, neg_neg] at hm₁,
      exact hm₁ },
    rcases real.archimedean' 1 (n • x) zero_lt_one with ⟨m₂, hm₂⟩,
    rw [nat.smul_one_eq_coe] at hm₂,
    -- So, there is an m : ℤ such that m - 1 ≤ nx < m...
    let m : ℤ := sorry,
    have hml : ↑(m + -1) ≤ n • x := sorry,
    have hmr : n • x < ↑m        := sorry,
    -- Then m ≤ nx + 1 < ny...
    replace hml : ↑m ≤ n • x + 1,
    { sorry },
    -- So x < m / n < y...
    use (↑m : ℚ) / (↑n : ℚ), split,
    { sorry },
    { sorry }}

  theorem real.exists_nth_root : ∀ n : ℕ, n ≠ 0 → ∃! y : ℝ, npow n y = x := by
  { intros n hn,
    -- Let E be the set consisting of all t : ℝ such that t > 0 and t^n < x...
    let E : set ℝ := (λ t, 0 < t ∧ npow n t < x),
    -- E is nonempty, since x / (x + 1) is in E...
    -- E is bounded above by x + 1...
    -- So we let y := sup E...
    -- Lemma: b^n - a^n < (b - a) n b^(n - 1)...
    -- * If y^n < x, choose h such that 0 < h < 1 and h < (x - y^n) / (n (y + 1)^(n - 1))...
    --   Then (y + h)^n - y^n < h n (y + h)^(n - 1) < h n (y + 1)^(n - 1) < x - y^n...
    --   So (y + h)^n < x, contradiction...
    -- * If y^n = x, all good...
    -- * If x < y^n, choose k := (y^n - x) / (n y^(n - 1)), then 0 < k < y...
    --   * For all t such that y - k ≤ t, y^n - t^n ≤ y^n - (y - k)^n < k n y^(n - 1) = y^n - x...
    --     So t^n > x, so t is not in E...
    --   So y - k is an upper bound of E, contradiction...
    sorry }

  -- lemma...
  -- (I might be giving up on this...)

end

--------------------------------------------------------------------------------
-- **The extended real number system**
-- (Nothing to do here...?)

--------------------------------------------------------------------------------
-- **The complex field**




--------------------------------------------------------------------------------
-- **Euclidean spaces**




end notes
