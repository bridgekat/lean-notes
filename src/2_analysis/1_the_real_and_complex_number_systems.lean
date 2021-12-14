/-
# Formalising *Principles of Mathematical Analysis* in Lean

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
-- **The real number field** in Lean

section
  variables (a b c : ℝ)

  #check real.field
  #check real.linear_order
  #check real.linear_ordered_field

-- Field axioms
  #check add_assoc a b c                --  a + b + c = a + (b + c)
  #check add_zero a                     --/ a + 0 = a
  #check zero_add a                     --\ 0 + a = a
  #check add_right_neg a                --/ a + -a = 0
  #check add_left_neg a                 --\ -a + a = 0
  #check add_comm a b                   --  a + b = b + a

  #check mul_assoc a b c                --  a * b * c = a * (b * c)
  #check @zero_ne_one ℝ _ _             --/ 0 ≠ 1
  #check @one_ne_zero ℝ _ _             --\ 1 ≠ 0
  #check mul_one a                      --/ a * 1 = a
  #check one_mul a                      --\ 1 * a = a
  #check @mul_inv_cancel _ _ a          --/ a ≠ 0 → a * a⁻¹ = 1
  #check @inv_mul_cancel _ _ a          --\ a ≠ 0 → a⁻¹ * a = 1
  #check mul_comm a b                   --  a * b = b * a

  #check mul_add a b c                  --/ a * (b + c) = a * b + a * c
  #check add_mul a b c                  --\ (a + b) * c = a * c + b * c

-- Convert between lt and le
  #check @le_iff_lt_or_eq _ _ a b       --/ a ≤ b ↔ a < b ∨ a = b
  #check @lt_iff_le_and_ne _ _ a b      --\ a < b ↔ a ≤ b ∧ a ≠ b

-- Total order axioms (lt)
  #check lt_irrefl a                    --  ¬a < a
  #check @lt_trans _ _ a b c            --  a < b → b < c → a < c
  #check lt_trichotomy a b              --  a < b ∨ a = b ∨ b < a
-- Ordered field axioms (lt)
  #check @add_lt_add_right _ _ _ _ a b  --/ a < b → ∀ (c : ℝ), a + c < b + c
  #check @add_lt_add_left _ _ _ _ b c   --\ b < c → ∀ (a : ℝ), a + b < a + c
  #check @mul_pos _ _ a b               --  0 < a → 0 < b → 0 < a * b

-- Total order axioms (le)
  #check le_refl a                      --  a ≤ a
  #check @le_trans _ _ a b c            --  a ≤ b → b ≤ c → a ≤ c
  #check @le_antisymm _ _ a b           --  a ≤ b → b ≤ a → a = b
  #check le_total a b                   --  a ≤ b ∨ b ≤ a
-- Ordered field axioms (le) (Sure?)
  #check @add_le_add_right _ _ _ _ a b  --/ a ≤ b → ∀ (c : ℝ), a + c ≤ b + c
  #check @add_le_add_left _ _ _ _ b c   --\ b ≤ c → ∀ (a : ℝ), a + b ≤ a + c
  #check @mul_nonneg _ _ a b            --  0 ≤ a → 0 ≤ b → 0 ≤ a * b

-- Completeness axiom (existence & uniqueness of supremum)
  #check real.has_Sup
  #check Sup (λ x : ℝ, x < 1)           -- ℝ (noncomputable)

-- Miscellaneous:
-- * Convert between minus and negation;
-- * Convert between division and inverse;
-- * "smul by integer" as repeated addition;
-- * "pow by integer" as repeated multiplication;
-- * Maximum and minimum (?)
end

--------------------------------------------------------------------------------


-- lemma example_1_1 : ¬ ∃ (p : ℝ), p ^ 2 = 2 := sorry



