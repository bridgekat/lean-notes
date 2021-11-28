import data.complex.basic
open complex

noncomputable theory

section
  variables a b c : ℂ

  #check complex.field

  -- Field axioms
  #check add_assoc a b c
  #check add_zero a
  #check add_neg_self a
  #check add_comm a b
  #check mul_assoc a b c
  #check mul_one a
  #check mul_inv_cancel -- ha_ne_0
  #check zero_ne_one
  #check mul_comm a b
  #check left_distrib a b c

  -- Real numbers can be coerced into complex numbers
  -- (Since ℝ is isomorphic to a subset of ℂ)
  variables a' b' c' : ℝ
  #check (↑a' : ℂ)
  #check b + ↑c'
  -- TODO: what does ⇑ mean?

  -- Complex conjugation
  #check (conj a : ℂ)
  #check conj_re a
  #check conj_im a
  -- TODO: make clear
end

/-
constant is_vector_space : Type → Prop

namespace vector_space
  
  -- How to define structures in Lean???
  -- How to define partial functions in Lean???

  axiom add_assoc :
    ∀ V, is_vector_space V → ∀ a b c : V, (a + b) + c = a + (b + c)

end vector_space
-/

--------------------------------------------------------------------------------

-- Definitions for a (inner product) vector space V

constant V : Type

constant add : V → V → V
constant zero : V
constant neg : V → V
constant smul : ℂ → V → V
constant inner : V → V → ℂ

instance : has_add V := ⟨add⟩
instance : has_neg V := ⟨neg⟩
instance : has_sub V := ⟨λ x y, x + -y⟩
notation `𝟘` := zero
notation x `*` a := smul x a
notation `⟨` a `,` b `⟩` := inner a b

-- Axioms for a vector space V

axiom v_add_assoc (a b c : V) :
  (a + b) + c = a + (b + c)

axiom v_add_zero (a : V) :
  a + 𝟘 = a

axiom v_add_neg (a : V) :
  a + (-a) = 𝟘

axiom v_add_comm (a b : V) :
  a + b = b + a

axiom v_smul_comp (x y : ℂ) (a : V) :
  (x * y) * a = x * (y * a)

axiom v_one_smul (a : V) :
  1 * a = a

axiom v_add_smul (x y : ℂ) (a : V) :
  (x + y) * a = x * a + y * a

axiom v_smul_add (x : ℂ) (a b : V) :
  x * (a + b) = x * a + x * b

-- Axioms for inner product on V

axiom v_inner_conjsymm (a b : V) :
  ⟨a, b⟩ = conj ⟨b, a⟩

axiom v_inner_add_left (a b c : V) :
  ⟨a + b, c⟩ = ⟨a, c⟩ + ⟨b, c⟩

axiom v_inner_smul_left (x : ℂ) (a b : V) :
  ⟨x * a, b⟩ = x * ⟨a, b⟩

axiom v_inner_pos_of_nonzero (a : V) (h : a ≠ 𝟘) :
  ⟨a, a⟩.re > 0

--------------------------------------------------------------------------------

lemma v_zero_add
  (a : V) :
  𝟘 + a = a :=
begin
  rw [v_add_comm, v_add_zero],
end

lemma v_neg_add
  (a : V) :
  (-a) + a = 𝟘 :=
begin
  rw [v_add_comm, v_add_neg],
end

lemma v_zero_smul
  (a : V) :
  0 * a = 𝟘 :=
begin
  have h₁ := calc
        0 * a
      = ((1 + 1) * 0) * a : by rw [mul_zero (1 + 1 : ℂ)]
  ... = (1 + 1) * (0 * a) : by rw [v_smul_comp]
  ... = 0 * a + 0 * a : by rw [v_add_smul, v_one_smul],
  calc
        0 * a
      = 0 * a + (0 * a + -(0 * a)) : by rw [v_add_neg, v_add_zero]
  ... = 0 * a + -(0 * a) : by rw [← v_add_assoc, ← h₁]
  ... = 𝟘 : by rw v_add_neg,
end

lemma v_negone_smul
  (a : V) :
  (-1) * a = -a :=
begin
  have h₁ := calc
        a + (-1) * a
      = (1 + (-1)) * a : by rw [v_add_smul, v_one_smul]
  ... = 𝟘 : by rw [add_neg_self, v_zero_smul],
  calc
        (-1) * a
      = (-1) * a + (a + (-a)) : by rw [v_add_neg, v_add_zero]
  ... = -a : by rw [← v_add_assoc, v_add_comm _ a, h₁, v_zero_add],
end

--------------------------------------------------------------------------------

lemma v_inner_add_right
  (a b c : V) :
  ⟨a, b + c⟩ = ⟨a, b⟩ + ⟨a, c⟩ :=
begin
  calc  ⟨a, b + c⟩
      = conj ⟨b + c, a⟩ : by rw [v_inner_conjsymm]
  ... = conj (⟨b, a⟩ + ⟨c, a⟩) : by rw [v_inner_add_left]
  ... = conj ⟨b, a⟩ + conj ⟨c, a⟩ : by rw [conj.map_add]
  ... = ⟨a, b⟩ + ⟨a, c⟩ : by rw [← v_inner_conjsymm, ← v_inner_conjsymm]
end

lemma v_inner_smul_right
  (x : ℂ) (a b : V) :
  ⟨a, x * b⟩ = conj x * ⟨a, b⟩ :=
begin
  calc  ⟨a, x * b⟩
      = conj ⟨x * b, a⟩ : by rw [v_inner_conjsymm]
  ... = conj (x * ⟨b, a⟩) : by rw [v_inner_smul_left]
  ... = conj x * conj ⟨b, a⟩ : by rw [conj.map_mul]
  ... = conj x * ⟨a, b⟩ : by rw [← v_inner_conjsymm]
end

lemma v_inner_self_eq_conj_inner_self
  (a : V) :
  ⟨a, a⟩ = conj ⟨a, a⟩ :=
begin
  rw [← v_inner_conjsymm],
end

lemma v_inner_nonzero_of_nonzero (a : V) (h : a ≠ 𝟘) :
  ⟨a, a⟩ ≠ 0 :=
begin
  have h₁ := v_inner_pos_of_nonzero a h,
  intros h0,
  have h₂ : ⟨a, a⟩.re = 0, {
    rw h0,
    trivial,
  },
  rw h₂ at h₁,
  exact gt_irrefl 0 h₁,
end

lemma v_zero_of_inner_self_eq_zero
  (a : V) (h : ⟨a, a⟩ = 0) :
  a = 𝟘 :=
begin
  have h := classical.em (a = 𝟘),
  cases h with ha0 hna0,
  { exact ha0 },
  { have h₁ := v_inner_pos_of_nonzero a hna0,
    rw h at h₁,
    change (0 : ℝ) > 0 at h₁,
    exfalso,
    exact lt_irrefl (0 : ℝ) h₁,
  }
end

--------------------------------------------------------------------------------

-- Definition for norm (length)
-- TODO: square root...
def norm (a : V) :=
  /-sqrt-/ ⟨a, a⟩.re

-- Definition for orthogonal (perpendicular)
def orthogonal (a b : V) :=
  ⟨a, b⟩ = 0

-- Definition for "projection of b on a" (a ≠ 0)
def proj (a b : V) :=
  ⟨b, a⟩ * ⟨a, a⟩⁻¹ * a

-- The difference between the original b and its projected image p must be perpendicular to a
-- i.e. the name "projection" indeed makes sense
lemma proj_residue_orthogonal
  (a b p : V) (h : p = proj a b) (ha : a ≠ 𝟘) :
  orthogonal a (b + -p) :=
begin
  calc  ⟨a, b + -p⟩
      = ⟨a, b⟩ + ⟨a, (-1) * p⟩ : by rw [v_negone_smul, v_inner_add_right]
  ... = ⟨a, b⟩ + -⟨a, p⟩ : by begin rw [v_inner_smul_right], simp end
  ... = ⟨a, b⟩ + -⟨a, ⟨b, a⟩ * ⟨a, a⟩⁻¹ * a⟩ : by begin rw h, unfold proj, end
  ... = ⟨a, b⟩ + -(conj (⟨b, a⟩ * ⟨a, a⟩⁻¹) * ⟨a, a⟩) : by rw [v_inner_smul_right]
  ... = ⟨a, b⟩ + -(conj (⟨b, a⟩ * ⟨a, a⟩⁻¹ * ⟨a, a⟩)) : by rw [conj.map_mul _ ⟨a, a⟩, ← v_inner_self_eq_conj_inner_self]
  ... = ⟨a, b⟩ + -conj ⟨b, a⟩ : by begin rw [mul_assoc, mul_comm _ ⟨a, a⟩, mul_inv_cancel (v_inner_nonzero_of_nonzero a ha)], simp, end
  ... = ⟨a, b⟩ + -⟨a, b⟩ : by rw [v_inner_conjsymm]
  ... = 0 : by simp
end

-- The Cauchy-Schwarz inequality
theorem cauchy_schwarz_ineq
  (a b : V) (ha : a ≠ 𝟘) :
  (⟨a, b⟩ * ⟨b, a⟩).re ≤ (⟨a, a⟩ * ⟨b, b⟩).re :=
begin
  let p : V := proj a b,
  let e : V := b + -p,
  have he : ⟨a, e⟩ = 0 := proj_residue_orthogonal a b p rfl ha,
  have he' : ⟨e, a⟩ = 0, {
    rw v_inner_conjsymm,
    simp [he],
  },
  have hb : b = e + p, {
    -- How to expand definition of e here?
    have he₂ : e = b + -p := rfl,
    rw he₂,
    rw [v_add_assoc, v_add_comm (-p), v_add_neg, v_add_zero],
  },
  let k := ⟨b, a⟩ * ⟨a, a⟩⁻¹,
  have hp : p = k * a := rfl,
  -- Step 1
  have h₁ : ⟨a, p⟩ * ⟨p, a⟩ = ⟨a, a⟩ * ⟨p, p⟩, {
    rw hp,
    rw [v_inner_smul_left, v_inner_smul_right],
    rw [v_inner_smul_left, v_inner_smul_right],
    rw [← mul_assoc, mul_assoc (conj k) ⟨a,a⟩, mul_comm ⟨a, a⟩ k, ← mul_assoc],
    rw [← mul_assoc k, ← mul_assoc ⟨a,a⟩, mul_comm ⟨a,a⟩, mul_comm (conj k) k],
  },
  -- Step 2
  have h₂ : ⟨a, b⟩ * ⟨b, a⟩ = ⟨a, p⟩ * ⟨p, a⟩, {
    rw [hb, v_inner_add_left, v_inner_add_right],
    rw [he, he'], simp,
  },
  -- Step 3
  have h₃ : ⟨p, p⟩.re ≤ ⟨b, b⟩.re, {
    rw [hb, v_inner_add_left, v_inner_add_right, v_inner_add_right _ e p],
    sorry,
  },
  sorry,
end

--------------------------------------------------------------------------------

example (h : (0 : ℝ) > 0) : false :=
begin
  -- library_search,
  sorry
end

-- #lint
