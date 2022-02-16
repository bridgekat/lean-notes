import data.nat.basic
import data.int.basic
import data.rat.basic
import data.real.basic
import data.complex.basic
import data.list

import tactic
import tactic.rewrite_search.frontend


namespace notes

section
  parameters (G : Type) [has_mul G]
  -- parameters (mul_assoc : ∀ a b c : G, a * (b * c) = (a * b) * c)
  -- parameters (mul_comm : ∀ a b : G, a * b = b * a)

  def is_left_id  (e : G) : Prop := ∀ g : G, e * g = g
  def is_right_id (e : G) : Prop := ∀ g : G, g * e = g

  section
    parameters (e₁ : G) (he₁ : is_left_id e₁)
    parameters (e₂ : G) (he₂ : is_right_id e₂)

    lemma left_id_eq_right_id : e₁ = e₂ := eq.trans (eq.symm (he₂ e₁)) (he₁ e₂)
  end

  def is_id (e : G) : Prop := is_left_id e ∧ is_right_id e

  section
    parameters (e : G) (he : is_id e)
    parameters (e' : G) (he' : is_id e')

    lemma id_unique : e = e' :=
      left_id_eq_right_id _ he.left _ he'.right
  end

  section
    parameters (e : G) (he : is_left_id e ∧ is_right_id e)
    parameters (g : G)

    def has_left_inv_of  (h : G) : Prop := h * g = e
    def has_right_inv_of (h : G) : Prop := g * h = e

    section
      parameters (mul_assoc' : ∀ a b c : G, a * (b * c) = (a * b) * c)
      parameters (h₁ : G) (hh₁ : has_left_inv_of h₁)
      parameters (h₂ : G) (hh₂ : has_right_inv_of h₂)

      -- h₁ = h₁ * e = h₁ * (g * h₂) = (h₁ * g) * h₂ = e * h₂ = h₂
      include g e he h₁ hh₁ h₂ hh₂ mul_assoc'
      lemma left_inv_eq_right_inv : h₁ = h₂ := by
        calc  h₁
            = h₁ * e        : eq.symm (he.right h₁)
        ... = h₁ * (g * h₂) : congr_arg2 (*) rfl hh₂.symm
        ... = (h₁ * g) * h₂ : mul_assoc' _ _ _
        ... = e * h₂        : congr_arg2 (*) hh₁ rfl
        ... = h₂            : he.left h₂

      -- I don't know why tactics are not working properly here!
      -- Probably another reason why I have to invent my own prover...
    end

    def has_inv_of (h : G) : Prop := h * g = e ∧ g * h = e

    section
      parameters (mul_assoc' : ∀ a b c : G, a * (b * c) = (a * b) * c)
      parameters (h : G) (hh : has_inv_of h)
      parameters (h' : G) (hh' : has_inv_of h')

      include g e he h hh h' hh' mul_assoc'
      lemma inv_unique : h = h' :=
        left_inv_eq_right_inv mul_assoc' _ hh.left _ hh'.right
    end
  end
end

@[class]
structure group (G : Type) : Type :=
  (mul : G → G → G)
  (mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c))
  (e : G)
  (he : ∀ g : G, mul e g = g ∧ mul g e = g)
  (i : G → G)
  (hi : ∀ g : G, mul (i g) g = e ∧ mul g (i g) = e)



end notes
