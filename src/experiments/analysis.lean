import tactic
import data.nat.basic
import data.real.basic
open function

section
  variables a b c : ℝ

  #check real.field
  #check real.linear_ordered_field

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

  -- Total order axioms
  #check le_refl a
  #check le_trans -- hab hbc
  #check le_antisymm -- hab hba
  #check le_total a b

  -- Ordered field axioms
  #check add_le_add_right -- hab c
  #check mul_nonneg -- ha hb

  -- Completeness axiom (existence & uniqueness of supremum)
  #check real.has_Sup
end

--------------------------------------------------------------------------------

section
  variables (X Y Z : Type)

  theorem injective_def (f : X → Y) : 
    injective f ↔ ∀ (a b : X), f a = f b → a = b :=
  begin
    refl
  end

  theorem surjective_def (f : X → Y) : 
    surjective f ↔ ∀ y : Y, ∃ x : X, f x = y :=
  begin
    refl
  end
end

namespace hidden

-- Definition for countable sets
def countable {T : Type} (S : set T) : Prop :=
  ∃ (f : ℕ → S), bijective f

-- Definition for infinite sets
def infinite {T : Type} (S : set T) : Prop :=
  ∃ (S' : set T), S' ⊆ S ∧ S' ≠ S ∧ ∃ (f : S → S'), bijective f

-- Infinite sets are nonempty
lemma nonempty_of_infinite
  {T : Type}
  (S : set T) (h : infinite S) :
  ∃ x, x ∈ S :=
begin
  unfold infinite at h,
  cases h with S' hS',
  cases hS' with hS'₁ hS'₂, cases hS'₂ with hS'₂ hS'₃,
  cases hS'₃ with f hf,
  -- 讲个笑话，我为了这玩意连用了 by_contra 和 AC...
  -- 以后看看能不能简化...
  have h₁ : S ≠ ∅, {
    intros h₁,
    have h₂ : S' = ∅, {
      ext, split, {
        intros hxS',
        have hxS'₁ := hS'₁ hxS',
        rw h₁ at hxS'₁,
        exact hxS'₁,
      }, {
        intros hF,
        exfalso,
        exact hF,
      },
    },
    rw [h₁, h₂] at hS'₂,
    apply hS'₂, refl,
  },
  have h₂ : ∃x, x ∈ S, {
    by_contra,
    have h₃ : S = ∅, {
      ext, split, {
        intros hxS,
        apply h,
        use x,
        exact hxS,
      }, {
        intros hF,
        exfalso,
        exact hF,
      },
    },
    exact h₁ h₃,
  },
  let x := classical.some h₂,
  have hx := classical.some_spec h₂,
  use x,
  exact hx,
end

-- Every nonempty subset of ℕ has a least element
theorem has_min_of_nonempty_subset_of_N
  (S : set ℕ) (h : ∃ x, x ∈ S) :
  ∃ (x : S), ∀ (y : S), x ≤ y :=
begin
  by_contra h₁,
  have h₂ : ∀ n : ℕ, ∀ m : ℕ, m ≤ n → m ∉ S, {
    intros n,
    induction n with n hn, {
      intros m hm0 hmS,
      apply h₁,
      have hm0 : m = 0, by exact nat.le_zero_iff.mp hm0,
      rw hm0 at hmS,
      rename hmS h0S,
      use ⟨0, h0S⟩,
      intros y,
      have h₂ : 0 ≤ (y : ℕ), by exact zero_le y,
      exact h₂,
    }, {
      intros m hmn hmS,
      cases hmn with _ hmn, {
        apply h₁,
        use ⟨n.succ, hmS⟩,
        intros y,
        have h₂ : n.succ ≤ (y : ℕ), {
          clear hmn hmS h h₁,
          have h₃ : ¬(n.succ > (y : ℕ)), {
            intros h₃,
            have h₄ : n ≥ (y : ℕ), by exact nat.lt_succ_iff.mp h₃,
            cases y with y hy,
            exact hn y h₄ hy,
          },
          exact not_lt.mp h₃,
        },
        exact h₂,
      }, {
        exact hn m hmn hmS,
      },
    },
  },
  cases h with x hx,
  exact h₂ x x rfl.le hx,
end

noncomputable def g {S : set ℕ} (h : infinite S) : ℕ → S
| 0        := classical.some (has_min_of_nonempty_subset_of_N S (nonempty_of_infinite S h))
| (nat.succ n) := g n

-- Every infinite subset of N is countable
lemma countable_of_infinite_subset_of_N
  (S : set ℕ) (h : infinite S) :
  countable S :=
begin
  have h₁ := h,
  unfold infinite at h,
  unfold countable,
  cases h with S' hS,
  cases hS with hS₁ hS₂, cases hS₂ with hS₂ hS₃,
  cases hS₃ with f hf,
  cases hf with hf_inj hf_surj,
  let g₁ := @nat.rec (λ _, ℕ)
    ↑(classical.some (has_min_of_nonempty_subset_of_N S (nonempty_of_infinite S h₁)))
    (λ n, λ gn, gn),
  sorry,
end

end hidden
