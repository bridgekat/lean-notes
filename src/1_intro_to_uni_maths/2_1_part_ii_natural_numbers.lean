import tactic
import tactic.rewrite_search.frontend
import .«1_part_i»
noncomputable theory

namespace notes

universe u

--------------------------------------------------------------------------------
-- Definitions from the Natural Number Game (modified)

-- Definition of ℕ as an inductive type
inductive mynat : Type
| zero :         mynat
| succ : mynat → mynat

namespace mynat

  instance : has_zero mynat := ⟨mynat.zero⟩
  theorem mynat_zero_eq_zero : mynat.zero = 0 := rfl

  def one : mynat := succ 0
  instance : has_one mynat := ⟨mynat.one⟩

-- Addition
  def add : mynat → mynat → mynat
  | m 0        := m
  | m (succ n) := succ (add m n)
  instance : has_add mynat := ⟨add⟩

  @[simp, rewrite] def add_zero (m : mynat) : m + 0 = m := rfl
  @[simp, rewrite] def add_succ (m n : mynat) : m + succ n = succ (m + n) := rfl

  -- (Numerals now work)
  example : mynat := 37

-- Multiplication
  def mul : mynat → mynat → mynat
  | m 0        := 0
  | m (succ n) := mul m n + m
  instance : has_mul mynat := ⟨mul⟩

  @[simp, rewrite] def mul_zero (m : mynat) : m * 0 = 0 := rfl
  @[simp, rewrite] def mul_succ (m n : mynat) : m * succ n = m * n + m := rfl

-- Power
/-
  def pow : mynat → mynat → mynat
  | m 0        := 1
  | m (succ n) := pow m n * m
  instance : has_pow mynat mynat := ⟨pow⟩

  @[simp, rewrite] def pow_zero (m : mynat) : m ^ (0 : mynat) = 1 := rfl
  @[simp, rewrite] def pow_succ (m n : mynat) : m ^ succ n = m ^ n * m := rfl
-/

-- Less or equal than
  def le (m n : mynat) : Prop :=
    ∃ (v : mynat), n = m + v
  instance has_le : has_le mynat := ⟨le⟩

-- Less than
  def lt (m n : mynat) : Prop :=
    ∃ (v : mynat), v ≠ 0 ∧ n = m + v
  instance : has_lt mynat := ⟨lt⟩

end mynat

-- Add this line in the beginning of each file to override the default ℕ
local notation `ℕ` : 1024 := mynat

namespace mynat

-- Peano axioms (here they are all derived theorems!)
-- For proving `no_confusion` with the recursor, refer to TPIL notes
  theorem succ_ne_zero : ∀ (n : ℕ), succ n ≠ 0 :=
    λ n h, mynat.no_confusion h

  theorem succ_inj : ∀ (m n : ℕ), succ m = succ n → m = n :=
    λ m n h, (@mynat.no_confusion (m = n) (succ m) (succ n) h) id

-- (Just a special case of the recursor!)
  theorem axiom_of_induction : ∀ (P : ℕ → Prop),
    P 0 → (∀ n, P n → P (succ n)) → ∀ n, P n :=
      @mynat.rec

-- (Anothor special case of the recursor!)
  def def_by_recursion {α : Type u} : Π (x₀ : α) (F : ℕ → α → α), ℕ → α :=
    @mynat.rec (λ _, α)

-- (For demonstration only; use `rfl` instead)
  variables {α : Type u} (x₀ : α) (F : ℕ → α → α)
  local notation `R` := def_by_recursion x₀ F
  theorem axiom_of_recursion : (R 0 = x₀) ∧ (∀ x, R (succ x) = F x (R x)) :=
    ⟨rfl, (λ x, rfl)⟩

end mynat

--------------------------------------------------------------------------------
-- # Natural Numbers

namespace mynat

section
  variables (x y z : ℕ)

  @[simp, rewrite]
  theorem add_assoc :
    (x + y) + z = x + (y + z)
  :=
  begin
    induction z with z ih,
    { refl },
    { change (x + y + z).succ = (x + (y + z)).succ,
      rw ih }
  end
  
  @[simp, rewrite]
  theorem zero_add :
    0 + x = x
  :=
  begin
    induction x with x ih,
    { refl },
    { change (0 + x).succ = x.succ,
      rw ih, }
  end

  @[simp, rewrite]
  theorem succ_add :
    succ x + y = succ (x + y)
  :=
  begin
    induction y with y ih,
    { refl },
    { change (x.succ + y).succ = (x + y.succ).succ,
      rw ih, refl }
  end

  @[rewrite] -- No @[simp] in commutativity lemmas
  theorem add_comm :
    x + y = y + x
  :=
  begin
    induction y with y ihy generalizing x,
    { erw zero_add, refl },
    { induction x with x ihx,
      { erw zero_add, refl },
      { change (x.succ + y).succ = (y.succ + x).succ,
        rw [← ihx, ihy],
        change (y + x).succ.succ = (x + y).succ.succ,
        rw ihy }}
  end

  @[simp, rewrite]
  theorem add_mul :
    (x + y) * z = x * z + y * z
  :=
  begin
    induction z with z ih,
    { refl },
    { change (x + y) * z + (x + y) = (x * z + x) + (y * z + y),
      rw [ih, add_assoc, ← add_assoc (y * z) x, add_comm (y * z) x],
      simp only [add_assoc] }
    -- TODO: "simp normal forms"
    -- TODO: permute using `assoc` and `comm`? (requires: tactic programming)
  end

  @[rewrite] -- No @[simp] in commutativity lemmas
  theorem mul_comm :
    x * y = y * x
  :=
  begin
    induction y with y ihy generalizing x,
    { induction x with x ihx,
      { refl },
      { exact ihx }},
    { induction x with x ihx,
      { change 0 * y = 0,
        rw ihy, refl },
      { change x.succ * y + x.succ = y.succ * x + y.succ,
        rw [← ihx, ihy],
        change y * x + y + (x + 1) = x * y + x + (y + 1),
        rw [ihy, add_assoc, ← add_assoc y x 1, add_comm y x],
        simp only [add_assoc] }}
  end

  @[simp, rewrite]
  lemma mul_add : x * (y + z) = x * y + x * z :=
    by rw [mul_comm, add_mul, mul_comm y x, mul_comm z x]
  
  @[simp, rewrite]
  lemma zero_mul : 0 * x = 0 :=
    by { rw [mul_comm], refl }
  
  @[simp, rewrite]
  lemma succ_mul : succ x * y = x * y + y :=
    by { rw [mul_comm, mul_comm x y], refl }

  @[simp, rewrite]
  theorem one_mul :
    1 * x = x
  :=
  begin
    induction x with x ih,
    { refl },
    { change 1 * x + 1 = x.succ,
      rw ih, refl }
  end

  @[simp, rewrite]
  theorem mul_one :
    x * 1 = x
  :=
  begin
    change 0 + x = x,
    exact zero_add x,
  end

  @[simp, rewrite]
  theorem mul_assoc :
    (x * y) * z = x * (y * z)
  :=
  begin
    induction z with z ih,
    { refl },
    { change x * y * z + x * y = x * (y * z + y),
      rw [mul_add, ih] }
  end

end

--------------------------------------------------------------------------------

section
  variables (x y z : ℕ)

  theorem add_right_cancel :
    x + z = y + z → x = y
  :=
  begin
    induction z with z ih,
    { exact id },
    { intros h,
      replace h := succ.inj h,
      exact ih h }
  end

  lemma add_left_cancel : x + y = x + z → y = z :=
    by { rw [add_comm x y, add_comm x z], exact add_right_cancel _ _ _ }

  lemma zero_of_add_right_eq_self :
    x + y = x → y = 0
  :=
  begin
    intros h,
    exact add_left_cancel x _ _ h
  end

  lemma zero_of_add_zero :
    x + y = 0 → x = 0 ∧ y = 0
  :=
  begin
    intros h, split,
    { cases y with y, { exact h }, { injections }},
    { cases y with y, { refl }, { injections }}
  end

  theorem mul_right_cancel :
    z ≠ 0 → x * z = y * z → x = y
  :=
  begin
    cases z with z',
    { intros h, exfalso, exact h rfl },
    intros _ h,
    induction x with x ih generalizing y,
    { erw zero_mul at h,
      change 0 = y * z' + y at h,
      cases y with y, { refl }, { injections }},
    { rw succ_mul at h,
      cases y with y',
      { erw zero_mul at h,
        change (x * z'.succ + z').succ = 0 at h,
        injections },
      { rw succ_mul at h,
        replace h := add_right_cancel _ _ _ h,
        rw (ih y' h) }}
  end

  lemma mul_left_cancel : x ≠ 0 → x * y = x * z → y = z :=
    by { rw [mul_comm x y, mul_comm x z], exact mul_right_cancel _ _ _ }

end

--------------------------------------------------------------------------------

-- `ℕ` is a "commutative semiring" with `add_left_cancel` and `mul_left_cancel`!
-- I found some relevant typeclasses in Lean:

instance add_cancel_comm_monoid : add_cancel_comm_monoid mynat :=
  { add             := mynat.add,
    add_assoc       := mynat.add_assoc,
    add_left_cancel := mynat.add_left_cancel,
    zero            := mynat.zero,
    zero_add        := mynat.zero_add,
    add_zero        := mynat.add_zero,
    add_comm        := mynat.add_comm }

instance comm_semiring : comm_semiring mynat :=
  { mul             := mynat.mul,
    left_distrib    := mynat.mul_add,
    right_distrib   := mynat.add_mul,
    zero_mul        := mynat.zero_mul,
    mul_zero        := mynat.mul_zero,
    mul_assoc       := mynat.mul_assoc,
    one             := mynat.one,
    one_mul         := mynat.one_mul,
    mul_one         := mynat.mul_one,
    mul_comm        := mynat.mul_comm,
    ..mynat.add_cancel_comm_monoid }

-- These DO NOT cover the conditional `mul_left_cancel`, though...

--------------------------------------------------------------------------------

section
  variables (x y z : ℕ)

-- Alternative way to switch between ≤ and < (other than by definition)
  lemma le_iff_lt_or_eq :
    x ≤ y ↔ (x < y ∨ x = y)
  :=
  begin
    split,
    { rintros ⟨v, hv⟩,
      cases v with v,
      { right, exact eq.symm hv },
      { left, use v.succ, refine ⟨_, hv⟩, intros h, injections }},
    { rintros (⟨v, ⟨hv₁, hv₂⟩⟩ | h₂),
      { use v, exact hv₂ },
      { use 0, exact eq.symm h₂ }}
  end

  lemma add_right_le_of_le :
    x ≤ y → x + z ≤ y + z
  :=
  begin
    rintros ⟨c, hc⟩,
    use c,
    rw [hc, add_assoc, add_comm c z],
    simp only [add_assoc]
  end

  lemma mul_right_le_of_le :
    x ≤ y → x * z ≤ y * z
  :=
  begin
    rintros ⟨c, hc⟩,
    use c * z,
    rw [hc, add_mul]
  end

  theorem le_total_order :
    is_total_order le
  :=
  begin
    unfold is_total_order,
    refine ⟨_, _, _, _⟩,
    -- Refl
    { intros x, use 0, refl },
    -- Antisymm
    { rintros x y ⟨c, hc⟩ ⟨d, hd⟩,
      rw [hc, add_assoc] at hd,
      change x + 0 = x + (c + d) at hd,
      replace hd := eq.symm (add_left_cancel _ _ _ hd),
      cases (zero_of_add_zero _ _ hd) with hc₁ hd₁,
      rw hc₁ at hc,
      exact eq.symm hc },
    -- Trans
    { rintros x y z ⟨c, hc⟩ ⟨d, hd⟩,
      use c + d,
      rw [hd, hc, add_assoc] },
    -- Total
    { intros x y,
      induction y with y ih,
      { right, use x, erw zero_add },
      { rcases ih with ⟨c, hc⟩ | ⟨c, hc⟩,
        { left, use c.succ, rw hc, refl },
        { cases c with c',
          { left, use 1, rw hc, refl },
          { right, use c', rw hc, rw succ_add, refl }}}}
  end

  theorem lt_trichotomy :
    x = y ∨ x < y ∨ y < x
  :=
  begin
    rcases le_total_order with ⟨_, _, _, htotal⟩,
    rcases (htotal x y) with ⟨c, hc⟩ | ⟨c, hc⟩,
    { cases c with c',
      { left, exact eq.symm hc },
      { right, left, use c'.succ, split,
        { intros h, injections },
        { exact hc }}},
    { cases c with c',
      { left, exact hc },
      { right, right, use c'.succ, split,
        { intros h, injections },
        { exact hc }}}
  end

  lemma le_iff_not_gt :
    x ≤ y ↔ ¬ (y < x)
  :=
  begin
    split,
    { rintros ⟨c, hc⟩ ⟨d, hd', hd⟩,
      cases d with d, { exact hd' rfl },
      rw [hc, add_assoc] at hd,
      replace hd := zero_of_add_right_eq_self _ _ hd.symm,
      injection hd },
    { intros h,
      rcases lt_trichotomy x y with (h₁|h₂|h₃),
      { use 0, rw h₁, refl },
      { rcases h₂ with ⟨c, _, hc⟩, use c, exact hc },
      { exfalso, exact h h₃ }}
  end

  lemma lt_iff_not_ge :
    x < y ↔ ¬ (y ≤ x)
  :=
  begin
    split,
    { rintros ⟨c, hc', hc⟩ ⟨d, hd⟩,
      cases c with c, { exact hc' rfl },
      rw [hd, add_assoc] at hc,
      replace hc := zero_of_add_right_eq_self _ _ hc.symm,
      injection hc },
    { intros h,
      rcases lt_trichotomy x y with (h₁|h₂|h₃),
      { exfalso, exact h ⟨0, h₁⟩ },
      { exact h₂ },
      { rcases h₃ with ⟨c, _, hc⟩, exfalso, exact h ⟨c, hc⟩ }}
  end

-- TODO: `linarith`

end

--------------------------------------------------------------------------------

section

  theorem based_induction : ∀ (P : ℕ → Prop) (n₀ : ℕ),
    P n₀ → (∀ m, n₀ ≤ m → P m → P (succ m)) → ∀ m, n₀ ≤ m → P m
  :=
    -- (Golfing, for tactic proof see the next theorem)
    λ P n₀ h₀ h m ⟨c, hc⟩, hc.symm ▸ (mynat.rec_on c
      h₀ (λ c' ih, h (n₀ + c') ⟨c', rfl⟩ ih))

  theorem based_strong_induction : ∀ (P : ℕ → Prop) (n₀ : ℕ),
    P n₀ → (∀ m, (∀ k, n₀ ≤ k → k ≤ m → P k) → P (succ m)) → ∀ m, n₀ ≤ m → P m
  :=
  begin
    rintros P n₀ h₀ h m ⟨c, hc⟩,
    have : ∀ x y, y ≤ x → P (n₀ + y),
    { intros x, induction x with x ihx,
      { rintros y ⟨d, hd⟩,
        have hy := (zero_of_add_zero _ _ hd.symm).left,
        rw hy,
        exact h₀ },
      { rintros y ⟨d, hd⟩,
        cases d with d,
        { change x.succ = y at hd,
          rw ← hd,
          apply h (n₀ + x),
          rintros k ⟨e, he⟩ ⟨f, hf⟩,
          rw he,
          apply ihx e,
          use f,
          rw [he, add_assoc] at hf,
          exact add_left_cancel _ _ _ hf },
        { apply ihx,
          use d,
          exact mynat.succ.inj hd, }}},
    rw hc,
    exact this c c ⟨0, rfl⟩
  end

  theorem le_well_order : ∀ (X : set ℕ),
    (∃ a₀, a₀ ∈ X) → ∃ a, (a ∈ X ∧ (∀ x, x ∈ X → a ≤ x))
  :=
  begin
    rintros X ⟨a₀, ha₀⟩,
    by_contra h,
    have : ∀ n m, m ≤ n → m ∉ X,
    { intros n, induction n with n ih,
      -- Claim: 0 is not in X
      { rintros m ⟨k, hk⟩ h₁,
        have hm := (zero_of_add_zero _ _ hk.symm).left,
        apply h, use 0, split,
        { rw ← hm, exact h₁ },
        intros x _, use x, exact (zero_add x).symm, },
      -- IH   : 0 ~ n are not in X
      -- Claim: 0 ~ (succ n) are not in X
      { rintros m ⟨k, hk⟩ h₁,
        cases k with k,
        -- If (succ n) is in X, (succ n) will be the least element of X
        { apply h,
          use m, split, { exact h₁ },
          intros x hx,
          rw le_iff_not_gt,
          rintros ⟨c, ⟨hc₁, hc₂⟩⟩,
          cases c with c, { apply hc₁, refl },
          apply (ih x),
          { use c, apply mynat.succ.inj, rw hk, exact hc₂ },
          { exact hx }},
        -- If any of 0 ~ n is in X, that directly contradicts with IH
        { refine ih m _ h₁,
          use k,
          apply mynat.succ.inj,
          exact hk }}},
    refine this a₀ a₀ _ ha₀,
    use 0, refl
  end

-- TODO: well-ordering principle for decidable predicates
-- TODO: (requires well-founded recursion...?)

end

--------------------------------------------------------------------------------

-- `ℕ` is an "*ordered* commutative semiring"!
-- I found some relevant typeclasses in Lean:

#print classes

#check is_well_order -- TODO

instance linear_order : linear_order mynat :=
  let ⟨hrefl, hantisymm, htrans, htotal⟩ := mynat.le_total_order in
    { le           := mynat.le,
      le_refl      := @hrefl,
      le_antisymm  := @hantisymm,
      le_trans     := @htrans,
      le_total     := @htotal,
      decidable_le := λ (l r : ℕ), classical.prop_decidable (l ≤ r) }

instance ordered_semiring : ordered_semiring mynat :=
  { add_le_add_left         := sorry,
    le_of_add_le_add_left   := sorry,
    zero_le_one             := sorry, -- Does anyone know why this would not work?
    mul_lt_mul_of_pos_left  := sorry,
    mul_lt_mul_of_pos_right := sorry,
    ..mynat.add_cancel_comm_monoid,
    ..mynat.comm_semiring,
    ..mynat.linear_order }

end mynat

--------------------------------------------------------------------------------

end notes
