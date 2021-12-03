import tactic
import .«1_part_i»

namespace notes

universe u

--------------------------------------------------------------------------------
-- Definitions from the Natural Number Game

-- Definition as inductive type
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
  instance : has_add mynat := ⟨mynat.add⟩

  -- (Numerals now work)
  example : mynat := 37

-- Multiplication
  def mul : mynat → mynat → mynat
  | m 0        := 0
  | m (succ n) := mul m n + m
  instance : has_mul mynat := ⟨mul⟩

-- Power
  def pow : mynat → mynat → mynat
  | m 0        := 1
  | m (succ n) := pow m n * m
  instance : has_pow mynat mynat := ⟨pow⟩

-- Less or equal
  def le (m n : mynat) : Prop :=
    ∃ (v : mynat), n = m + v
  -- Another choice is to define it recursively: 
  -- | le 0 _               := true
  -- | le (succ a) (succ b) := le a b
  instance : has_le mynat := ⟨mynat.le⟩

-- Less than
  def lt (m n : mynat) : Prop :=
    ∃ (v : mynat), v ≠ 0 ∧ n = m + v
  instance : has_lt mynat := ⟨mynat.lt⟩

end mynat

local notation `ℕ` : 1024 := mynat

namespace mynat

-- Peano axioms (here they are all derived theorems!)
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

  @[simp]
  theorem add_assoc :
    (x + y) + z = x + (y + z)
  :=
  begin
    induction z with z ih,
    { refl },
    { change (x + y + z).succ = (x + (y + z)).succ,
      rw ih }
  end

  @[simp]
  theorem zero_add :
    zero + x = x
  :=
  begin
    induction x with x ih,
    { refl },
    { change (zero + x).succ = x.succ,
      rw ih, }
  end

  @[simp]
  theorem succ_add :
    succ x + y = succ (x + y)
  :=
  begin
    induction y with y ih,
    { refl },
    { change (x.succ + y).succ = (x + y.succ).succ,
      rw ih, refl }
  end

  @[simp]
  theorem add_comm :
    x + y = y + x
  :=
  begin
    induction y with y ihy generalizing x,
    { rw zero_add, refl },
    { induction x with x ihx,
      { rw zero_add, refl },
      { change (x.succ + y).succ = (y.succ + x).succ,
        rw [← ihx, ihy],
        change (y + x).succ.succ = (x + y).succ.succ,
        rw ihy }}
  end

  @[simp]
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
  end

  @[simp]
  theorem mul_comm :
    x * y = y * x
  :=
  begin
    induction y with y ihy generalizing x,
    { induction x with x ihx,
      { refl },
      { exact ihx }},
    { induction x with x ihx,
      { change zero * y = zero,
        rw ihy, refl },
      { change x.succ * y + x.succ = y.succ * x + y.succ,
        rw [← ihx, ihy],
        change y * x + y + (x + 1) = x * y + x + (y + 1),
        rw [ihy, add_assoc, ← add_assoc y x 1, add_comm y x],
        simp only [add_assoc] }}
  end

  @[simp]
  lemma mul_add : x * (y + z) = x * y + x * z :=
    by rw [mul_comm, add_mul, mul_comm y x, mul_comm z x]
  
  @[simp]
  lemma zero_mul : zero * x = zero :=
    by { rw [mul_comm], refl }
  
  @[simp]
  lemma succ_mul : succ x * y = x * y + y :=
    by { rw [mul_comm, mul_comm x y], refl }

  @[simp]
  theorem one_mul :
    one * x = x
  :=
  begin
    induction x with x ih,
    { refl },
    { change one * x + one = x.succ,
      rw ih, refl }
  end

  @[simp]
  theorem mul_one :
    x * one = x
  :=
  begin
    change zero + x = x,
    exact zero_add x,
  end

  @[simp]
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

section
  variables (x y z : ℕ)

  theorem add_right_cancel :
    x + z = y + z → x = y
  :=
  begin
    induction z with z ih,
    { exact id },
    { intros h,
      have h' := succ.inj h,
      exact ih h' }
  end

  lemma add_left_cancel : z + x = z + y → x = y :=
    by { rw [add_comm z x, add_comm z y], exact add_right_cancel _ _ _ }

  lemma zero_of_add_right_eq_self :
    x + y = x → y = 0
  :=
  begin
    intros h,
    exact add_left_cancel _ _ x h
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
    z ≠ zero → x * z = y * z → x = y
  :=
  begin
    cases z with z',
    { intros h, exfalso, exact h rfl },
    intros _ h,
    induction x with x ih generalizing y,
    { rw zero_mul at h,
      change zero = y * z' + y at h,
      cases y with y, { refl }, { injections }},
    { rw succ_mul at h,
      cases y with y',
      { rw zero_mul at h,
        change (x * z'.succ + z').succ = zero at h,
        injections },
      { rw succ_mul at h,
        have h' := add_right_cancel _ _ _ h,
        rw (ih y' h') }}
  end

  lemma mul_left_cancel : z ≠ zero → z * x = z * y → x = y :=
    by { rw [mul_comm z x, mul_comm z y], exact mul_right_cancel _ _ _ }

end

section
  variables (x y z : ℕ)

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

  theorem le_total :
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
      change x + zero = x + (c + d) at hd,
      have hd' := eq.symm (add_left_cancel _ _ _ hd),
      cases (zero_of_add_zero _ _ hd') with hc₁ hd₁,
      rw hc₁ at hc,
      exact eq.symm hc },
    -- Trans
    { rintros x y z ⟨c, hc⟩ ⟨d, hd⟩,
      use c + d,
      rw [hd, hc, add_assoc] },
    -- Total
    { intros x y,
      induction y with y ih,
      { right, use x, rw zero_add },
      { rcases ih with ⟨c, hc⟩ | ⟨c, hc⟩,
        { left, use c.succ, rw hc, refl },
        { cases c with c',
          { left, use 1, rw hc, refl },
          { right, use c', rw hc, rw succ_add, refl }}}}
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

  theorem lt_trichotomy :
    x = y ∨ x < y ∨ y < x
  :=
  begin
    rcases le_total with ⟨_, _, _, htotal⟩,
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

end

end mynat


--------------------------------------------------------------------------------
-- # Integers






--------------------------------------------------------------------------------

end notes






