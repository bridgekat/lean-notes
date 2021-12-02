import tactic
noncomputable theory

namespace notes

universe u

--------------------------------------------------------------------------------
-- Definitions from the Natural Number Game

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
  def le (a b : mynat) : Prop :=
    ∃ (c : mynat), b = a + c
  -- Another choice is to define it recursively: 
  -- | le 0 _               := true
  -- | le (succ a) (succ b) := le a b
  instance : has_le mynat := ⟨mynat.le⟩

end mynat

local notation `ℕ` : 1024 := mynat

--------------------------------------------------------------------------------
-- # Natural Numbers

namespace mynat

section
  variables {x y z : ℕ}

  theorem add_assoc :
    (x + y) + z = x + (y + z)
  :=
  begin
    induction z with z ih,
    { refl },
    { change (x + y + z).succ = (x + (y + z)).succ,
      rw ih }
  end

  theorem zero_add :
    zero + x = x
  :=
  begin
    induction x with x ih,
    { refl },
    { change (zero + x).succ = x.succ,
      rw ih, }
  end

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
        rw ihy } }
  end

  theorem add_mul :
    (x + y) * z = x * z + y * z
  :=
  begin
    induction z with z ih,
    { refl },
    { change (x + y) * z + (x + y) = (x * z + x) + (y * z + y),
      rw ih,
      sorry /- TODO: "simp normal forms" -/ }
  end

-- TODO: complete the proofs

end

end mynat


--------------------------------------------------------------------------------
-- # Integers






--------------------------------------------------------------------------------

end notes
