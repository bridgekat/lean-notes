import tactic
import .«2_1_part_ii_natural_numbers»

namespace notes

-- Add this line in the beginning of each file to override the default ℕ
local notation `ℕ` : 1024 := mynat

universe u

--------------------------------------------------------------------------------
-- Definitions

-- Definition of ℤ as a quotient type
def eq_as_myint : ℕ × ℕ → ℕ × ℕ → Prop :=
  λ ⟨a, b⟩ ⟨c, d⟩, a + d = c + b

def myint : Type :=
  @quot (ℕ × ℕ) eq_as_myint

-- Add this line in the beginning of each file to override the default ℤ
local notation `ℤ` : 1024 := myint

namespace myint

  protected def mk : ℕ × ℕ → ℤ :=
    quot.mk eq_as_myint

  #check ℤ
  #check (myint.mk (3, 4) : ℤ)
  -- #check (⟨3, 4⟩ : ℤ) -- invalid



end myint



--------------------------------------------------------------------------------

end notes
