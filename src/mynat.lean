-- Definitions from the Natural Number Game

@[derive decidable_eq]
inductive mynat
| zero : mynat
| succ (n : mynat) : mynat

#check mynat.decidable_eq

namespace mynat
	instance : has_zero mynat := ⟨mynat.zero⟩
	theorem mynat_zero_eq_zero : mynat.zero = 0 := rfl

	def one : mynat := succ 0
	instance : has_one mynat := ⟨mynat.one⟩
	theorem one_eq_succ_zero : 1 = succ 0 := rfl

	lemma zero_ne_succ (m : mynat) : (0 : mynat) ≠ succ m := λ h, by cases h
	lemma succ_ne_zero (m : mynat) : succ m ≠ (0 : mynat) := λ h, by cases h
	lemma succ_inj (m n : mynat)  (h : succ m = succ n) : (m = n) := by cases h; refl

	-- Definition of "addition on the natural numbers"
	def add : mynat → mynat → mynat
		| m 0 := m
		| m (succ n) := succ (add m n)
	instance : has_add mynat := ⟨mynat.add⟩
	-- Notation a + b := add a b
	-- Numerals now work
	example : mynat := 37
	lemma add_zero (m : mynat) : m + 0 = m := rfl
	lemma add_succ (m n : mynat) : m + succ n = succ (m + n) := rfl

	-- Definition of "multiplication on the natural numbers"
	def mul : mynat → mynat → mynat
		| m zero := zero
		| m (succ n) := mul m n + m
	instance : has_mul mynat := ⟨mul⟩
	-- Notation a * b := mul a b
	example : (1 : mynat) * 1 = 1 := 
	begin
		refl,
	end
	lemma mul_zero (m : mynat) : m * 0 = 0 := rfl
	lemma mul_succ (m n : mynat) : m * (succ n) = m * n + m := rfl

	-- Definition of "power on the natural numbers"
	def pow : mynat → mynat → mynat
		| m zero := one
		| m (succ n) := pow m n * m
	instance : has_pow mynat mynat := ⟨pow⟩
	-- Notation a ^ b := pow a b
	example : (1 : mynat) ^ (1 : mynat) = 1 := 
	begin
		refl,
	end
	lemma pow_zero (m : mynat) : m ^ (0 : mynat) = 1 := rfl
	lemma pow_succ (m n : mynat) : m ^ (succ n) = m ^ n * m := rfl

	-- Definition of "less or equal than on the natural numbers"
	def le (a b : mynat) :=  ∃ (c : mynat), b = a + c
	-- Another choice is to define it recursively: 
	-- | le 0 _
	-- | le (succ a) (succ b) = le a b 
	-- Notation a ≤ b := le a b
	instance : has_le mynat := ⟨mynat.le⟩
	theorem le_def' : mynat.le = (≤) := rfl -- ???
	theorem le_iff_exists_add (a b : mynat) : a ≤ b ↔ ∃ (c : mynat), b = a + c := iff.rfl
end mynat

attribute [symm] ne.symm
