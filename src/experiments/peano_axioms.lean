constant N : Type

constant zero : N
noncomputable instance : has_zero N := ⟨zero⟩
constant ν : N → N
noncomputable instance : has_one N := ⟨ν 0⟩
constant ν_ne_0 : ∀ x : N, ν x ≠ 0
constant ν_inj : ∀ x y : N, ν x = ν y → x = y
constant induction : ∀(P : N → Prop), (P(0) → (∀x, P(x) → P(ν x)) → ∀x, P(x))

constant add : N → N → N
noncomputable instance : has_add N := ⟨add⟩
constant add_0 : ∀ x : N, x + 0 = x
constant add_ν : ∀ x y : N, x + (ν y) = ν (x + y)

constant mul : N → N → N
noncomputable instance : has_mul N := ⟨mul⟩
constant mul_0 : ∀ x : N, x * 0 = 0
constant mul_ν : ∀ x y : N, x * ν y = (x * y) + x

constant pow : N → N → N
noncomputable instance : has_pow N N := ⟨pow⟩
constant pow_0 : ∀ x : N, x ^ (0 : N) = ν 0
constant pow_ν : ∀ x y : N, x ^ ν y = x ^ y * x

--------------------------------------------------------------------------------

theorem add_comm : ∀(a b : N), a + b = b + a :=
begin
	intros a b,
	-- Induction on b:
	let statement := induction (λ(b : N), ∀(a : N), a + b = b + a),
	have base : ∀(a : N), a + 0 = 0 + a, {
		intros a,
		-- Induction on a:
		let statement₁ := induction (λ(a : N), a + 0 = 0 + a),
		have base₁ : (0 : N) + 0 = 0 + 0 := rfl,
		have step₁ : ∀(a : N), (a + 0 = 0 + a) → (ν a + 0 = 0 + ν a), {
			intros a ih₁,
			symmetry,
			calc 0 + ν a
					= ν (0 + a) : by rw add_ν
			... = ν (a + 0) : by rw ih₁
			... = ν a       : by rw add_0
			... = ν a + 0   : by rw add_0
		},
		exact (statement₁ base₁ step₁ a),
	},
	have step : ∀(b : N), (∀(a : N), a + b = b + a) → (∀(a : N), a + ν b = ν b + a), {
		intros b ih a,
		-- Induction on a:
		let statement₁ := induction (λ(a : N), a + ν b = ν b + a),
		have base₁ : 0 + ν b = ν b + 0, {
			calc 0 + ν b
					= ν (0 + b) : by rw add_ν
			... = ν (b + 0) : by rw ih
			... = ν b       : by rw add_0
			... = ν b + 0   : by rw add_0
		},
		have step₁ : ∀(a : N), (a + ν b = ν b + a) → (ν a + ν b = ν b + ν a), {
			intros a ih₁,
			calc ν a + ν b
					= ν (ν a + b) 	: by rw add_ν
			... = ν (b + ν a)	 	: by rw ih
			... = ν (ν (b + a)) : by rw add_ν
			... = ν (ν (a + b)) : by rw ih a
			... = ν (a + ν b) 	: by rw add_ν
			... = ν (ν b + a) 	: by rw ih₁
			... = ν b + ν a     : by rw add_ν
		},
		exact (statement₁ base₁ step₁ a),
	},
	exact (statement base step b a),
end
