-- See: https://leanprover.github.io/logic_and_proof/first_order_logic_in_lean.html

constant Person : Type
  -- Domain of discourse

constant Loves : Person → Person → Prop
  -- (Loves a b) means "a loves b"

constant BetterThan : Person → Person → Person → Prop
  -- (BetterThan a b c) means "a thinks that b is better than c"

constant QZR : Person
  -- Me.

axiom exclusiveness :
  ∀(x y : Person), Loves x y → (∀z : Person, z ≠ y → ¬(Loves x z))
  -- Exclusiveness: Everyone loves at most one person.

axiom preference :
  ∀(x y z : Person), BetterThan x y z → (Loves x z → Loves x y)
  -- Preference: if x thinks that y is better than z,
  --             that means x will also fall in love with y if x appreciates z.

axiom shadowing :
  ∃y : Person, (y ≠ QZR ∧ (∀x : Person, BetterThan x y QZR))
  -- Shadowing: there is someone who is better than QZR in everyone's eyes.

theorem no_one_loves_QZR : ¬(∃x : Person, Loves x QZR) :=
begin
  intros hx,
  cases hx with x hx,
  cases shadowing with y hy,
  cases hy with hy₁ hy₂,
  specialize hy₂ x,
  have hnxy : ¬Loves x y, {
    have hx₁ := (exclusiveness x QZR) hx,
    specialize hx₁ y,
    exact hx₁ hy₁,
  },
  have hxy : Loves x y, {
    have hy₃ := (preference x y QZR) hy₂ hx,
    exact hy₃,
  },
  exact hnxy hxy,
end
