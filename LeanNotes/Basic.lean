-- My "hello, world" in Lean 4.
-- Here "love" refers to romantic attraction only.

/-- Domain of discourse. -/
axiom Person : Type

/-- `loves a b` means "a loves b". -/
axiom loves : Person → Person → Prop

/-- `prefers a b c` means "a thinks that b is better than c". -/
axiom prefers : Person → Person → Person → Prop

/-- Me. -/
axiom qzr : Person

/-- Everyone loves at most one person.  -/
axiom exclusiveness : ∀ x y, loves x y → ∀ z, z ≠ y → ¬loves x z

/-- If x thinks that y is better than z,
this means x will also fall in love with y if x appreciates z. -/
axiom preference : ∀ x y z, prefers x y z → loves x z → loves x y

/-- There is someone who is better than qzr in everyone's eyes. -/
axiom shadowing : ∃ y, y ≠ qzr ∧ ∀ x, prefers x y qzr

theorem no_one_loves_qzr : ¬∃ x, loves x qzr := by
  intros hx
  have ⟨x, hx⟩ := hx
  have ⟨y, hy⟩ := shadowing
  have ⟨hy₁, hy₂⟩ := hy
  specialize hy₂ x
  have hnxy : ¬loves x y := by
    have hx₁ := exclusiveness x qzr hx
    specialize hx₁ y
    exact hx₁ hy₁
  have hxy : loves x y := by
    have hy₃ := preference x y qzr hy₂ hx
    exact hy₃
  exact hnxy hxy

theorem no_one_loves_qzr' : ¬∃ x, loves x qzr :=
  fun ⟨x, hx⟩ =>
    let ⟨z, hz₁, hz₂⟩ := shadowing;
      exclusiveness x qzr hx z hz₁ (preference x z qzr (hz₂ x) hx)

/-- ??? -/
axiom yxy : Person

/-- ??? -/
axiom impossible : loves yxy qzr

/-- ??? -/
theorem contradiction : False :=
  no_one_loves_qzr' ⟨yxy, impossible⟩
