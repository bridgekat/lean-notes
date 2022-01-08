import tactic

namespace notes

universe u
variables {X Y Z : Type u}

--------------------------------------------------------------------------------
-- # Functions

section
  example (f : X → Y) (g : X → Y) :
-- Proposition. (Extensionality of Functions)
    f = g ↔ (∀ x : X, f x = g x)
-- Note that in Lean it follows from an axiom (`funext`).
-- Proof.
    :=
  begin
    split,
    { intros h, rw h, exact (λ x, rfl), },
    { intros h, funext, exact h x, },
  end
-- ∎
end

section
-- Definitions.
  def injective (f : X → Y) : Prop :=
    ∀ (a b : X), f a = f b → a = b
  def surjective (f : X → Y) : Prop :=
    ∀ y : Y, ∃ x : X, f x = y
  def bijective (f : X → Y) : Prop :=
    injective f ∧ surjective f
end

section
  variables {f : X → Y} {g : Y → Z}

  theorem composition_inj_of_inj :
-- Theorem.
    injective f → injective g → injective (g ∘ f)
-- Proof.
  :=
  begin
    unfold injective at *,
    intros hf hg a b h,
    unfold function.comp at *,
    apply hf,
    apply (hg (f a) (f b)),
    exact h,
  end
-- ∎

  theorem composition_surj_of_surj :
-- Theorem.
    surjective f → surjective g → surjective (g ∘ f)
-- Proof.
  :=
  begin
    unfold surjective at *,
    intros hf hg z,
    unfold function.comp at *,
    cases (hg z) with y hy,
    cases (hf y) with x hx,
    use x,
    rw [hx, hy],
  end
-- ∎

  theorem composition_bij_of_bij :
-- Theorem.
    bijective f → bijective g → bijective (g ∘ f)
-- Proof.
  :=
  begin
    unfold bijective at *,
    rintros ⟨hf_inj, hf_surj⟩ ⟨hg_inj, hg_surj⟩,
    exact ⟨composition_inj_of_inj hf_inj hg_inj, composition_surj_of_surj hf_surj hg_surj⟩,
  end
-- ∎

  theorem inj_of_composition_inj :
-- Theorem.
    injective (g ∘ f) → injective f
-- Proof.
  :=
  begin
    unfold injective at *,
    intros h_inj a b h,
    apply h_inj,
    unfold function.comp,
    rw h,
  end
-- ∎

  theorem surj_of_composition_surj :
-- Theorem.
    surjective (g ∘ f) → surjective g
-- Proof.
  :=
  begin
    unfold surjective at *,
    intros h z,
    cases (h z) with x hx,
    use (f x),
    exact hx,
  end
-- ∎
end

section
-- Definition.
  def are_inverse (f : X → Y) (g : Y → X) : Prop :=
    (∀ x : X, g (f x) = x) ∧ (∀ y : Y, f (g y) = y)

  lemma are_inverse.symm (f : X → Y) (g : Y → X) :
-- Corollary.
    are_inverse f g ↔ are_inverse g f
-- Proof.
  :=
  begin
    unfold are_inverse,
    split,
    { rintros ⟨hgf, hfg⟩, exact ⟨hfg, hgf⟩, },
    { rintros ⟨hfg, hgf⟩, exact ⟨hgf, hfg⟩, },
  end
-- ∎
end

section
  open classical

  theorem has_inverse_iff_bij (f : X → Y) :
-- Theorem.
    bijective f ↔ (∃ g : Y → X, are_inverse f g)
-- Proof.
  :=
  begin
    split,
    { rintros ⟨hf_inj, hf_surj⟩,
      let g : Y → X := (λ y, some (hf_surj y)),
      use g,
      split,
      { intros x,
        have hgy := some_spec (hf_surj (f x)),
        have hgy' := hf_inj _ _ hgy,
        exact hgy', },
      { intros y,
        have hgy := some_spec (hf_surj y),
        exact hgy, } },
    { rintros ⟨g, ⟨hgf, hfg⟩⟩,
      split,
      { intros a b h,
        rw [← hgf a, h, hgf b], },
      { intros y,
        use (g y),
        exact (hfg y), } },
  end
-- ∎
end

--------------------------------------------------------------------------------
-- # Relations

section
  variable r : X → X → Prop
-- Definitions.
  def reflexive : Prop :=
    ∀ (a : X), r a a
  def symmetric : Prop :=
    ∀ {a b : X}, r a b → r b a
  def antisymmetric : Prop :=
    ∀ {a b : X}, r a b → r b a → a = b
  def transitive : Prop :=
    ∀ {a b c : X}, r a b → r b c → r a c
  def total : Prop :=
    ∀ (a b : X), r a b ∨ r b a
end

section
  variable r : X → X → Prop
-- Definitions.
  def is_partial_order : Prop :=
    reflexive r ∧ antisymmetric r ∧ transitive r
  def is_total_order : Prop :=
    reflexive r ∧ antisymmetric r ∧ transitive r ∧ total r
  def is_equivalence_relation : Prop :=
    reflexive r ∧ symmetric r ∧ transitive r
end

section
  variables (r : X → X → Prop)
-- Definition.
  def cl (hr : is_equivalence_relation r) (s : X) : set X :=
    (λ x, r s x)
end

section
  variables (r : X → X → Prop) (hr : is_equivalence_relation r)
  local notation `cl` := cl r hr

  lemma cl.eq_of_equiv {a b : X} :
-- Lemma.
    r a b → cl a = cl b
-- Proof.
  :=
  begin
    rcases hr with ⟨hrefl, hsymm, htrans⟩,
    unfold «cl»,
    intros hr,
    ext, split,
    { intros hax, exact (htrans (hsymm hr) hax), },
    { intros hbx, exact (htrans hr hbx), },
  end
-- ∎

  lemma cl.disjoint_of_not_equiv {a b : X} :
-- Lemma.
    ¬(r a b) → cl a ∩ cl b = ∅
-- Proof.
  :=
  begin
    rcases hr with ⟨hrefl, hsymm, htrans⟩,
    unfold «cl» at *,
    intros h,
    ext, split,
    { rintros ⟨hax, hbx⟩, exact h (htrans hax (hsymm hbx)), },
    { intros hf, exfalso, exact hf, },
  end
end
-- ∎

section
-- Definition.
  def is_partition (A : set (set X)) : Prop :=
    ∀ x : X, ∃! a, a ∈ A ∧ x ∈ a
end

section
  variables (r : X → X → Prop) (hr : is_equivalence_relation r)
  local notation `cl` := cl r hr

  theorem partition_from_equiv :
-- Theorem.
    is_partition (λ s, ∃ x : X, s = cl x)
-- Proof.
  :=
  begin
    have hr' := hr,
    rcases hr' with ⟨hrefl, hsymm, htrans⟩,
    intros x,
    use (cl x), split,                 -- Claim: `x` is only in `cl x`
    { exact ⟨⟨x, rfl⟩, hrefl x⟩, },    -- By definition, `x` is in `cl x`
    { unfold «cl»,
      rintros a ⟨⟨z, ha⟩, hx : (a x)⟩,
      ext y, split,                    -- Assume that `x` is also in `y`
      { intros hy,
        rw ha at *,
        exact htrans (hsymm hx) hy, }, -- Then anything in `y` must be in `cl x`
      { intros hxy,
        rw ha at *,
        exact htrans hx hxy, } },      -- And anything in `cl x` must be in `y`
  end
-- ∎

  private theorem partition_equiv_eq_self {f : X → set X} {rf : X → X → Prop}
-- Theorem.
    (hf : ∀ a : X, f a = cl a) (hrf : ∀ a b : X, rf a b ↔ f a = f b) :
    rf = r
-- Proof.
  :=
  begin
    rcases hr with ⟨hrefl, hsymm, htrans⟩,
    unfold «cl» at *,
    ext x y, split,
    { intros hxy,
      have h := (hrf x y).mp hxy,
      rw [hf, hf] at h,
      have h' : r y y → r x y,
      { change (λ (x : X), r y x) y → r x y,
        rw ← h,
        exact id, },
      exact h' (hrefl y), },
    { intros hxy,
      have h : f x = f y,
      { rw [hf, hf],
        ext, split,
        { intros h, exact htrans (hsymm hxy) h, },
        { intros h, exact htrans hxy h, }, },
      exact (hrf x y).mpr h, },
  end
-- ∎
end

--------------------------------------------------------------------------------

end notes
