/-
# Formalising IUM 2021 in Lean (unofficial version)

Things about the logical foundations of Lean are skipped here...
(I just assumed the basic knowledge of "universes", "Π types", "inductive types" and their "recursors",
 also you need to know about how the logical connectives, the naturals and equality are defined in Lean...)
(For them you may want to read *Theorem Proving in Lean*:
 https://leanprover.github.io/theorem_proving_in_lean/
 I also made some notes about that...)
-/

import tactic

universe u

--------------------------------------------------------------------------------
-- ## Using sets in Lean

namespace using_sets_in_lean

#print set
/-
In Lean, the `set` is a "type constructor":
  `def set : Type u → Type u :=`
  `  λ (α : Type u), α → Prop`
"A set on a type α" (`set α`) is just the type `α → Prop`!

Note that:
1. This is a function type, which contains all "predicates on `α`"
    (i.e. function that receives an element of `α` and returns a `Prop`).
2. This function type lives in the same universe as `α`.
-/

#check set ℕ
#reduce set ℕ -- `set ℕ` and `ℕ → Prop` are the same (definitionally equal)!

-- This is the set {0, 1, 12}.
def some_subset : set ℕ := λ n, n = 0 ∨ n = 1 ∨ n = 12
-- You can also define it as:
-- `def some_subset : ℕ → Prop := λ n, n = 0 ∨ n = 1 ∨ n = 12`

#print notation ∈
#print set.mem
/-
The `mem` is defined as:
  `def set.mem : Π {α : Type u} (a : α) (s : set α), Prop :=`
    `λ α a s, s a`
which is just a function that "takes an implicit `α : Type`,
  an element of `a`, and a "set" `s` on `α` (i.e. `s : α → Prop`),
  and returns the proposition obtained by putting `a` into the predicate `s`."
  (i.e. it is just an application of the predicate `s` on `a`!)
-/

#check (set.mem 4 some_subset) -- `Prop`
#check (4 ∈ some_subset) -- An alternative notation for the above line
#check (some_subset 4) -- An alternative notation for the above line!

#reduce (4 ∈ some_subset) -- `4 = 0 ∨ 4 = 1 ∨ 4 = 12`

-- Let's prove that 1 ∈ {0, 1, 12}...
lemma l1 : (1 ∈ some_subset) :=
begin
  unfold some_subset,
  right, left, refl,
end
-- (Term mode version)
example : (1 ∈ some_subset) := or.inr (or.inl rfl)

-- Now prove that 4 ∉ {0, 1, 12}...
example : (4 ∉ some_subset) :=
begin
  intros h,
  unfold some_subset at h,
  cases h with h₁ h₂,
  { injection h₁ },
  { cases h₂ with h₂ h₃,
    { injections },
    { injections }}
end
-- (Term mode version)
example : (4 ∉ some_subset) :=
  (λ h : (some_subset 4), h.elim
    (λ h, nat.no_confusion h)
    (λ h, h.elim
      (λ h, nat.no_confusion (nat.succ.inj h))
      (λ h, nat.no_confusion ((nat.succ.inj ∘ nat.succ.inj ∘ nat.succ.inj ∘ nat.succ.inj) h))))

#print notation ⊆
#print set.subset
/-
In Lean, the `subset` takes two `set`s and emits a `Prop`:
  `def set.subset : Π {α : Type u}, set α → set α → Prop :=`
  `  λ α s₁ s₂, (∀ (a : α), a ∈ s₁ → a ∈ s₂)`
-/

#print set.univ
#print notation ∅
#print set.has_emptyc -- TODO: typeclasses
/-
In Lean, the `univ` emits a `set` (α is implicit):
  `def set.univ : Π {α : Type u}, set α :=`
  `  λ α, (λ a, true)`
-/

#reduce (some_subset ⊆ (set.univ : set ℕ))
-- `∀ (a : ℕ), (a = 0 ∨ a = 1 ∨ a = 12) → true`
example : some_subset ⊆ (set.univ : set ℕ) :=
  λ x (hx : some_subset x), trivial

-- TODO: intersection, union, complement
-- TODO: indexed intersection / union
-- TODO: extensionality of sets
-- https://leanprover.github.io/logic_and_proof/sets_in_lean.html

end using_sets_in_lean


--------------------------------------------------------------------------------
-- ## Using functions in Lean

-- TODO: complete



