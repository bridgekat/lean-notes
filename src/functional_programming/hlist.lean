-- Inductive family!
inductive vector (α : Type) : ℕ → Type
| vnil  :                           vector 0
| vcons : Π {n : ℕ}, α → vector n → vector n.succ

namespace vector

  def show_vector' {α : Type} [has_to_string α] : Π {n : ℕ}, vector α n → string
  | 0 vnil                     := ""
  | _ (vcons a vnil)           := to_string a
  | _ (vcons a rs@(vcons _ _)) := to_string a ++ ", " ++ show_vector' rs

  def show_vector {α : Type} {n : ℕ} [has_to_string α] : vector α n → string :=
    λ x, "(" ++ show_vector' x ++ ")"

  instance {α : Type} {n : ℕ} [has_to_string α] : has_to_string (vector α n) :=
    ⟨show_vector⟩

  def vec := vcons 1 (vcons 2 (vcons 3 vnil))
  #eval to_string vec

  -- `fin n`: a type that contains exactly `n` elements
  inductive fin : ℕ → Type
  | fzero : Π {n : ℕ},         fin n.succ
  | fsucc : Π {n : ℕ}, fin n → fin n.succ

  -- This is guaranteed to be exhaustive (the equation compiler could identify it!)
  -- See: https://leanprover.github.io/theorem_proving_in_lean/induction_and_recursion.html#dependent-pattern-matching
  def get_element {α : Type} : Π {n : ℕ}, vector α n → fin n → α
--  0 vnil         ...            := ...  -- no possible combination for the third parameter
--  0 vcons ...    ...            := ...  -- no possible combination for the third parameter
--  succ... vnil   ...            := ...  -- dependent type mismatch
  | _ (vcons x _)  fin.fzero      := x
  | _ (vcons _ xs) (fin.fsucc fn) := get_element xs fn

  local infix `!!!` : 50 := get_element

end vector


-- Heterogeneous list!
inductive hlist : list Type → Type 1
| nil  :                                               hlist []
| cons : Π {α : Type} {αs : list Type}, α → hlist αs → hlist (α :: αs)

namespace hlist

/-
  def head' {α : Type} {αs : list Type} : hlist (α :: αs) → α :=
    λ ls, @hlist.rec_on
      -- This motive says: given an empty hlist, we eliminate into `unit`;
      --   otherwise, we eliminate into `α` (the type of the first element).
      (λ ls _, @list.rec Type (λ _, Type) unit (λ α αs _, α) ls)
      -- Indices and the term
      (α :: αs) ls
      -- Empty case
      unit.star
      -- Nonempty case
      (λ α αs a as _, a)
-/

  def head' {α : Type} {αs : list Type} : hlist (α :: αs) → α
  | (cons a as) := a

  def tail' {α : Type} {αs : list Type} : hlist (α :: αs) → hlist αs
  | (cons a as) := as

  instance base : has_to_string (hlist []) :=
    ⟨λ ls, "[]"⟩

  instance step {α : Type} {αs : list Type} [has_to_string α] [has_to_string (hlist αs)] : has_to_string (hlist (α :: αs)) :=
    ⟨λ ls,
      match ls with
      | (cons a as) := to_string a ++ " : " ++ to_string as
      end⟩

  open native
  meta def example_list := cons "gg" (cons 233 (cons (1.2 : float) nil))
  #check example_list
  #eval to_string example_list

end hlist

