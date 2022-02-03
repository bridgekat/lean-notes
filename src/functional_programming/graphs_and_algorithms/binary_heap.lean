import data.int.basic
import data.list.basic
import tactic


inductive min_heap (α : Type) [linear_order α] : Type
| nil  :                           min_heap
| node : min_heap → α → min_heap → min_heap

namespace min_heap
  -- instance {α : Type} [linear_order α] : has_emptyc (min_heap α) := ⟨empty⟩

  structure nonempty {α : Type} [linear_order α] (h : min_heap α) :=
    mk :: (root : {a // ∃ l r, h = node l a r})

  section
    variables {α : Type}
    variables [inhabited α] [linear_order α]

    notation `∅` := min_heap.nil

    def all_nodes : min_heap α → list α
    | ∅            := []
    | (node l a r) := (all_nodes l) ++ [a] ++ (all_nodes r)

    def is_empty : min_heap α → bool
    | ∅ := tt
    | _ := ff

    def size : min_heap α → nat
    | ∅            := 0
    | (node l a r) := size l + 1 + size r

    def get_min : min_heap α → α
    | ∅            := default α
    | (node _ a _) := a

    def get_last : min_heap α → α
    | ∅            := default α
    | (node ∅ a ∅) := a
    | (node l a ∅) := get_last l
    | (node l a r) := get_last r

    def remove_last : min_heap α → min_heap α
    | ∅            := ∅
    | (node ∅ a ∅) := ∅
    | (node l a ∅) := node (remove_last l) a ∅
    | (node l a r) := node l a (remove_last r)

    lemma size_remove_last : ∀ h : min_heap α, h.remove_last.size = h.size - 1
    | ∅ := rfl
    | (node ∅ a ∅) := rfl
    | (node l a ∅) := by { sorry }
    | (node l a r) := by { sorry }

    def fix_min_heap : min_heap α → min_heap α
    | ∅ := ∅
    | (node ∅ a ∅) := node ∅ a ∅
    | (node (node l₁ a₁ r₁) a ∅) :=
      if a₁ < a then node (fix_min_heap $ node l₁ a r₁) a₁ ∅
      else           node (node l₁ a₁ r₁) a ∅
    | (node ∅ a (node l₂ a₂ r₂)) :=
      if a₂ < a then node ∅ a₂ (fix_min_heap $ node l₂ a r₂)
      else           node ∅ a (node l₂ a₂ r₂)
    | (node (node l₁ a₁ r₁) a (node l₂ a₂ r₂)) :=
      if      a₁ < a then node (fix_min_heap $ node l₁ a r₁) a₁ (node l₂ a₂ r₂)
      else if a₂ < a then node (node l₁ a₁ r₁) a₂ (fix_min_heap $ node l₂ a r₂)
      else                node (node l₁ a₁ r₁) a (node l₂ a₂ r₂)

    lemma size_fix_min_heap : ∀ h : min_heap α, h.fix_min_heap.size = h.size
    | ∅ := by { unfold fix_min_heap }
    | (node ∅ a ∅) := by { unfold fix_min_heap }
    | (node (node l₁ a₁ r₁) a ∅) := by
      { unfold fix_min_heap, sorry }
    | (node ∅ a (node l₂ a₂ r₂)) := by sorry
    | (node (node l₁ a₁ r₁) a (node l₂ a₂ r₂)) := by sorry

    def remove_min (h : min_heap α) : min_heap α :=
      let ⟨last, h'⟩ := (get_last h, remove_last h) in
        match h' with
        | ∅            := node ∅ last ∅
        | (node l a r) := fix_min_heap $ node l last r
        end

    lemma size_remove_min : ∀ h : min_heap α, h.remove_min.size = h.size - 1 := sorry

    def init_min_heap : min_heap α → min_heap α
    | ∅ := ∅
    | (node l a r) := fix_min_heap $ node (init_min_heap l) a (init_min_heap r)
    
    open nat

    -- Greatest integer power of 2 less or equal than n
    def gpow2 : nat → nat
    | 0 := 0
    | 1 := 1
    | (succ (succ a)) :=
      have a / 2 + 1 < a + 2 := succ_lt_succ_iff.mpr (lt_succ_of_le (nat.div_le_self a 2)),
      gpow2 (a / 2 + 1) * 2

    lemma gpow2_le : ∀ n : nat, gpow2 n ≤ n
    | 0 := by { unfold gpow2 }
    | 1 := by { unfold gpow2 }
    | (succ (succ a)) :=
      have a / 2 + 1 < a + 2 := succ_lt_succ_iff.mpr (lt_succ_of_le (nat.div_le_self a 2)),
      have ih : gpow2 (a / 2 + 1) ≤ a / 2 + 1 :=
      by { exact gpow2_le (a / 2 + 1) },
      by { unfold gpow2,
           suffices : (a / 2 + 1) * 2 ≤ a + 2,
           { have h := mul_le_mul_right' (gpow2_le (a / 2 + 1)) 2,
             exact le_trans h this },
           rw [add_mul, one_mul],
           apply lt_succ_of_le,
           apply lt_succ_of_le,
           exact div_mul_le_self a 2 }
    
    lemma zero_lt_gpow2 : ∀ n : nat, 0 < n → 0 < gpow2 n
    | 0 := by { unfold gpow2, exact id }
    | 1 := by { unfold gpow2, exact id }
    | (succ (succ a)) := λ _,
      have a / 2 + 1 < a + 2 := succ_lt_succ_iff.mpr (lt_succ_of_le (nat.div_le_self a 2)),
      have ih : 0 < gpow2 (a / 2 + 1) :=
      by { exact zero_lt_gpow2 (a / 2 + 1) (zero_lt_succ _), },
      by { unfold gpow2,
           rw mul_two, exact add_pos ih ih }

    open list

    def from_list : list α → min_heap α
    | [] := ∅
    | [a] := node ∅ a ∅
    | ls'@(a :: (b :: ls)) :=
      let l := gpow2 (length ls' - 1) in
      have h₁ : l - 1 < ls'.length := by
      { have := gpow2_le (length (a :: b :: ls) - 1),
        replace this : l - 1 ≤ length ls := sub_le_sub_right' this 1,
        apply lt_succ_of_le,
        exact le_trans this (le_succ (length ls)) },
      have h₂ : length ls' - gpow2 (length ls' - 1) < length ls' := by
      { suffices : 0 < gpow2 (length ls + 1), { exact nat.sub_lt (pos_of_gt h₁) this },
        exact zero_lt_gpow2 (length ls + 1) (zero_lt_succ _) },
      node (from_list $ take (l - 1) ls') (ls'.nth_le (l - 1) h₁) (from_list $ drop l ls')
    using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf length⟩]}

  end

end min_heap


-- Heapsort
section
  variables {α : Type}
  variables [inhabited α] [linear_order α]

  def extract_heap : min_heap α → list α
  | min_heap.nil := []
  | hp@(min_heap.node l a r) :=
    let ⟨min, h⟩ := (hp.get_min, hp.remove_min) in
      have h.size < (l.node a r).size := by { sorry },
        min :: extract_heap h
  using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf min_heap.size⟩]}

  def heapsort (ls : list α) : list α :=
    extract_heap (min_heap.from_list ls)

end



