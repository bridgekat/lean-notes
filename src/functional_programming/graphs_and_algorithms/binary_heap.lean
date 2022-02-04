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
    variables [inhabited α] [linear_order α] [has_to_string α]

    notation `∅` := min_heap.nil

    def all_nodes : min_heap α → list α
    | ∅            := []
    | (node l a r) := (all_nodes l) ++ [a] ++ (all_nodes r)

    def print : min_heap α → string
    | ∅            := ""
    | (node l a r) := "(" ++ (print l) ++ " " ++ (to_string a) ++ " " ++ (print r) ++ ")"

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

    lemma size_remove_last (h : min_heap α) : h.remove_last.size = h.size - 1 := by
    { induction h with l a r hl hr,
      refl,
      cases l with l₁ a₁ r₁,
      { cases r with l₂ a₂ r₂,
        { simp [remove_last, size] },
        { simp [remove_last, size, hr], ring_nf } },
      { cases r with l₂ a₂ r₂,
        { simp [remove_last, size, hl], ring_nf },
        { simp [remove_last, size, hl, hr], ring_nf } } }

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
      if a₁ < a₂ then
      ( if a₁ < a then node (fix_min_heap $ node l₁ a r₁) a₁ (node l₂ a₂ r₂)
        else           node (node l₁ a₁ r₁) a (node l₂ a₂ r₂) )
      else
      ( if a₂ < a then node (node l₁ a₁ r₁) a₂ (fix_min_heap $ node l₂ a r₂)
        else           node (node l₁ a₁ r₁) a (node l₂ a₂ r₂) )

    lemma size_fix_min_heap : ∀ h : min_heap α, h.fix_min_heap.size = h.size
    | ∅ := by { simp [fix_min_heap, size] }
    | (node ∅ a ∅) := by { simp [fix_min_heap, size] }
    | (node (node l₁ a₁ r₁) a ∅) := by
      { simp [fix_min_heap, size], split_ifs;
        simp [fix_min_heap, size, size_fix_min_heap (node l₁ a r₁)] }
    | (node ∅ a (node l₂ a₂ r₂)) := by
      { simp [fix_min_heap, size], split_ifs;
        simp [fix_min_heap, size, size_fix_min_heap (node l₂ a r₂)] }
    | (node (node l₁ a₁ r₁) a (node l₂ a₂ r₂)) := by
      { simp [fix_min_heap, size], split_ifs;
        simp [fix_min_heap, size],
        { simp [fix_min_heap, size, size_fix_min_heap (node l₁ a r₁)] },
        { simp [fix_min_heap, size, size_fix_min_heap (node l₂ a r₂)] } }

    def remove_min : min_heap α → min_heap α
    | ∅              := ∅
    | h@(node l a r) := fix_min_heap ∘ remove_last $ node l (get_last h) r

    lemma size_remove_min : ∀ h : min_heap α, h.remove_min.size = h.size - 1 := by
    { intros h, induction h with l a r hl hr,
      { simp [size, remove_min, get_last, remove_last] },
      { simp [size, remove_min, get_last, remove_last, size_remove_last, size_fix_min_heap] } }

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
      let l := gpow2 (length ls') in
      have h₁ : gpow2 (length ls') - 1 < length ls' := by
      { have := gpow2_le (length (a :: b :: ls)),
        cases gpow2 (a :: b :: ls).length,
        { simp }, { exact this } },
      have h₂ : length ls' - gpow2 (length ls') < length ls' := by
      { suffices : 0 < gpow2 (length ls + 2), { refine nat.sub_lt _ this, simp },
        exact zero_lt_gpow2 (length ls + 2) (zero_lt_succ _) },
      node (from_list $ take (l - 1) ls') (ls'.nth_le (l - 1) h₁) (from_list $ drop l ls')
    using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf length⟩]}

  end

end min_heap


-- Heapsort
section
  variables {α : Type}
  variables [inhabited α] [linear_order α] [has_to_string α]

  def extract_heap : min_heap α → list α
  | min_heap.nil := []
  | hp@(min_heap.node l a r) :=
    have hp.remove_min.size < (l.node a r).size := by
    { have := min_heap.size_remove_min (min_heap.node l a r),
      simp [min_heap.size] at *,
      rw this, simp },
    hp.get_min :: extract_heap hp.remove_min
  using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf min_heap.size⟩]}

  def heapsort (ls : list α) : list α :=
    extract_heap ∘ min_heap.init_min_heap ∘ min_heap.from_list $ ls

  #eval heapsort $ [1, 4, 7, 4, 2, 1, 8, 9]

end



