--(a)
lemma de_morgan_2 {p q : Prop} : (¬p ∧ ¬q) → ¬(p ∨ q) := by
-- by closing box [1-11]
  intro h
  have h_not_p := h.left,
  have h_not_q := h.right,
  have h1: p → False := by
-- by closing box [5-6]
  { intro hp,
    exact h_not_p hp },
  have h2: q → False := by
--  by closing box [7-8]
  { intro hq,
    exact h_not_q hq },
  intro h_or,
  apply Or.elim h_or h1 h2


--(b)
lemma de_morgan_3 {p q : Prop} : (¬p ∨ ¬q) → ¬(p ∧ q) := by 
-- by closing box [1-10]
  intro h,
  intro h_and,
  have hp := h_and.left,
  have hq := h_and.right,
-- by closing box [2-9]
  apply Or.elim h,
-- by closing box [5-6]
  { intro h_not_p,
    show False,
    apply h_not_p,
    exact hp },
--  by closing box [7-8]
  { intro h_not_q,
    show False,
    apply h_not_q,
    exact hq }

