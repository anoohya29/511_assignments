--(a)
  lemma de_morgan_2 {p q : Prop} : (¬p ∧ ¬q) → ¬(p ∨ q) :=  by 
  intro h
  have h_not_p := h.left,
  have h_not_q := h.right,
  have h1: p → False := by
  { intro h_p,
    exact h_not_p h_p },
    have h2: q → False := by
    { intro h_q,
  
    exact h_not_q h_q },
  intro h_or,
  apply Or.elim h_or h1 h2
--(b)
  lemma de_morgan_3 {p q : Prop} : (¬p ∨ ¬q) → ¬(p ∧ q) := by

  intro h_or
  have h1: ¬p → False := by
    { intro h_not_p,  --[5,6]
      intro h_and,
      exact h_not_p h_and.left },
  have h2: ¬q → False := by
  { intro h_not_q,    --[7-8]
    intro h_and,
    exact h_not_q h_and.right },
  intro h_and,
  apply Or.elim h_or h1 h2
