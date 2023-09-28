
import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

--4(a) 

example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, ht⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have ht' : 0 < (-x) * t := by addarith [ht]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at ht'
    apply ne_of_gt
    apply ht'
  · have ht' : 0 < x * (-t) := by calc
      x * (-t) = (-x) * t := by ring
      _ > 0 := by addarith [ht] 
    have hx' : 0 ≤ x := by addarith [hx]
    cancel x at ht'
    apply ne_of_lt
    addarith [ht']

--4(b)

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a+1, a
  ring 

--4(c)
  
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q)/2
  constructor 
  calc
    p = ( p+ p)/2 := by ring 
    _ < (p + q)/2 := by rel[h]
  calc 
    q = ( q+ q)/2 := by ring 
    _ > (p + q )/2 := by rel[h]

--5(a)

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hx2: -x ≥ 0 := by addarith [hx]
    use x - 1
    calc
      (x - 1) ^ 2  = x ^ 2 - 2 * x + 1 := by ring
      _ = -x * -x - 2 * x + 1 := by ring
      _ ≥ 0 * -x - 2 * x + 1 := by rel [hx2]
      _ = -2 * x + 1 := by ring
      _ > -2 * x := by extra
      _ = -x + -x := by ring
      _ ≥ 0 + 0 := by rel [hx2]
      _ = 0 := by numbers
      _ ≥ x := by addarith[hx]
  . use x + 1
    calc 
      (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by ring
      _ = x * x + 2 * x + 1 := by ring
      _ ≥ 0 * x + 2 * x + 1 := by rel[hx]
      _ = 2 * x + 1 := by ring
      _ > 2 * x := by extra
      _ = x + x := by ring
      _ ≥ x + 0 := by rel[hx]
      _ = x := by ring
  
--5(b)

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨x , hx1⟩ := h
  intro ht
  rw [ht]at hx1
  apply ne_of_lt hx1
  ring 

--5(c)

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨x, hxm⟩ := h
  intro hm
  rw [hm] at hxm
  have H := le_or_gt x 2
  obtain hx | hx := H
  · have := calc
      5 = 2 * x := by rw [hxm]
      _ ≤ 2 * 2 := by rel [hx]
      _ = 4 := by numbers
    contradiction
  . have hx1: x ≥ 3 := by addarith[hx]
    have := calc
      5 = 2 * x := by rw [hxm]
      _ ≥ 2 * 3 := by rel [hx1]
      _ = 6 := by numbers
    contradiction
