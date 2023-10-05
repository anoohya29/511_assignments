
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use
import Mathlib.Data.Real.Basic


-- 4a
example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 7 * k + 1 
  calc
    7 * n - 4 = 7 * (2 * k + 1) - 4 := by rw [hk]
    _ = 2 * (7 * k + 1) + 1 := by ring
  
-- 4b
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  dsimp [Odd] 
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2*a*b + 3*b + a + 1
  calc 
    x*y + 2*y = (2*a + 1) * (2*b + 1) + 2* (2*b+1) := by rw [ha, hb]
    _ = 2*(2*a*b + 3*b + a + 1) + 1 := by ring


-- 4c
example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  obtain ⟨k, hk⟩ := hn
  use 2*k^2 + 2*k - 3
  calc
    n ^ 2 + 2 * n - 5 = (k+k)^2 + 2*(k+k) - 5 := by rw[hk]
    _ = 4 * k^2 + 4*k - 5 := by ring
    _ = 2 * (2* k^2 + 2*k - 3) + 1 := by ring


attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

open Int

--4d
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain hbc | hbc := Int.even_or_odd (b - c)
  . right
    right
    obtain ⟨x, hbc⟩ := hbc
    use x
    calc
      b - c = 2 * x := by rw[hbc]
      _ = x + x := by ring 
  . obtain hac | hac := Int.even_or_odd (a + c)
    . right
      left
      obtain ⟨x, hac⟩ := hac
      use x
      calc
        a + c = 2 * x := by rw[hac]
        _ = x + x := by ring
    . left
      obtain ⟨x, hac⟩ := hac
      obtain ⟨y, hbc⟩ := hbc
      use (x - y - c)
      calc
        a - b = (a+c) - (b-c) - 2 * c := by ring
        _ = (2 * x + 1) - (b - c) - 2 * c := by rw[hac]
        _ = (2 * x + 1) - (2 * y + 1) - 2 * c := by rw[hbc]
        _ = 2 * x - 2 * y - 2 * c := by ring
        _ = 2 * (x - y - c) := by ring
        _ = (x-y-c) + (x-y-c) := by ring
        _ = 2*(x-y-c)


