import Mathlib.Data.Nat.Basic

def double (n : ℕ) : ℕ := 2 * n

theorem double_add (a b : ℕ) : double (a + b) = double a + double b := by
  simp [double]
  rw [Nat.mul_add]

#check double_add
