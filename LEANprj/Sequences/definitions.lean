import Mathlib

-- omezenost
def LowerBoundedSequence (a : ℕ → ℝ) := ∃ l : ℝ, ∀ n : ℕ, a n > l
def UpperBoundedSequence (a : ℕ → ℝ) := ∃ u : ℝ, ∀ n : ℕ, a n < u
def BoundedSequence (a : ℕ → ℝ) := ∃ K > 0, ∀ n : ℕ, |a n| < K

-- monotonie
def IncreasingSequence (a : ℕ → ℝ) := ∀ n : ℕ, a (n + 1) ≥ a n
def StrictlyIncreasingSequence (a : ℕ → ℝ) := ∀ n : ℕ, a (n + 1) > a n
def DecreasingSequence (a : ℕ → ℝ) := ∀ n : ℕ, a (n + 1) ≤ a n
def StrictlyDecreasingSequence (a : ℕ → ℝ) := ∀ n : ℕ, a (n + 1) < a n
def MonotonicSequence (a : ℕ → ℝ) := IncreasingSequence a ∨ DecreasingSequence a
def StrictlyMonotonicSequence (a : ℕ → ℝ) := StrictlyIncreasingSequence a ∨ StrictlyDecreasingSequence a

-- podposloupnost posloupnosi a s indexovou fci k
def Subsequence (a : ℕ → ℝ) (k : ℕ → ℕ) (_hk : ∀ n : ℕ, k (n + 1) > k n) : ℕ → ℝ :=
  λ n => a (k n)

#eval Subsequence (λ n => n) (λ n => 2 * n) (by intro n; linarith) 3
