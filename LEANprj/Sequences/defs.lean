import Mathlib
open Classical

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

-- overeni zda s (i) je sup (inf)
def IsSup (A : Set ℝ) (s : ℝ) : Prop := ∀ x ∈ A, x ≤ s ∧ ∀ ε > 0, ∃ x ∈ A, s - ε < x
def IsInf (A : Set ℝ) (i : ℝ) : Prop := ∀ x ∈ A, i ≤ x ∧ ∀ ε > 0, ∃ x ∈ A, x < i + ε

-- konvergence a n → q
def ConvergesTo (a : ℕ → ℝ) (q : ℝ) := ∀ ε > 0, ∃ n₀ : ℕ, ∀ n > n₀, |a n - q| < ε
def Convergent (a : ℕ → ℝ) := ∃ q : ℝ, ConvergesTo a q
