import Mathlib

def Sequence := ℕ → ℝ

-- 1. POSLOUPNOSTI (Omezenost)
def LowerBoundedSequence (a : Sequence) := ∃ l : ℝ, ∀ n : ℕ, l ≤ a n
def UpperBoundedSequence (a : Sequence) := ∃ u : ℝ, ∀ n : ℕ, a n ≤ u
def BoundedSequence (a : Sequence) := ∃ K > 0, ∀ n : ℕ, |a n| ≤ K

-- 2. POSLOUPNOSTI (Monotonie)
def IncreasingSequence (a : Sequence) := ∀ n : ℕ, a n ≤ a (n + 1)
def StrictlyIncreasingSequence (a : Sequence) := ∀ n : ℕ, a n < a (n + 1)
def DecreasingSequence (a : Sequence) := ∀ n : ℕ, a (n + 1) ≤ a n
def StrictlyDecreasingSequence (a : Sequence) := ∀ n : ℕ, a (n + 1) < a n
def MonotonicSequence (a : Sequence) := IncreasingSequence a ∨ DecreasingSequence a
def StrictlyMonotonicSequence (a : Sequence) := StrictlyIncreasingSequence a ∨ StrictlyDecreasingSequence a
def StrictlyIncreasingSequenceN (k : ℕ → ℕ) := ∀ n : ℕ, k n < k (n + 1)

-- 3. PODPOSLOUPNOSTI
def Subsequence (a : Sequence) (k : ℕ → ℕ) : Sequence := a ∘ k
-- def Subsequence (a : Sequence) (k : ℕ → ℕ) : Sequence := λ n ↦ a (k n)

-- 4. SUPREMUM A INFIMUM
def IsSup (A : Set ℝ) (s : ℝ) : Prop := (∀ x ∈ A, x ≤ s) ∧ (∀ ε > 0, ∃ x ∈ A, s - ε < x)
def IsInf (A : Set ℝ) (i : ℝ) : Prop := (∀ x ∈ A, i ≤ x) ∧ (∀ ε > 0, ∃ x ∈ A, x < i + ε)

-- 5. KONVERGENCE POSLOUPNOSTÍu
def ConvergesTo (a : Sequence) (q : ℝ) := ∀ ε > 0, ∃ n₀, ∀ n ≥ n₀, |a n - q| < ε
def Convergent (a : Sequence) := ∃ q : ℝ, ConvergesTo a q
def Divergent (a : Sequence) := ¬Convergent a
def DivergentToInf (a : Sequence) := ∀ m > 0, ∃ n₀, ∀ n ≥ n₀, a n > m
def DivergentToNegInf (a : Sequence) := ∀ m < 0, ∃ n₀, ∀ n ≥ n₀, a n < m

def CauchySequence (a : Sequence) := ∀ ε > 0, ∃ n₀ : ℕ, ∀ n m : ℕ, (n > n₀ ∧ m > n₀) → |a n - a m| < ε

-- 6. ŘADY
def PartialSum (a : Sequence) (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n + 1), a k
def SeriesConvergesTo (a : Sequence) (s : ℝ) : Prop := ConvergesTo (PartialSum a) s
def SeriesConvergent (a : Sequence) : Prop := ∃ s : ℝ, SeriesConvergesTo a s

-- 7. TOPOLOGICKÉ VLASTNOSTI MNOŽIN
def CompactSet (M : Set ℝ) : Prop :=
  ∀ (a : Sequence), (∀ n : ℕ, a n ∈ M) →
  ∃ (k : ℕ → ℕ), StrictlyIncreasingSequenceN k ∧ ∃ l : ℝ, ConvergesTo (Subsequence a k) l ∧ l ∈ M

def ClosedSet (M : Set ℝ) : Prop :=
  ∀ (a : Sequence) (L : ℝ), (∀ n : ℕ, a n ∈ M) → ConvergesTo a L → L ∈ M

def UpperBoundedSet (M : Set ℝ) : Prop := ∃ c : ℝ, ∀ m ∈ M, m ≤ c
def LowerBoundedSet (M : Set ℝ) : Prop := ∃ c : ℝ, ∀ m ∈ M, c ≤ m
def BoundedSet (M : Set ℝ) : Prop := ∃ c : ℝ, c > 0 ∧ ∀ m ∈ M, |m| ≤ c

-- 8. LIMITY FUNKCÍ A SPOJITOST
def HeineLimitFunction (f : ℝ → ℝ) (x₀ : ℝ) (b : ℝ) :=
  ∀ (a : Sequence), (∀ n : ℕ, a n ≠ x₀) → ConvergesTo a x₀ → ConvergesTo (f ∘ a) b
def CauchyLimitFunction (f : ℝ → ℝ) (x₀ : ℝ) (b : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ (x : ℝ), (0 < |x - x₀| ∧ |x - x₀| < δ) → |f x - b| < ε

def FunctionContinuousAt (f : ℝ → ℝ) (x₀ : ℝ) := CauchyLimitFunction f x₀ (f x₀)
def FunctionContinuous (f : ℝ → ℝ) := ∀ x : ℝ, FunctionContinuousAt f x
def FunctionContinuousOnSet (M : Set ℝ) (f : ℝ → ℝ) := ∀ x ∈ M, FunctionContinuousAt f x
def FunctionBddOnSet (M : Set ℝ) (f : ℝ → ℝ) := ∃ K > 0, ∀ x ∈ M, |f x| ≤ K
