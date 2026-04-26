import Mathlib

-- ## 1. POSLOUPNOSTI (Omezenost)
def LowerBoundedSequence (a : ℕ → ℝ) := ∃ l : ℝ, ∀ n : ℕ, l ≤ a n
def UpperBoundedSequence (a : ℕ → ℝ) := ∃ u : ℝ, ∀ n : ℕ, a n ≤ u
def BoundedSequence (a : ℕ → ℝ) := ∃ K > 0, ∀ n : ℕ, |a n| ≤ K

-- ## 2. POSLOUPNOSTI (Monotonie)
def IncreasingSequence (a : ℕ → ℝ) := ∀ n : ℕ, a n ≤ a (n + 1)
def StrictlyIncreasingSequence (a : ℕ → ℝ) := ∀ n : ℕ, a n < a (n + 1)
def DecreasingSequence (a : ℕ → ℝ) := ∀ n : ℕ, a (n + 1) ≤ a n
def StrictlyDecreasingSequence (a : ℕ → ℝ) := ∀ n : ℕ, a (n + 1) < a n
def MonotonicSequence (a : ℕ → ℝ) := IncreasingSequence a ∨ DecreasingSequence a
def StrictlyMonotonicSequence (a : ℕ → ℝ) := StrictlyIncreasingSequence a ∨ StrictlyDecreasingSequence a
def StrictlyIncreasingSequenceN (k : ℕ → ℕ) := ∀ n : ℕ, k n < k (n + 1)

-- ## 3. PODPOSLOUPNOSTI
def Subsequence (a : ℕ → ℝ) (k : ℕ → ℕ) : ℕ → ℝ := a ∘ k

-- ## 4. SUPREMUM A INFIMUM
def IsSup (A : Set ℝ) (s : ℝ) : Prop := (∀ x ∈ A, x ≤ s) ∧ (∀ ε > 0, ∃ x ∈ A, s - ε < x)
def IsInf (A : Set ℝ) (i : ℝ) : Prop := (∀ x ∈ A, i ≤ x) ∧ (∀ ε > 0, ∃ x ∈ A, x < i + ε)

-- ## 5. KONVERGENCE POSLOUPNOSTÍ
def ConvergesTo (a : ℕ → ℝ) (q : ℝ) := ∀ ε > 0, ∃ n₀, ∀ n ≥ n₀, |a n - q| < ε
def Convergent (a : ℕ → ℝ) := ∃ q : ℝ, ConvergesTo a q
def CauchySequence (a : ℕ → ℝ) := ∀ ε > 0, ∃ n₀ : ℕ, ∀ n m : ℕ, (n > n₀ ∧ m > n₀) → |a n - a m| < ε

-- ## 6. MNOŽINY
def UpperBoundedSet (M : Set ℝ) : Prop := ∃ c : ℝ, ∀ m ∈ M, m ≤ c
def LowerBoundedSet (M : Set ℝ) : Prop := ∃ c : ℝ, ∀ m ∈ M, c ≤ m
def BoundedSet (M : Set ℝ) : Prop := ∃ c : ℝ, c > 0 ∧ ∀ m ∈ M, |m| ≤ c

-- ## 0. AXIOMY ÚPLNOSTI ℝ
def AxNIP : Prop :=
  ∀ l u : ℕ → ℝ, IncreasingSequence l → DecreasingSequence u → (∀ n : ℕ, l n ≤ u n) →
    ∃ s : ℝ, ∀ n, l n ≤ s ∧ s ≤ u n

def AxSup : Prop :=
  ∀ A : Set ℝ, A.Nonempty → UpperBoundedSet A → ∃! s : ℝ, IsSup A s

def AxMonoConv : Prop :=
  ∀ a : ℕ → ℝ, MonotonicSequence a → BoundedSequence a → Convergent a

def AxBW : Prop :=
  ∀ a : ℕ → ℝ, BoundedSequence a → ∃ k : ℕ → ℕ, StrictlyIncreasingSequenceN k ∧ Convergent (Subsequence a k)

def AxCauchyConv : Prop :=
  ∀ a : ℕ → ℝ, CauchySequence a ↔ Convergent a
