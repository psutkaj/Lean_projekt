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

-- supremum a infimum posloupnosti
  -- noncomputable, protoze LEAN ho primo nepocita, jenom vi, ze existuje, je jednoznacny a bere ho tak
  -- vlastnosti jsou jiz dokazane z knihoven
noncomputable def SupSequence (a : ℕ → ℝ) (_h_bdd : BddAbove (Set.range a)) : ℝ := sSup (Set.range a)
noncomputable def InfSequence (a : ℕ → ℝ) (_h_bdd : BddBelow (Set.range a)) : ℝ := sInf (Set.range a)

-- overeni zda s (i) je sup (inf)
def IsSup (a : ℕ → ℝ) (s : ℝ) : Prop := ∀ x ∈ (Set.range a), x ≤ s ∧ ∀ ε > 0, ∃ x ∈ (Set.range a), s - ε < x
def IsInf (a : ℕ → ℝ) (i : ℝ) : Prop := ∀ x ∈ (Set.range a), i ≤ x ∧ ∀ ε > 0, ∃ x ∈ (Set.range a), x < i + ε

-- konvergence a n → q
def ConvergentTo (a : ℕ → ℝ) (q : ℝ) := ∀ ε > 0, ∃ n₀ : ℕ, ∀ n > n₀, |a n - q| < ε
def Convergent (a : ℕ → ℝ) := ∃ q : ℝ, ConvergentTo a q
