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

-- overeni zda s (i) je sup (inf)
def IsSup (a : ℕ → ℝ) (s : ℝ) : Prop := ∀ x ∈ (Set.range a), x ≤ s ∧ ∀ ε > 0, ∃ x ∈ (Set.range a), s - ε < x
def IsInf (a : ℕ → ℝ) (i : ℝ) : Prop := ∀ x ∈ (Set.range a), i ≤ x ∧ ∀ ε > 0, ∃ x ∈ (Set.range a), x < i + ε

-- supremum a infimum posloupnosti
noncomputable def SupSeq (a : ℕ → ℝ) (h_low_bdd : LowerBoundedSequence a) : ℝ :=
  Classical.choose (exists_unique_supremum a h_low_bdd)
noncomputable def InfSeq (a : ℕ → ℝ) (h_upp_bdd : LowerBoundedSequence a) : ℝ :=
  Classical.choose (exists_unique_infimum a h_upp_bdd)

-- exsitence a jednoznacnost suprema (infima)
theorem exists_unique_supremum (a : ℕ → ℝ) : ∃! s : ℝ, IsSup a s := by
  sorry

theorem exists_unique_infimum (a : ℕ → ℝ) : ∃! i : ℝ, IsInf a i := by
  sorry

-- konvergence a n → q
def ConvergentTo (a : ℕ → ℝ) (q : ℝ) := ∀ ε > 0, ∃ n₀ : ℕ, ∀ n > n₀, |a n - q| < ε
def Convergent (a : ℕ → ℝ) := ∃ q : ℝ, ConvergentTo a q
