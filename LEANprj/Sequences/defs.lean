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

-- zavedu jako axiom uplnosti Realnych cisel
axiom exists_point_in_nested_intervals
  (l u : ℕ → ℝ)
  (inc_l : IncreasingSequence l)
  (dec_u : DecreasingSequence u)
  (sep : ∀ n, l n ≤ u n)
  (shrink : ∀ n, u (n + 1) - l (n + 1) ≤ u n - l n) :
  ∃ s : ℝ, ∀ n, l n ≤ s ∧ s ≤ u n

lemma inc_le_of_le {a : ℕ → ℝ} (hinc : IncreasingSequence a) : ∀ {n m : ℕ}, n ≤ m → a n ≤ a m := by
  intro n m hnm
  refine Nat.le_induction (show a n ≤ a n from le_rfl) ?step m hnm
  intro k hk ih
  exact le_trans ih (hinc k)

lemma dec_le_of_le {a : ℕ → ℝ} (hdec : DecreasingSequence a) : ∀ {n m : ℕ}, n ≤ m → a n ≥ a m := by
  intro n m hnm
  refine Nat.le_induction (show a n ≥ a n from le_rfl) ?step m hnm
  intro k hk ih
  exact le_trans (hdec k) ih

-- podposloupnost posloupnosi a s indexovou fci k
def Subsequence (a : ℕ → ℝ) (k : ℕ → ℕ) : ℕ → ℝ := λ n => a (k n)

-- overeni zda s (i) je sup (inf)
def IsSup (A : Set ℝ) (s : ℝ) : Prop := ∀ x ∈ A, x ≤ s ∧ ∀ ε > 0, ∃ x ∈ A, s - ε < x
def IsInf (A : Set ℝ) (i : ℝ) : Prop := ∀ x ∈ A, i ≤ x ∧ ∀ ε > 0, ∃ x ∈ A, x < i + ε

-- konvergence a n → q
def ConvergesTo (a : ℕ → ℝ) (q : ℝ) := ∀ ε > 0, ∃ n₀, ∀ n ≥ n₀, |a n - q| < ε
def Convergent (a : ℕ → ℝ) := ∃ q : ℝ, ConvergesTo a q

def CauchySequence (a : ℕ → ℝ) := ∀ ε > 0, ∃ n₀ : ℕ, ∀ n m : ℕ, n > n₀ ∧ m > n₀ → |a n - a m| < ε
