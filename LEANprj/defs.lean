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
def StrictlyIncreasingSequenceN (a : ℕ → ℕ) := ∀ n : ℕ, a (n + 1) > a n

-- zavedu jako axiom uplnosti Realnych cisel
axiom exists_point_in_nested_intervals
  (l u : ℕ → ℝ)
  (inc_l : IncreasingSequence l)
  (dec_u : DecreasingSequence u)
  (sep : ∀ n, l n ≤ u n)
  (shrink : ∀ n, u (n + 1) - l (n + 1) ≤ u n - l n) :
  ∃ s : ℝ, ∀ n, l n ≤ s ∧ s ≤ u n

lemma StrictlyIncreasingSequenceN_ge_id (k : ℕ → ℕ) (hk : StrictlyIncreasingSequenceN k) :
  ∀ n, k n ≥ n := by
  intro n
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have : k (n + 1) ≥ k n + 1 := Nat.succ_le_of_lt (hk n)
    calc
      k (n + 1) ≥ k n + 1 := this
      _ ≥ n + 1 := by linarith

lemma inc_lt_of_ltN (k : ℕ → ℕ) (hk_inc : StrictlyIncreasingSequenceN k) : ∀ {n m : ℕ}, n < m → k n < k m := by
    intro n m h
    induction m, h using Nat.le_induction with
    | base =>
      exact hk_inc n
    | succ m' _ ih =>
      exact Nat.lt_trans ih (hk_inc m')

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
def Divergent (a : ℕ → ℝ) := ¬Convergent a

def CauchySequence (a : ℕ → ℝ) := ∀ ε > 0, ∃ n₀ : ℕ, ∀ n m : ℕ, n > n₀ ∧ m > n₀ → |a n - a m| < ε

def PartialSum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n + 1), a k
def SeriesConvergesTo (a : ℕ → ℝ) (s : ℝ) : Prop := ConvergesTo (PartialSum a) s
def SeriesConvergent (a : ℕ → ℝ) : Prop := ∃ s : ℝ, SeriesConvergesTo a s

def CompactSet (M : Set ℝ) : Prop := ∀ (a : ℕ → ℝ), (∀ n : ℕ, a n ∈ M) → ∃ (k : ℕ → ℕ), StrictlyIncreasingSequenceN k ∧ ∃ l : ℝ, ConvergesTo (Subsequence a k) l ∧ l ∈ M
def ClosedSet (M : Set ℝ) : Prop := ∀ (a : ℕ → ℝ) (L : ℝ), (∀ n : ℕ, a n ∈ M) → ConvergesTo a L → L ∈ M
def BoundedSet (M : Set ℝ) : Prop := ∃ c : ℝ, c > 0 ∧ ∀ m ∈ M, |m| < c
