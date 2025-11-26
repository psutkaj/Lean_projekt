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

-- podposloupnost posloupnosi a s indexovou fci k
def Subsequence (a : ℕ → ℝ) (k : ℕ → ℕ) : ℕ → ℝ := λ n => a (k n)

-- overeni zda s (i) je sup (inf)
def IsSup (A : Set ℝ) (s : ℝ) : Prop := ∀ x ∈ A, x ≤ s ∧ ∀ ε > 0, ∃ x ∈ A, s - ε < x
def IsInf (A : Set ℝ) (i : ℝ) : Prop := ∀ x ∈ A, i ≤ x ∧ ∀ ε > 0, ∃ x ∈ A, x < i + ε

-- konvergence a n → q
def ConvergesTo (a : ℕ → ℝ) (q : ℝ) := ∀ ε > 0, ∃ n₀, ∀ n ≥ n₀, |a n - q| < ε
def Convergent (a : ℕ → ℝ) := ∃ q : ℝ, ConvergesTo a q
def Divergent (a : ℕ → ℝ) := ¬Convergent a
def DivergentToInf (a : ℕ → ℝ) := ∀ m > 0, ∃ n₀, ∀ n ≥ n₀, a n > m
def DivergentToNegInf (a : ℕ → ℝ) := ∀ m < 0, ∃ n₀, ∀ n ≥ n₀, a n < m

def CauchySequence (a : ℕ → ℝ) := ∀ ε > 0, ∃ n₀ : ℕ, ∀ n m : ℕ, n > n₀ ∧ m > n₀ → |a n - a m| < ε

def PartialSum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n + 1), a k
def SeriesConvergesTo (a : ℕ → ℝ) (s : ℝ) : Prop := ConvergesTo (PartialSum a) s
def SeriesConvergent (a : ℕ → ℝ) : Prop := ∃ s : ℝ, SeriesConvergesTo a s

def CompactSet (M : Set ℝ) : Prop := ∀ (a : ℕ → ℝ), (∀ n : ℕ, a n ∈ M) → ∃ (k : ℕ → ℕ), StrictlyIncreasingSequenceN k ∧ ∃ l : ℝ, ConvergesTo (Subsequence a k) l ∧ l ∈ M
def ClosedSet (M : Set ℝ) : Prop := ∀ (a : ℕ → ℝ) (L : ℝ), (∀ n : ℕ, a n ∈ M) → ConvergesTo a L → L ∈ M
def BoundedSet (M : Set ℝ) : Prop := ∃ c : ℝ, c > 0 ∧ ∀ m ∈ M, |m| < c

---------- pomocna lemmata ----------

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



lemma DivInfUnbdd {a : ℕ → ℝ} (hdiv : DivergentToInf a) : ¬ BoundedSequence a := by
  unfold BoundedSequence
  unfold DivergentToInf at hdiv
  push_neg
  intro K K_pos
  obtain ⟨n₀, hn₀⟩ := hdiv K K_pos
  use n₀
  specialize hn₀ n₀ (by linarith)
  by_contra h
  push_neg at h
  have : |a n₀| ≥ a n₀ := by exact le_abs_self (a n₀)
  have : |a n₀| > K := by
    calc
      |a n₀| ≥ a n₀ := this
      _ > K := hn₀
  linarith

lemma IncUnbddDivgToInf {a : ℕ → ℝ} (ha_inc : IncreasingSequence a) (ha_unbdd : ¬ BoundedSequence a) : DivergentToInf a := by
 classical
  intro M M_pos
  have h_unbdd' : ∀ K > 0, ∃ n, |a n| ≥ K := by
    intro K K_pos
    by_contra hfalse
    push_neg at hfalse
    have : BoundedSequence a := by
      have : ∀ n : ℕ, a n ≤ |a n| := by exact fun n => le_abs_self (a n)
      unfold BoundedSequence
      refine ⟨K, K_pos, ?_⟩
      intro n
      exact hfalse n

    exact ha_unbdd this
  let K := M + |a 0| + 1
  have K_pos : K > 0 := by
    have : |a 0| ≥ 0 := abs_nonneg (a 0)
    linarith
  rcases h_unbdd' K K_pos with ⟨n0, hn0⟩

  have hn0_pos : a n0 ≥ 0 := by
    by_contra h
    push_neg at h
    rw [abs_of_neg h] at hn0
    have : a n0 ≥ a 0 := inc_le_of_le ha_inc (Nat.zero_le n0)
    have : a 0 ≥ -|a 0| := by exact neg_abs_le (a 0)
    linarith

  rw [abs_of_nonneg hn0_pos] at hn0

  use n0
  intro n hn_ge
  have h_mono : a n ≥ a n0 := inc_le_of_le ha_inc hn_ge
  have hK : K = M + |a 0| + 1 := rfl
  have : |a 0| ≥ 0 := abs_nonneg (a 0)
  linarith

  lemma construct_unbounded_sequence
    (M : Set ℝ)
    (hnot : ¬ BoundedSet M) :
    ∃ a : ℕ → ℝ, (∀ n, a n ∈ M) ∧ (¬ BoundedSequence a) :=
by
  classical
  have : ∀ N : ℕ, ∃ m ∈ M, |m| ≥ N := by
    intro N
    by_contra hC
    push_neg at hC
    have : BoundedSet M := by
      unfold BoundedSet
      use N + 1
      constructor
      · linarith
      · intro m hmM
        calc
          |m| < (N : ℝ) := by exact hC m hmM
          _ < (N : ℝ) + 1 := by linarith
    exact hnot this
  choose a haM haBig using this
  use a
  constructor
  · intro n; exact (haM n)
  · unfold BoundedSequence
    push_neg
    intro K K_pos
    use Nat.ceil K
    have : (Nat.ceil K : ℝ) ≥ K := Nat.le_ceil K
    calc
      |(a (Nat.ceil K))| ≥ (Nat.ceil K : ℝ) := haBig (Nat.ceil K)
      _ ≥ K := this
