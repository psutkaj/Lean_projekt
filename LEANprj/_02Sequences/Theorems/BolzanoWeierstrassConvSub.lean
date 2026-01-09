import LEANprj._02Sequences.Theorems.MonoBddImpliesConv
import LEANprj._02Sequences.Theorems.ExMonoSubsequence

theorem BolzanoWeierstrassConvSub (a : ℕ → ℝ) (ha_bdd : BoundedSequence a) : ∃ k : ℕ → ℕ, StrictlyIncreasingSequenceN k ∧ Convergent (Subsequence a k) := by
  obtain ⟨k, hk_inc, hk_mono⟩ := ExMonoSubsequence a
  have sub_bdd : BoundedSequence (Subsequence a k) := by
    obtain ⟨K, hK, hkn⟩ := ha_bdd
    refine ⟨K, hK, ?_⟩
    intro n
    exact hkn (k n)
  refine ⟨k, hk_inc, ?_⟩
  exact MonoBddImpliesConv (Subsequence a k) hk_mono sub_bdd


theorem BolzanoWeierstrassConvSub' (a : ℕ → ℝ) (ha_bdd : BoundedSequence a) :
    ∃ k : ℕ → ℕ, StrictlyIncreasingSequenceN k ∧ Convergent (Subsequence a k) :=  by
  have ⟨k, hk_strict, hk_mono⟩ := ExMonoSubsequence a

  -- The subsequence is also bounded since the original sequence is bounded
  have subseq_bdd : BoundedSequence (Subsequence a k) := by
    rcases ha_bdd with ⟨K, hK_pos, hK_bdd⟩
    exists K, hK_pos
    intro n
    exact hK_bdd (k n)

  -- A bounded monotonic sequence converges
  have h_conv : Convergent (Subsequence a k) := by
    cases hk_mono with
    | inl h_increasing =>
      exact MonoBddImpliesConv (Subsequence a k) (Or.inl h_increasing) subseq_bdd
    | inr h_decreasing =>
      exact MonoBddImpliesConv (Subsequence a k) (Or.inr h_decreasing) subseq_bdd

  exists k





theorem BolzanoWeierstrassConvSub'' (a : ℕ → ℝ) (ha_bdd : BoundedSequence a) : ∃ k : ℕ → ℕ, StrictlyIncreasingSequenceN k ∧ Convergent (Subsequence a k) := by
  -- 1. Find a monotonic subsequence using the previous theorem.
  rcases ExMonoSubsequence a with ⟨k, hk_strict, hk_mono⟩

  -- 2. Show that this subsequence is also bounded.
  have h_sub_bdd : BoundedSequence (Subsequence a k) := by
    rcases ha_bdd with ⟨K, hK_pos, hK_bound⟩
    refine ⟨K, hK_pos, ?_⟩
    intro n
    -- The elements of the subsequence are elements of the original sequence.
    exact hK_bound (k n)

  -- 3. A bounded monotonic subsequence converges.
  have h_sub_conv : Convergent (Subsequence a k) := MonoBddImpliesConv (Subsequence a k) hk_mono h_sub_bdd

  -- 4. Combine the results.
  exact ⟨k, hk_strict, h_sub_conv⟩
