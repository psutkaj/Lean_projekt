import LEANprj.defs

lemma SubsequenceConvEq {a : ℕ → ℝ} {L : ℝ} (hconv : ConvergesTo a L) (k : ℕ → ℕ) (hk : StrictlyIncreasingSequenceN k) : ConvergesTo (Subsequence a k) L := by
  intro ε ε_pos
  obtain ⟨n₀, hn₀⟩ := hconv ε ε_pos
  use n₀
  intro n hn_geq
  unfold Subsequence
  unfold StrictlyIncreasingSequenceN at hk
  have k_inc : ∀ {i j}, i ≤ j → k i ≤ k j := by
    intro i j hij
    by_cases h : i = j
    · simp [h]
    · have : i < j := by exact Nat.lt_of_le_of_ne hij h
      have : k i < k j := by exact inc_lt_of_ltN k hk this
      exact Nat.le_of_succ_le this
  have k_ge_n : ∀ m, k m ≥ m := by
    intro m
    induction' m with m ih
    · simp
    · have : k (m + 1) ≥ k m + 1 := Nat.succ_le_of_lt (hk m)
      calc
        k (m + 1) ≥ k m + 1 := this
        _ ≥ m + 1 := by linarith
  have : k n ≥ k n₀ := by exact k_inc hn_geq
  have kn_ge_n0 : k n ≥ n₀ := by
    have : k n ≥ n := k_ge_n n
    exact Nat.le_trans hn_geq (k_ge_n n)
  exact hn₀ (k n) kn_ge_n0
