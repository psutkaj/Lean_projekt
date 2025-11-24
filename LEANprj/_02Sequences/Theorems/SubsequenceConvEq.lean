import LEANprj.defs

lemma SubsequenceConvEq {a : ℕ → ℝ} {L : ℝ} (hconv : ConvergesTo a L) (k : ℕ → ℕ) (hk : StrictlyIncreasingSequenceN k) : ConvergesTo (Subsequence a k) L := by
  intro ε ε_pos
  obtain ⟨n₀, hn₀⟩ := hconv ε ε_pos
  use n₀
  intro n hn_geq
  unfold Subsequence
  have : k n ≥ n₀ := by


    sorry

  sorry
