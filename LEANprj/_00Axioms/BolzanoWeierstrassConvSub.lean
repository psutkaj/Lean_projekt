import LEANprj.defs

axiom BolzanoWeierstrassConvSub
  (a : ℕ → ℝ)
  (h_bdd : BoundedSequence a) :
  ∃ k : ℕ → ℕ,
  StrictlyIncreasingSequenceN k ∧
  Convergent (Subsequence a k)
