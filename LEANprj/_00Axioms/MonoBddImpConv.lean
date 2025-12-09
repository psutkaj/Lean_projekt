import LEANprj.defs

axiom MonoBddImpConv
  (a : ℕ → ℝ)
  (ha_mono : MonotonicSequence a)
  (ha_bdd : BoundedSequence a) :
  Convergent a
