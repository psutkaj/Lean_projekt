import LEANprj.defs

axiom CauchyEqConv
  (a : ℕ → ℝ) :
  CauchySequence a ↔ Convergent a
