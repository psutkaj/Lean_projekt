import LEANprj.defs
import LEANprj._02Sequences.AxCauchyConvOfAxBW

theorem BolzanoCauchy (a : ℕ → ℝ) : AxCauchyConv → (SeriesConvergent a ↔ CauchySequence (PartialSum a)) := by
  intro AxCauchyConv
  rw [SeriesConvergent]
  unfold SeriesConvergesTo
  rw [← Convergent]
  exact Iff.symm (AxCauchyConv (PartialSum a))
