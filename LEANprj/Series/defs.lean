import LEANprj.Sequences.defs

--
def PartialSum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n + 1), a k
def SeriesConvergesTo (a : ℕ → ℝ) (s : ℝ) : Prop := ConvergesTo (PartialSum a) s
def SeriesConvergent (a : ℕ → ℝ) : Prop := ∃ s : ℝ, SeriesConvergesTo a s
