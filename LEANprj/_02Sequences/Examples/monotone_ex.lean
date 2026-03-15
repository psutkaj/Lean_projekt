import LEANprj.defs

example (a : ℕ → ℝ) (ha: ∀ n : ℕ, a n = n) : StrictlyIncreasingSequence a := by
  unfold StrictlyIncreasingSequence
  intro n
  rw [ha, ha]
  norm_cast
  linarith

example (a : ℕ → ℝ) (ha: ∀ n : ℕ, a n = (n / (n + 1))) : StrictlyIncreasingSequence a := by
  unfold StrictlyIncreasingSequence
  intro n
  rw [ha, ha]
  norm_cast
  simp
  refine (div_lt_div_iff₀ ?_ ?_).mpr ?_
  linarith
  linarith
  nlinarith

noncomputable def d : Sequence := λ n ↦ n / (n + 1)
example :
  StrictlyIncreasingSequence d :=
by
  unfold StrictlyIncreasingSequence
  intro n
  dsimp [d]

  refine (div_lt_div_iff₀ ?_ ?_).mpr ?_
  · linarith
  · linarith
  · norm_cast
    nlinarith
