import LEANprj.defs

example (a : ℕ → ℝ) (c : ℝ) (h : ∀ n : ℕ, a n = c) : BoundedSequence a := by
  unfold BoundedSequence
  use |c| + 1
  constructor
  linarith [abs_nonneg c]
  intro n
  rw [h]
  linarith

example (a : ℕ → ℝ) (c : ℝ) (h: ∀ n : ℕ, a n = c ∨ a n = -c) : BoundedSequence a := by
  unfold BoundedSequence
  use |c| + 1
  constructor
  linarith [abs_nonneg c]
  intro n
  cases h n with
  | inl hc => simp [hc]
  | inr hcn =>
    simp [hcn]


-- example (a : ℕ → ℝ) (ha: ∀ n : ℕ, a n = (n / (n + 1))) : BoundedSequence a := by
--   unfold BoundedSequence
--   use 1
--   constructor
--   linarith
--   intro n
--   rw [ha]
--   -- chci ukazat ze jmenovatel je pozitivni
--   have denom_pos : 0 < (n + 1 : ℝ) := by
--     norm_cast
--     linarith
--   -- chci ukazat ze citatel je mensi nee jmenovatel abych mohl ukaza ze n / n + 1 < 1
--   have num_lt_denom : (n : ℝ) < (n + 1 : ℝ) := by
--     linarith
--   -- chci ukazat, ze n / n + 1 < 1
--   have : (n : ℝ) / (n + 1 : ℝ) < 1 := by
--     exact (div_lt_one₀ denom_pos).mpr num_lt_denom
--   -- ukazu, ze vyraz je nezaporny
--   have nonneg : 0 ≤ (n : ℝ) / (n + 1 : ℝ) := by
--     exact div_nonneg (by norm_cast; apply Nat.cast_nonneg) (le_of_lt denom_pos)
--   -- a diky tomu abs vyrazu = vyraz
--   have h : |(n : ℝ) / (n + 1 : ℝ)| = (n : ℝ) / (n + 1 : ℝ) := abs_of_nonneg nonneg
--   rw [h]
--   exact this

noncomputable def d : Sequence := λ n ↦ n / (n + 1)
example :
  BoundedSequence d :=
by
  unfold BoundedSequence
  use 2
  constructor
  · linarith
  · intro n
    dsimp [d]
    have denom_pos : (n + 1 : ℝ) > 0 := by linarith
    have num_nonneg : (n : ℝ) ≥ 0 := by linarith
    have frac_pos : (n : ℝ) / (n + 1 : ℝ) ≥ 0 := by
      exact div_nonneg num_nonneg (by linarith)
    rw [abs_of_nonneg frac_pos]
    have : (n : ℝ) / (n + 1 : ℝ) < 1 := by
      refine (div_lt_one₀ denom_pos).mpr ?_
      linarith
    linarith


noncomputable def a : Sequence := λ n ↦ 1 / (n + 1)
example : BoundedSequence a := by
  unfold BoundedSequence
  use 2
  constructor
  · linarith
  · intro n
    dsimp [a]
    rw [abs_of_nonneg]
    · have : (n + 1) > 0 := by exact Nat.zero_lt_succ n
      apply (one_div_le (by linarith) (by linarith)).mpr
      linarith
    · simp
      linarith
