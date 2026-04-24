import LEANprj.defs
noncomputable section

def max_upto (a : ℕ → ℝ) : ℕ → ℝ
  | 0     => |a 0|
  | n + 1 => max (|a (n + 1)|) (max_upto a n)

lemma le_max_upto
  (a : ℕ → ℝ) (n k : ℕ) (h : k ≤ n) :
  |a k| ≤ max_upto a n :=
by
  induction' n with d hd
  · rw [Nat.eq_zero_of_le_zero h, max_upto]
  · rw [max_upto]
    by_cases h₁ : k = d + 1
    · exact le_sup_of_le_left (by rw [h₁])
    · push_neg at h₁
      apply le_sup_of_le_right
      apply hd
      exact Nat.le_of_lt_succ (Nat.lt_of_le_of_ne h h₁)

theorem bdd_of_conv
  {a : ℕ → ℝ} (a_conv : Convergent a) :
  BoundedSequence a :=
by
  obtain ⟨c, hc⟩ := a_conv
  obtain ⟨n₀, hn₀⟩ := hc 1 (by linarith)
  let K₀ := max_upto a n₀
  let K := max K₀ (|c| + 1)
  use K
  constructor
  · dsimp [K]
    simp
    right
    exact Right.add_pos_of_nonneg_of_pos (abs_nonneg c) (by linarith)
  intro n
  dsimp [K]
  by_cases h : n ≤ n₀
  · simp
    left
    exact le_max_upto a n₀ n h
  · simp
    right
    have : |a n| - |c| ≤ |a n - c| := abs_sub_abs_le_abs_sub (a n) c
    calc |a n|
      _ ≤ |a n - c| + |c| := by linarith
      _ ≤ 1 + |c| := by
        simp
        push_neg at h
        specialize hn₀ n (by linarith)
        exact le_of_lt hn₀
    linarith
