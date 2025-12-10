import LEANprj.defs
open Classical
noncomputable section

def max_upto (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => |a 0|
  | (n + 1) => max (|a (n + 1)|) (max_upto a n)

lemma le_max_upto (a : ℕ → ℝ) (n k : ℕ) (h : k ≤ n) : |a k| ≤ max_upto a n := by
  induction' n with d hd
  · have : k = 0 := by exact Nat.eq_zero_of_le_zero h
    rw [this, max_upto]
  · rw [max_upto]
    by_cases h₁ : k = d + 1
    · refine le_sup_of_le_left ?_
      rw [h₁]
    · push_neg at h₁
      have : k ≤ d := by
        have : k < d + 1 := by exact Nat.lt_of_le_of_ne h h₁
        exact Nat.le_of_lt_succ this
      exact le_sup_of_le_right (hd this)

theorem ConvImpliesBdd {a : ℕ → ℝ} (a_conv : Convergent a) : BoundedSequence a := by
  obtain ⟨c, hc⟩ := a_conv
  obtain ⟨n₀, hn₀⟩ := hc 1 (by linarith)
  unfold BoundedSequence
  let K₀ := max_upto a n₀
  let K := max K₀ (|c| + 1)
  have K_pos : K > 0 := by
    apply lt_of_lt_of_le zero_lt_one
    calc 1 ≤ |c| + 1 := le_add_of_nonneg_left (abs_nonneg c)
         _ ≤ K       := le_max_right _ _
  use K, K_pos
  intro n
  by_cases h : n ≤ n₀
  · dsimp [K]
    refine le_sup_of_le_left ?_
    dsimp [K₀]
    exact le_max_upto a n₀ n h
  · push_neg at h
    dsimp [K]
    refine le_sup_of_le_right ?_
    specialize hn₀ n (by linarith)
    have : |a n| - |c| ≤ |a n - c| := by exact abs_sub_abs_le_abs_sub (a n) c
    calc |a n|
    _ ≤ |c| + |a n - c| := by linarith
    _ ≤ |c| + 1 := by linarith
