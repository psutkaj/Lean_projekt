import LEANprj.defs

theorem UniquenessLimitFunction (f : ℝ → ℝ) (x₀ a b : ℝ) (h₁ : HeineLimitFunction f x₀ a) (h₂ : HeineLimitFunction f x₀ b) : a = b := by
  by_contra hne
  push_neg at hne
  unfold HeineLimitFunction at h₁
  unfold HeineLimitFunction at h₂
  let s := λ n : ℕ ↦ x₀ + 1 / (n + 1 : ℝ)
  have h_ne_x₀ : ∀ n, s n ≠ x₀ := by
    intro n
    dsimp [s]
    simp
    linarith
  have h_conv_s : ConvergesTo s x₀ := by
    intro ε hε
    dsimp [s]
    rcases exists_nat_one_div_lt hε with ⟨n₀, hn₀⟩
    use n₀
    intro n hn
    rw [abs_of_pos, add_sub_cancel_left]
    have : 1 / (n₀ + 1) ≥ 1 / (n + 1) := by gcongr;

    sorry

  sorry
