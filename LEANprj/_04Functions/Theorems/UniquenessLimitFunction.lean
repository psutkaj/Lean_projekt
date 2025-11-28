import LEANprj.defs
import LEANprj._02Sequences.Theorems.UniquenessTheorem


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
    have : 1 / (n₀ + 1 : ℝ) ≥ 1 / (n + 1 : ℝ) := by gcongr;
    calc
      1 / (↑n + 1) ≤ 1 / (↑n₀ + 1) := this
      _ < ε := hn₀
    simp
    linarith
  have h_seq_a : ConvergesTo (f ∘ s) a := by exact h₁ s h_ne_x₀ h_conv_s
  have h_seq_b : ConvergesTo (f ∘ s) b := by exact h₂ s h_ne_x₀ h_conv_s
  have : a = b := Uniqueness (f ∘ s) a b h_seq_a h_seq_b
  contradiction
