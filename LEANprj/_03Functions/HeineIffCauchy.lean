import LEANprj.defs

lemma cauchy_of_heine
  (f : ℝ → ℝ) (x₀ : ℝ) (b : ℝ) :
  HeineLimitFun f x₀ b →
  CauchyLimitFun f x₀ b :=
by
  unfold HeineLimitFun CauchyLimitFun
  intro Heine
  by_contra! h_not_cauchy
  obtain ⟨ε, ε_pos, h_not_δ⟩ := h_not_cauchy
  have h_ex_seq : ∀ n : ℕ, ∃ x, 0 < |x - x₀| ∧ |x - x₀| < 1 / (n + 1) ∧ ε ≤ |f x - b| := by
    intro n
    obtain ⟨x, hx⟩ := h_not_δ (1 / (n + 1)) (by norm_num; nlinarith)
    use x
    exact and_assoc.mp hx
  choose x h_x_props using h_ex_seq
  have h_neq : ∀ n, x n ≠ x₀ := by
    intro n
    exact abs_sub_pos.mp (h_x_props n).1
  have h_squeeze : ∀ n, |x n - x₀| < 1 / (n + 1) := by
    intro n
    exact (h_x_props n).2.1
  have h_far : ∀ n, |f (x n) - b| ≥ ε := by
    intro n
    exact (h_x_props n).2.2
  have h_conv_a : ConvergesTo x x₀ := by
    intro e e_pos
    have h : ∃ n₀ : ℕ, 1 / (n₀ + 1 : ℝ) < e := exists_nat_one_div_lt e_pos
    obtain ⟨n₀, hn₀⟩ := h
    use n₀
    intro n hn
    calc
      |x n - x₀| < 1 / (n + 1) := h_squeeze n
      _ ≤ 1 / (n₀ + 1) := by gcongr
      _ < e := hn₀
  have h_conv_f : ConvergesTo (f ∘ x) b := Heine x h_neq h_conv_a
  obtain ⟨n₀, h_close⟩ := h_conv_f ε ε_pos
  specialize h_close n₀ (by linarith)
  specialize h_far n₀
  simp at h_close
  linarith

lemma heine_of_cauchy (f : ℝ → ℝ) (x₀ : ℝ) (b : ℝ) :
  CauchyLimitFun f x₀ b → HeineLimitFun f x₀ b :=
by
  intro Cauchy x hne x_conv ε ε_pos
  obtain ⟨δ, δ_pos, h⟩ := Cauchy ε ε_pos
  obtain ⟨n₀, hn₀⟩ := x_conv δ δ_pos
  use n₀
  intro n hn
  apply h
  constructor
  · simp only [abs_pos, ne_eq]
    push_neg
    exact sub_ne_zero_of_ne (hne n)
  · exact hn₀ n hn

theorem heine_iff_cauchy (f : ℝ → ℝ) (x₀ : ℝ) (b : ℝ) :
  HeineLimitFun f x₀ b ↔ CauchyLimitFun f x₀ b :=
   ⟨cauchy_of_heine f x₀ b, heine_of_cauchy f x₀ b⟩
