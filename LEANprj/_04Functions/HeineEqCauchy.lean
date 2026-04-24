import LEANprj.defs

lemma HeineImpCauchy (f : ℝ → ℝ) (x₀ : ℝ) (b : ℝ) :
  HeineLimitFunction f x₀ b → CauchyLimitFunction f x₀ b :=
by
  unfold HeineLimitFunction CauchyLimitFunction
  intro Heine
  by_contra h_not_cauchy
  push_neg at h_not_cauchy
  obtain ⟨ε, ε_pos, h_not_δ⟩ := h_not_cauchy
  have h_ex_seq : ∀ n : ℕ, ∃ x, 0 < |x - x₀| ∧ |x - x₀| < 1 / (n + 1) ∧ ε ≤ |f x - b| := by
    intro n
    specialize h_not_δ (1 / (n + 1)) (by positivity)
    obtain ⟨x, hx⟩ := h_not_δ
    use x
    exact and_assoc.mp hx
  choose a h_a_props using h_ex_seq
  have h_neq : ∀ n, a n ≠ x₀ := by intro n; exact abs_sub_pos.mp (h_a_props n).1
  have h_squeeze : ∀ n, |a n - x₀| < 1 / (n + 1) := by intro n; exact (h_a_props n).2.1
  have h_far : ∀ n, |f (a n) - b| ≥ ε := by intro n; exact (h_a_props n).2.2
  have h_conv_a : ConvergesTo a x₀ := by
    unfold ConvergesTo
    intro e e_pos
    have h_arch : ∃ n₀ : ℕ, 1 / (n₀ + 1 : ℝ) < e := exists_nat_one_div_lt e_pos
    obtain ⟨n₀, hn₀⟩ := h_arch
    use n₀
    intro n hn
    calc
      |a n - x₀| < 1 / (n + 1) := h_squeeze n
      _ ≤ 1 / (n₀ + 1) := by gcongr
      _ < e := hn₀
  have h_conv_f : ConvergesTo (f ∘ a) b := Heine a h_neq h_conv_a
  unfold ConvergesTo at h_conv_f
  obtain ⟨n₀, h_close⟩ := h_conv_f ε ε_pos
  specialize h_close n₀ (by linarith)
  specialize h_far n₀
  simp at h_close
  linarith

lemma CauchyImpHeine (f : ℝ → ℝ) (x₀ : ℝ) (b : ℝ) :
  CauchyLimitFunction f x₀ b → HeineLimitFunction f x₀ b :=
by
  unfold HeineLimitFunction
  intros Cauchy a hne a_conv
  unfold ConvergesTo
  intro ε ε_pos
  obtain ⟨δ, δ_pos, h⟩ := Cauchy ε ε_pos
  specialize a_conv δ δ_pos
  obtain ⟨n₀, hn₀⟩ := a_conv
  use n₀
  intro n hn
  apply h
  constructor
  · simp
    push_neg
    exact sub_ne_zero_of_ne (hne n)
  · exact hn₀ n hn

theorem HeineEqCauchy (f : ℝ → ℝ) (x₀ : ℝ) (b : ℝ) :
  HeineLimitFunction f x₀ b ↔ CauchyLimitFunction f x₀ b :=
by
  constructor
  · -- Heine → Cauchy
    exact HeineImpCauchy f x₀ b
  · -- Cauchy → Heine
    exact CauchyImpHeine f x₀ b
