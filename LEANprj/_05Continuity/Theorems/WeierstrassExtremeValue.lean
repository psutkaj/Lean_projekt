import LEANprj.defs
import LEANprj.lemmas
import LEANprj._02Sequences.Theorems.AxBWOfAxMonoConv
import LEANprj._02Sequences.Theorems.Sandwich
import LEANprj._01Sets.Theorems.AxSupOfAxNIP

theorem WeierstrassBdd {f : ℝ → ℝ} {a b : ℝ}
  (h_cont : FunctionContinuousOnSet (Set.Icc a b) f) :
  AxMonoConv → FunctionBddOnSet (Set.Icc a b) f :=
by
  intro AxMonoConv
  by_contra h_unbdd
  unfold FunctionBddOnSet at h_unbdd
  push_neg at h_unbdd
  let x_seq : ℕ → ℝ := λ n => Classical.choose (h_unbdd (n + 1) (by linarith))
  have h_x_seq_prop : ∀ n, x_seq n ∈ (Set.Icc a b) ∧ |f (x_seq n)| ≥ n + 1 := by
    intro n
    obtain ⟨h_mem, h_lt⟩ := Classical.choose_spec (h_unbdd (n + 1) (by linarith))
    exact ⟨h_mem, le_of_lt h_lt⟩
  have h_x_seq_bounded : BoundedSequence x_seq := by
    unfold BoundedSequence
    let K := max (|a| + |b| + 1) 1
    use K, by (dsimp [K]; simp)
    intro n
    have h := (h_x_seq_prop n).1
    cases' h with h_left h_right
    rw [abs_le]
    constructor
    · calc -max (|a| + |b| + 1) 1
      _ ≤ - (|a| + |b| + 1) := neg_le_neg (le_max_left _ _)
      _ ≤ -|a| := by
        simp
        refine neg_le.mp ?_
        have : |b| ≥ 0 := abs_nonneg b
        calc -1 ≤ 0 := by linarith
        _ ≤ |b| := this
      _ ≤ a := neg_abs_le a
      _ ≤ x_seq n := h_left
    · calc x_seq n
        _ ≤ b := h_right
        _ ≤ |b| + 1 := by
          have : b ≤ |b| := le_abs_self b
          linarith
        _ ≤ |a| + |b| + 1 := by simp
        _ ≤ K := by dsimp [K]; simp
  obtain ⟨k, hk_inc, c, hk_conv⟩ := axBw_of_axMonoConv AxMonoConv x_seq h_x_seq_bounded
  have hc_in_Int : c ∈ (Set.Icc a b) := by
    have h_closure : ∀ n, x_seq (k n) ∈ (Set.Icc a b) := by
      intro n
      exact (h_x_seq_prop (k n)).1
    constructor
    · by_contra hnot
      push_neg at hnot
      let ε := (a - c) / 2
      have ε_pos : ε > 0 := by dsimp[ε]; linarith
      obtain ⟨n₀, hn₀⟩ := hk_conv ε ε_pos
      specialize hn₀ n₀ (by linarith)
      have h_x_ge_a := (h_closure n₀).1
      rw [Subsequence] at hn₀
      have upper_bound : c + ε = (a + c)/2 := by ring
      have upper_bound_lt_a : (a + c)/2 < a := by linarith
      rw [Function.comp_apply, abs_lt] at hn₀
      have h_x_lt_a : x_seq (k n₀) < a := by linarith
      linarith
    · by_contra hnot
      push_neg at hnot
      let ε := (c - b) / 2
      have ε_pos : ε > 0 := by dsimp [ε]; linarith
      have hε : ε > 0 := by linarith
      obtain ⟨N, hN⟩ := hk_conv ε hε
      specialize hN N (by linarith)
      have h_x_le_b := (h_closure N).2
      rw [Subsequence, Function.comp_apply, abs_lt] at hN
      have lower_bound : c - ε = (b + c)/2 := by ring
      have upper_bound_lt_a : (b + c)/2 > b := by linarith
      linarith
  have h_cont_at_c : FunctionContinuousAt f c := h_cont c hc_in_Int
  have h_f_conv : ConvergesTo (f ∘ (x_seq ∘ k)) (f c) := by
    intro ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ := h_cont_at_c ε hε
    obtain ⟨N, hN⟩ := hk_conv δ hδ_pos
    use N
    intro n hn
    specialize hN n hn
    rw [Subsequence] at hN
    by_cases h_eq : x_seq (k n) = c
    · rw [← h_eq]
      simpa using hε
    · apply hδ
      constructor
      · rw [abs_pos]
        exact sub_ne_zero.mpr h_eq
      · exact hN
  obtain ⟨N, hN⟩ := h_f_conv 1 Real.zero_lt_one
  obtain ⟨m, hm⟩ := exists_nat_gt (|f c|)
  let n := max N m
  specialize hN n (le_max_left N m)
  dsimp at hN
  have h_triangle : |f (x_seq (k n))| - |f c| ≤ |f (x_seq (k n)) - f c| := abs_sub_abs_le_abs_sub _ _
  have h_val_bound : |f (x_seq (k n))| < |f c| + 1 := by
    rw [abs_sub_comm] at hN
    have : |f (x_seq (k n))| ≤ |f c| + |f (x_seq (k n)) - f c| := by linarith
    have : |f (x_seq (k n)) - f c| = |f c - f (x_seq (k n))| := abs_sub_comm (f (x_seq (k n))) (f c)
    have : |f c| + |f (x_seq (k n)) - f c| < |f c| + 1 := by linarith
    linarith
  have h_seq_bound : |f (x_seq (k n))| ≥ n + 1 := by
    have hknn : k n ≥ n := StrictlyIncreasingSequenceN_ge_id k hk_inc n
    have hfkn : |f (x_seq (k n))| ≥ k n + 1 := (h_x_seq_prop (k n)).2
    have hkn : k n + 1 ≥ n + 1 := by linarith
    trans k n + 1
    · exact hfkn
    · simp
      linarith
  have h_n_large : n > |f c| := by
    have : (n : ℝ) ≥ m := Nat.cast_le.mpr (le_max_right N m)
    linarith
  linarith

theorem ContinuousImpliesSequential {f : ℝ → ℝ} {c : ℝ} (h_cont : FunctionContinuousAt f c)
  {x : ℕ → ℝ} (h_conv : ConvergesTo x c) :
  ConvergesTo (f ∘ x) (f c) :=
by
  intro ε hε
  obtain ⟨δ, hδ_pos, h_f_delta⟩ := h_cont ε hε
  obtain ⟨n₀, h_x_delta⟩ := h_conv δ hδ_pos
  use n₀
  intro n hn
  by_cases h_xn_eq_c : x n = c
  · rw [Function.comp_apply, h_xn_eq_c]
    simpa using hε
  · exact h_f_delta _ ⟨abs_sub_pos.mpr h_xn_eq_c, h_x_delta n hn⟩

theorem WeierstrassMax {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
  (h_cont : FunctionContinuousOnSet (Set.Icc a b) f) :
  AxMonoConv → AxNIP → ∃ M ∈ (Set.Icc a b), ∀ x ∈ (Set.Icc a b), f x ≤ f M :=
by
  intro AxMonoConv AxNIP
  let S := {f y | y ∈ (Set.Icc a b)}
  have S_nonempty : S.Nonempty := by
    use f a
    dsimp [S]
    use a
    constructor
    simpa
    rfl
  have S_bdd : BoundedSet S := by
    unfold BoundedSet
    obtain ⟨c, c_pos, hc⟩ := WeierstrassBdd h_cont AxMonoConv
    use c, c_pos
    intro m hm
    dsimp [S] at hm
    obtain ⟨y, y_in_int, hy⟩ := hm
    rw [←hy]
    exact hc y y_in_int
  have S_upper_bdd : ∃ u : ℝ, ∀ a ∈ S, a ≤ u := by
    obtain ⟨c, c_pos, hc⟩ := S_bdd
    use c
    intro a aS
    specialize hc a aS
    trans |a|
    · exact le_abs_self a
    · exact hc
  obtain ⟨M, IsSupM, UniqueM⟩ := axSup_of_axNip AxNIP S S_nonempty S_upper_bdd
  unfold IsSup at IsSupM
  cases' IsSupM with upper_bd lowest_upper
  let ε : ℕ → ℝ := λ n ↦ 1 / (n + 1 : ℝ)
  have ε_pos : ∀ n : ℕ, ε n > 0 := by intro n; dsimp[ε]; simp; linarith
  have M'_not_upper_bd : ∀ n : ℕ, ∃ y ∈ S,  M - ε n < y := by
    intro n
    exact lowest_upper (ε n) (ε_pos n)
  choose y y_in_S y_close using M'_not_upper_bd
  have M_upper_bd_of_y : ∀ n : ℕ, y n ≤ M := by
    intro n
    exact upper_bd (y n) (y_in_S n)
  have x_exists : ∀ n : ℕ, ∃ x ∈ (Set.Icc a b), f x = y n := by
    intro n
    exact y_in_S n
  choose x x_in_Int fx_eq_y using x_exists
  have x_bdd : BoundedSequence x := by
    unfold BoundedSequence
    use max |a| |b| + 1
    constructor
    · exact lt_add_of_nonneg_of_lt (le_sup_of_le_right (abs_nonneg b)) (by simp)
    · intro n
      specialize x_in_Int n
      rw [abs_le]
      constructor
      · calc - (max (|a|) (|b|) + 1)
        _ ≤ - max (|a|) (|b|) := by linarith
        _ ≤ - |a| := neg_le_neg (le_max_left _ _)
        _ ≤ a := neg_abs_le a
        _ ≤ x n := x_in_Int.1
      · calc x n
        _ ≤ b := x_in_Int.2
        _ ≤ |b| := le_abs_self b
        _ ≤ max (|a|) (|b|) := le_max_right _ _
        _ ≤ max (|a|) (|b|) + 1 := by linarith
  obtain ⟨k, hk_inc, hk_conv⟩ := axBw_of_axMonoConv AxMonoConv x x_bdd
  obtain ⟨c, hc⟩ := hk_conv
  have c_in_Int : c ∈ (Set.Icc a b) := by
    simp
    constructor
    · have a_leq_xn : ∀ n : ℕ, a ≤ x n := by
        intro n
        exact (x_in_Int n).1
      have a_leq_xkn : ∀ n : ℕ, a ≤ x (k n) := by
        intro n
        exact a_leq_xn (k n)
      refine LimitOrderLe (λ n ↦ a) (Subsequence x k) a c a_leq_xkn ?_ hc
      · unfold ConvergesTo
        intro ε ε_pos
        simp
        tauto
    · have xn_leq_b : ∀ n : ℕ, x n ≤ b := by
        intro n
        exact (x_in_Int n).2
      have xkn_leq_b : ∀ n : ℕ, x (k n) ≤ b := by
        intro n
        exact xn_leq_b (k n)
      refine LimitOrderLe (Subsequence x k) (λ n ↦ b) c b xkn_leq_b hc ?_
      · unfold ConvergesTo
        intro ε ε_pos
        simp
        tauto
  use c, c_in_Int
  intro d d_in_Int
  have h_cont_c : FunctionContinuousAt f c := h_cont c c_in_Int
  have h_lim_continuity : ConvergesTo (f ∘ (Subsequence x k)) (f c) := by
    apply ContinuousImpliesSequential h_cont_c
    exact hc
  have h_lim_construction : ConvergesTo (f ∘ (Subsequence x k)) M := by
    intro ε ε_pos
    obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt ε_pos
    use n₀
    intro n hn
    rw [abs_lt]
    constructor
    · simp
      have h_calc : f (x (k n)) > M - ε := calc f (x (k n))
        _ = y (k n) := fx_eq_y (k n)
        _ > M - 1 / (k n + 1) := y_close (k n)
        _ ≥ M - 1 / (n + 1)   := by
            apply sub_le_sub_left
            apply one_div_le_one_div_of_le
            · linarith
            · simp
              have := StrictlyIncreasingSequenceN_ge_id k hk_inc n
              linarith
        _ > M - ε := by
            have : 1 / (n + 1 : ℝ) ≤ 1 / (n₀ + 1 : ℝ) := by
              apply one_div_le_one_div_of_le
              · linarith
              · simp; linarith
            have : 1 / (n + 1 : ℝ) < ε := lt_of_le_of_lt this hn₀
            linarith
      dsimp [Subsequence]
      linarith
    · have h_calc : f (x (k n)) < M + ε := calc f (x (k n))
        _ = y (k n) := fx_eq_y (k n)
        _ ≤ M := M_upper_bd_of_y (k n)
        _ < M + ε := lt_add_of_pos_right M ε_pos
      dsimp [Subsequence]
      linarith

  have M_eq_fc : M = f c := by
    by_contra h
    have diff_pos : |M - f c| > 0 := abs_sub_pos.mpr h
    let ε := |M - f c| / 2
    have ε_pos : ε > 0 := by dsimp [ε]; linarith
    obtain ⟨N₁, hN₁⟩ := h_lim_construction ε ε_pos
    obtain ⟨N₂, hN₂⟩ := h_lim_continuity ε ε_pos
    let n := max N₁ N₂
    specialize hN₁ n (le_max_left _ _)
    specialize hN₂ n (le_max_right _ _)
    have : |M - f c| ≤ |M - f (x (k n))| + |f (x (k n)) - f c| := abs_sub_le M (f (x (k n))) (f c)
    rw [abs_sub_comm] at hN₁
    dsimp [Subsequence, ε] at hN₁ hN₂
    linarith

  rw [← M_eq_fc]
  apply upper_bd
  use d, d_in_Int

theorem WeierstrassMin {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
  (h_cont : FunctionContinuousOnSet (Set.Icc a b) f) :
  AxMonoConv → AxNIP →
  ∃ m ∈ (Set.Icc a b), ∀ x ∈ (Set.Icc a b), f m ≤ f x :=
by
  intro AxMonoConv AxNIP
  let g := - f
  have g_cont : FunctionContinuousOnSet (Set.Icc a b) g := by
    intro x hx
    unfold FunctionContinuousAt CauchyLimitFunction
    intro ε ε_pos
    obtain ⟨δ, δ_pos, hδ⟩ := h_cont x hx ε ε_pos
    use δ, δ_pos
    intro x₁ hx₁
    dsimp [g]
    simp
    specialize hδ x₁ hx₁
    have : |f x₁ - f x| = |-f x₁ + f x| := by calc |f x₁ - f x|
      _ = |-1| * |f x₁ - f x| := by simp
      _ = |(-1) * (f x₁ - f x)| := Eq.symm (abs_mul (-1) (f x₁ - f x))
      _ = |- f x₁ + f x| := by ring_nf
    rw [←this]
    exact hδ
  obtain ⟨m, hm, m_leq⟩ := WeierstrassMax hab g_cont AxMonoConv AxNIP
  use m, hm
  intro x hx
  specialize m_leq x hx
  dsimp [g] at m_leq
  linarith

theorem WeierstrassExtremeValue
  (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
  (h_cont : FunctionContinuousOnSet (Set.Icc a b) f) :
  AxNIP → AxMonoConv → AxSup →
  ((FunctionBddOnSet (Set.Icc a b) f) ∧
  (∃ M ∈ (Set.Icc a b), ∀ x ∈ (Set.Icc a b), f x ≤ f M) ∧
  (∃ m ∈ (Set.Icc a b), ∀ x ∈ (Set.Icc a b), f m ≤ f x)) :=
by
  intro AxNIP AxMonoConv AxSup
  exact ⟨WeierstrassBdd h_cont AxMonoConv, WeierstrassMax hab h_cont AxMonoConv AxNIP, WeierstrassMin hab h_cont AxMonoConv AxNIP⟩

#print axioms WeierstrassExtremeValue
