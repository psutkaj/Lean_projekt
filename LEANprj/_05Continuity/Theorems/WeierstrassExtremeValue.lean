import LEANprj.defs
import LEANprj._05Continuity.Theorems.AlgebraContinuousFun
import LEANprj._05Continuity.Theorems.IntermediateValue
import LEANprj._04Functions.Theorems.UniquenessFun
import LEANprj._04Functions.Theorems.SandwichFun
import LEANprj._02Sequences.Theorems.BolzanoWeierstrass

theorem WeierstrassBdd
  (f : ℝ → ℝ) (a b : ℝ) (_h_ab : a ≤ b) (Int : Set ℝ) (hInt : Int = Set.Icc a b)
  (h_cont : FunctionContinuousOnSet Int f) :
  FunctionBddOnSet Int f := by
  by_contra h_unbdd
  unfold FunctionBddOnSet at h_unbdd
  push_neg at h_unbdd
  let x_seq : ℕ → ℝ := λ n => Classical.choose (h_unbdd (n + 1) (by linarith))
  have h_x_seq_prop : ∀ n, x_seq n ∈ Int ∧ |f (x_seq n)| ≥ n + 1 := fun n => Classical.choose_spec (h_unbdd (n + 1) (by linarith))
  have h_x_seq_bounded : BoundedSequence x_seq := by
    unfold BoundedSequence
    let K := max (|a| + |b| + 1) 1
    use K, by dsimp [K]; simp
    intro n
    have h := (h_x_seq_prop n).1
    rw [hInt] at h
    simp at h
    cases' h with h_left h_right
    rw [abs_lt]
    dsimp [K]
    constructor
    · calc -max (|a| + |b| + 1) 1
      _ ≤ - (|a| + |b| + 1) := neg_le_neg (le_max_left _ _)
      _ < -|a| := by
        simp
        refine neg_lt_iff_pos_add'.mpr ?_
        have : |b| ≥ 0 := abs_nonneg b
        calc 0 < 1 := Real.zero_lt_one
        _ ≤ |b| + 1 := by exact le_add_of_nonneg_left this
      _ ≤ a := by exact neg_abs_le a
      _ ≤ x_seq n := h_left
    · calc x_seq n
        _ ≤ b := h_right
        _ < |b| + 1 := by
          have : b ≤ |b| := le_abs_self b
          linarith
        _ ≤ |a| + |b| + 1 := by simp
        _ ≤ K := by dsimp [K]; simp
  obtain ⟨k, hk_inc, c, hk_conv⟩ := BolzanoWeierstrass x_seq h_x_seq_bounded
  have hc_in_Int : c ∈ Int := by
    rw [hInt]
    simp
    have h_closure : ∀ n, x_seq (k n) ∈ Int := by
      intro n
      exact (h_x_seq_prop (k n)).1
    constructor
    · by_contra hnot
      push_neg at hnot
      let ε := (a - c) / 2
      have ε_pos : ε > 0 := by dsimp[ε]; linarith
      obtain ⟨n₀, hn₀⟩ := hk_conv ε ε_pos
      specialize hn₀ n₀ (by linarith)
      rw [hInt] at h_closure
      have h_x_ge_a := (h_closure n₀).1
      rw [Subsequence] at hn₀
      simp at hn₀
      have upper_bound : c + ε = (a + c)/2 := by ring
      have upper_bound_lt_a : (a + c)/2 < a := by linarith
      rw [abs_lt] at hn₀
      have h_x_lt_a : x_seq (k n₀) < a := by linarith
      linarith
    · by_contra hnot
      push_neg at hnot
      let ε := (c - b) / 2
      have ε_pos : ε > 0 := by dsimp [ε]; linarith
      have hε : ε > 0 := by linarith
      obtain ⟨N, hN⟩ := hk_conv ε hε
      specialize hN N (by linarith)
      rw [hInt] at h_closure
      have h_x_le_b := (h_closure N).2
      rw [Subsequence] at hN
      simp at hN
      rw [abs_lt] at hN
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
    simp at hN
    by_cases h_eq : x_seq (k n) = c
    · rw [← h_eq]; simp; exact hε
    · apply hδ
      constructor
      · rw [abs_pos]; exact sub_ne_zero.mpr h_eq
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
    have : |f (x_seq (k n)) - f c| = |f c - f (x_seq (k n))| := by exact abs_sub_comm (f (x_seq (k n))) (f c)
    have : |f c| + |f (x_seq (k n)) - f c| < |f c| + 1 := by linarith
    linarith
  have h_seq_bound : |f (x_seq (k n))| ≥ n + 1 := by
    have : k n ≥ n := StrictlyIncreasingSequenceN_ge_id k hk_inc n
    have : |f (x_seq (k n))| ≥ k n + 1 := (h_x_seq_prop (k n)).2
    have : k n + 1 ≥ n + 1 := by linarith
    trans k n + 1
    · (expose_names; exact this_2)
    · simp; linarith
  have h_n_large : n > |f c| := by
    have : (n : ℝ) ≥ m := Nat.cast_le.mpr (le_max_right N m)
    linarith
  linarith

-- theorem WeierstrassMax'
--   (f : ℝ → ℝ) (a b : ℝ) (h_ab : a ≤ b) (Int : Set ℝ) (hInt : Int = Set.Icc a b)
--   (h_cont : FunctionContinuousOnSet Int f) :
--   ∃ M ∈ Int, ∀ x ∈ Int, f x ≤ f M := by
--   classical
--   -- The interval Int = [a,b] is nonempty
--   have h_nonempty : Int.Nonempty := by
--     have ha_mem_Icc : a ∈ Set.Icc a b := ⟨le_rfl, h_ab⟩
--     have ha_mem_Int : a ∈ Int := by simpa [hInt] using ha_mem_Icc
--     exact ⟨a, ha_mem_Int⟩
--   -- Consider the image S = f(Int)
--   let S : Set ℝ := f '' Int
--   have hS_nonempty : S.Nonempty := by
--     rcases h_nonempty with ⟨x, hx⟩
--     exact ⟨f x, ⟨x, hx, rfl⟩⟩
--     -- f is bounded on Int, hence S is bounded above
--   have h_bdd : FunctionBddOnSet Int f :=
--     WeierstrassBdd f a b h_ab Int hInt h_cont
--   rcases h_bdd with ⟨K, hK_pos, hK⟩
--   have hS_bddAbove : BddAbove S := by
--     refine ⟨K, ?_⟩
--     intro y hy
--     rcases hy with ⟨x, hxInt, rfl⟩
--     have hfLt : |f x| < K := hK x hxInt
--     have hfLe : f x ≤ |f x| := le_abs_self _
--     exact le_trans hfLe (le_of_lt hfLt)
--   -- Let M0 be the supremum of S
--   let M0 : ℝ := sSup S

--   -- Every point of S is ≤ M0
--   have h_le_M0 : ∀ y ∈ S, y ≤ M0 := by
--     intro y hy
--     exact le_csSup hS_bddAbove hy
--   -- For each n, choose xₙ ∈ Int with f xₙ > M0 - 1/(n+1)
--   have h_approx : ∀ n : ℕ, ∃ x ∈ Int, M0 - (1 : ℝ) / (n+1) < f x := by
--     intro n
--     -- this will use the definition/properties of sSup on S
--     sorry
--   choose x hxInt hx_lt using h_approx

--   --choose x hxInt hx_lt using h_approx
--   -- Now x : ℕ → ℝ, with x n ∈ Int and M0 - 1/(n+1) < f (x n) for all n
--   have hx_in_Icc : ∀ n, x n ∈ Set.Icc a b := by
--     intro n
--     simpa [hInt] using hxInt n
--   -- The sequence x is bounded, since it stays in [a, b]
--   have hx_bdd : BoundedSequence x := by
--     -- for example, one can bound |x n| by max (|a|) (|b|) + 1
--     sorry
--   -- Apply Bolzano–Weierstrass to obtain a convergent subsequence of x
--   obtain ⟨φ, hφ_inc, c, hconv⟩ := BolzanoWeierstrass x hx_bdd
--   have hconv' : ConvergesTo (x ∘ φ) c := by
--     simpa [Subsequence] using hconv
--   -- The subsequence x ∘ φ still lies in Int
--   have hxφ_Int : ∀ n, x (φ n) ∈ Int := by
--     intro n
--     exact hxInt (φ n)
--   -- Hence its limit point c lies in Int (indeed in [a,b])
--   have hc_Int : c ∈ Int := by
--     -- use that Int = [a,b] is closed and contains all x (φ n),
--     -- together with the convergence hconv'
--     sorry
--   sorry

theorem Continuous_Implies_Sequential
  (f : ℝ → ℝ) (c : ℝ) (h_cont : FunctionContinuousAt f c)
  (x : ℕ → ℝ) (h_conv : ConvergesTo x c) :
  ConvergesTo (f ∘ x) (f c) := by
  -- Důkaz je přímočarý:
  -- 1. Vezmi libovolné ε > 0.
  intro ε hε
  -- 2. Díky spojitosti f (h_cont) existuje δ > 0.
  obtain ⟨δ, hδ_pos, h_f_delta⟩ := h_cont ε hε
  -- 3. Díky konvergenci x (h_conv) existuje n₀, od kterého jsou x_n blíže než δ.
  obtain ⟨n₀, h_x_delta⟩ := h_conv δ hδ_pos
  -- 4. Spoj to dohromady.
  use n₀
  intro n hn
  -- x_n je blízko c (o δ), takže f(x_n) musí být blízko f(c) (o ε).
  simp
  by_cases h_xn_eq_c : x n = c
  · rw [h_xn_eq_c]
    simp
    exact hε
  · apply h_f_delta
    constructor
    · exact abs_sub_pos.mpr h_xn_eq_c
    · exact h_x_delta n hn

theorem WeierstrassMax
  (f : ℝ → ℝ) (a b : ℝ) (h_ab : a ≤ b) (Int : Set ℝ) (hInt : Int = Set.Icc a b)
  (h_cont : FunctionContinuousOnSet Int f) :
  ∃ M ∈ Int, ∀ x ∈ Int, f x ≤ f M := by
  let S := {f y | y ∈ Int}
  have S_nonempty : S.Nonempty := by
    use f a
    dsimp [S]
    use a
    constructor
    rw [hInt]
    simpa
    rfl
  have S_bdd : BoundedSet S := by
    unfold BoundedSet
    obtain ⟨c, c_pos, hc⟩ := WeierstrassBdd f a b h_ab Int hInt h_cont
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
    · exact le_of_lt hc
  obtain ⟨M, IsSupM, UniqueM⟩ := exists_unique_supremum S S_nonempty S_upper_bdd
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
  have x_exists : ∀ n : ℕ, ∃ x ∈ Int, f x = y n := by
    intro n
    exact y_in_S n
  choose x x_in_Int fx_eq_y using x_exists
  rw [hInt] at x_in_Int
  have x_bdd : BoundedSequence x := by
    unfold BoundedSequence
    use max |a| |b| + 1
    constructor
    · simp
      have : max |a| |b| ≥ 0 := by
        exact le_sup_of_le_right (by exact abs_nonneg b)
      exact lt_add_of_nonneg_of_lt this (by simp)
    · intro n

      specialize x_in_Int n
      simp at x_in_Int
      rw [abs_lt]
      constructor
      · calc - (max (|a|) (|b|) + 1)
        _ < - max (|a|) (|b|) := by linarith
        _ ≤ - |a| := neg_le_neg (le_max_left _ _)
        _ ≤ a := neg_abs_le a
        _ ≤ x n := x_in_Int.1
      · calc x n
        _ ≤ b := x_in_Int.2
        _ ≤ |b| := le_abs_self b
        _ ≤ max (|a|) (|b|) := le_max_right _ _
        _ < max (|a|) (|b|) + 1 := by linarith
  obtain ⟨k, hk_inc, hk_conv⟩ := BolzanoWeierstrass x x_bdd
  obtain ⟨c, hc⟩ := hk_conv
  have c_in_Int : c ∈ Int := by
    rw [hInt]
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
    apply Continuous_Implies_Sequential f c h_cont_c
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
        _ > M - ε             := by
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
    obtain ⟨N1, hN1⟩ := h_lim_construction ε ε_pos
    obtain ⟨N2, hN2⟩ := h_lim_continuity ε ε_pos
    let n := max N1 N2
    specialize hN1 n (le_max_left _ _)
    specialize hN2 n (le_max_right _ _)
    have : |M - f c| ≤ |M - f (x (k n))| + |f (x (k n)) - f c| := abs_sub_le M (f (x (k n))) (f c)
    rw [abs_sub_comm] at hN1
    dsimp [Subsequence, ε] at hN1 hN2
    linarith

  rw [← M_eq_fc]
  apply upper_bd
  use d, d_in_Int



theorem WeierstrassMin
  (f : ℝ → ℝ) (a b : ℝ) (h_ab : a ≤ b) (Int : Set ℝ) (hInt : Int = Set.Icc a b)
  (h_cont : FunctionContinuousOnSet Int f) :
  ∃ m ∈ Int, ∀ x ∈ Int, f m ≤ f x := by
  let g := λ x ↦ - f x
  have g_cont : FunctionContinuousOnSet Int g := by
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
      _ = |(-1) * (f x₁ - f x)| := by exact Eq.symm (abs_mul (-1) (f x₁ - f x))
      _ = |- f x₁ + f x| := by ring_nf
    rw [←this]
    exact hδ
  obtain ⟨m, hm, m_leq⟩ := WeierstrassMax g a b h_ab Int hInt g_cont
  use m, hm
  intro x hx
  specialize m_leq x hx
  dsimp [g] at m_leq
  linarith

theorem WeierstrassExtremeValue
  (f : ℝ → ℝ) (a b : ℝ) (h_ab : a ≤ b) (Int : Set ℝ) (hInt : Int = Set.Icc a b)
  (h_cont : FunctionContinuousOnSet Int f) :
  (FunctionBddOnSet Int f) ∧
  (∃ M ∈ Int, ∀ x ∈ Int, f x ≤ f M) ∧
  (∃ m ∈ Int, ∀ x ∈ Int, f m ≤ f x) := by
  exact ⟨WeierstrassBdd f a b h_ab Int hInt h_cont, WeierstrassMax f a b h_ab Int hInt h_cont, WeierstrassMin f a b h_ab Int hInt h_cont⟩
