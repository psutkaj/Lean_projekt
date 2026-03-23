import LEANprj.defs

--GPT 5.1

lemma prefix_bounded (a : ℕ → ℝ) :
    ∀ N : ℕ, ∃ M : ℝ, ∀ n ≤ N, |a n| ≤ M := by
  intro N
  induction' N with N ih
  · -- base case N = 0
    refine ⟨|a 0|, ?_⟩
    intro n hn
    -- if n ≤ 0, then n = 0
    have : n = 0 := Nat.eq_zero_of_le_zero hn
    simp [this]
  · -- inductive step: N.succ
    -- from induction: ∃ M0, ∀ n ≤ N, |a n| ≤ M0
    rcases ih with ⟨M0, hM0⟩
    -- new bound: max M0 |a (N.succ)|
    refine ⟨max M0 |a N.succ|, ?_⟩
    intro n hn
    have h' : n ≤ N ∨ n = N.succ := by
      -- from n ≤ N.succ, either n < N.succ or n = N.succ
      have := Nat.lt_or_eq_of_le hn
      cases this with
      | inl hlt =>
          -- n < N.succ ⇒ n ≤ N
          have : n ≤ N := Nat.le_of_lt_succ hlt
          exact Or.inl this
      | inr heq =>
          exact Or.inr heq
    cases h' with
    | inl hle =>
        -- use old bound and compare with max
        have : |a n| ≤ M0 := hM0 n hle
        exact le_trans this (le_max_left _ _)
    | inr heq =>
        -- n = N.succ
        subst heq
        have : |a N.succ| ≤ max M0 |a N.succ| := le_max_right _ _
        simp

theorem cauchy_implies_bdd {a : ℕ → ℝ} (h : CauchySequence a) : BoundedSequence a := by
  -- take ε = 1 in the definition of CauchySequence
  have hpos : (0 : ℝ) < 1 := by exact zero_lt_one
  obtain ⟨N, hN⟩ := h 1 hpos

  -- finite prefix up to N+1 is bounded
  obtain ⟨M0, hM0⟩ := prefix_bounded a (N + 1)

  -- "tail bound": for n > N+1, |a n| ≤ |a (N+1)| + 1
  have h_tail : ∀ n > N + 1, |a n| ≤ |a (N + 1)| + 1 := by
    intro n hn
    -- First show n > N, so we can use the Cauchy condition with index N
    have hn' : n > N := Nat.lt_trans (Nat.lt_succ_self N) hn
    have hN1 : N + 1 > N := Nat.lt_succ_self N

    -- Cauchy condition with m = N+1
    have hdist : |a n - a (N + 1)| < 1 :=
      hN n (N + 1) ⟨hn', hN1⟩
    have hdist_le : |a n - a (N + 1)| ≤ 1 := le_of_lt hdist

    -- triangle inequality on a n = (a n - a (N+1)) + a (N+1)
    calc
      |a n| = |a n - a (N + 1) + a (N + 1)| := by
        ring_nf
      _ ≤ |a n - a (N + 1)| + |a (N + 1)| := by
        have := abs_add (a n - a (N + 1)) (a (N + 1))
        simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
      _ ≤ 1 + |a (N + 1)| := by
        have := add_le_add_right hdist_le |a (N + 1)|
        simpa [add_comm, add_left_comm, add_assoc] using this
    linarith

  -- choose a global bound M as the max of prefix bound and tail bound, plus 1 for strict inequality
  let M : ℝ := max M0 (|a (N + 1)| + 1) + 1
  refine ⟨M, ?_⟩
  constructor
  · have h1 : 0 ≤ |a (N + 1)| := abs_nonneg _
    have h2 : 0 < |a (N + 1)| + 1 := by linarith
    have h3 : 0 < max M0 (|a (N + 1)| + 1) := lt_max_of_lt_right h2
    linarith
  intro n
  by_cases hcase : n ≤ N + 1
  · -- prefix case: n ≤ N+1
    have : |a n| ≤ M0 := hM0 n hcase
    calc |a n| ≤ M0 := this
         _ ≤ max M0 (|a (N + 1)| + 1) := le_max_left _ _
         _ ≤ max M0 (|a (N + 1)| + 1) + 1 := by linarith
  · -- tail case: n > N+1
    have hn : N + 1 < n := Nat.lt_of_not_ge hcase
    have : |a n| ≤ |a (N + 1)| + 1 := h_tail n hn
    calc |a n| ≤ |a (N + 1)| + 1 := this
         _ ≤ max M0 (|a (N + 1)| + 1) := le_max_right _ _
         _ ≤ max M0 (|a (N + 1)| + 1) + 1 := by linarith
