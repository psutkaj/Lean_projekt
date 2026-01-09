import LEANprj.defs

theorem UniquenessSeq
  (a : ℕ → ℝ) (p q : ℝ) (h₁ : ConvergesTo a p) (h₂ : ConvergesTo a q) : p = q :=
by
  by_contra hne
  have hab : |p - q| > 0 := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hpos : 0 < |p - q| / 2 := half_pos hab
  rcases h₁ (|p - q| / 2) hpos with ⟨n₁,hn₁⟩
  rcases h₂ (|p - q| / 2) hpos with ⟨n₂,hn₂⟩
  let nₒ := max n₁ n₂
  have hn₁e : |a nₒ - p| < |p - q| / 2 := hn₁ nₒ (le_max_left  n₁ n₂)
  have hn₂e : |a nₒ - q| < |p - q| / 2 := hn₂ nₒ (le_max_right n₁ n₂)
  have : |p - q| < |p - q| := by
    calc
      |p - q| = |(p - a nₒ) + (a nₒ - q)| := by simp [sub_add_sub_cancel]
      _ ≤ |p - a nₒ| + |a nₒ - q| := abs_add _ _
      _ = |a nₒ - p| + |a nₒ - q| := by rw [abs_sub_comm p (a nₒ)]
      _ < |p - q| / 2 + |p - q| / 2 := add_lt_add hn₁e hn₂e
      _ = |p - q| := by ring
  linarith



theorem UniquenessSeq'
  (a : ℕ → ℝ) (p q : ℝ) (h₁ : ConvergesTo a p) (h₂ : ConvergesTo a q) : p = q :=
by
  -- Proof by contradiction: assume p ≠ q
  by_contra h
  push_neg at h
  -- Let ε = |p - q|/2 > 0
  let ε := |p - q| / 2
  have ε_pos : ε > 0 := by
    apply half_pos
    exact abs_pos.mpr (sub_ne_zero_of_ne h)

  -- From h₁, there exists n₁ such that for all n ≥ n₁, |a n - p| < ε
  obtain ⟨n₁, hn₁⟩ := h₁ ε ε_pos
  -- From h₂, there exists n₂ such that for all n ≥ n₂, |a n - q| < ε
  obtain ⟨n₂, hn₂⟩ := h₂ ε ε_pos

  -- Let n₀ = max(n₁, n₂)
  let n₀ := max n₁ n₂
  -- For n ≥ n₀, both inequalities hold
  have h₁' := hn₁ n₀ (le_max_left _ _)
  have h₂' := hn₂ n₀ (le_max_right _ _)

  -- Now we reach a contradiction using the triangle inequality
  have : |p - q| < |p - q| := calc
    |p - q| = |(p - a n₀) + (a n₀ - q)| := by ring
    _ ≤ |p - a n₀| + |a n₀ - q| := abs_add _ _
    _ = |a n₀ - p| + |a n₀ - q| := by rw [abs_sub_comm]
    _ < ε + ε := add_lt_add h₁' h₂'
    _ = 2 * ε := by ring
    _ = 2 * (|p - q| / 2) := by rfl
    _ = |p - q| := by field_simp

  -- This is impossible
  exact lt_irrefl _ this


theorem UniquenessSeq''
  (a : ℕ → ℝ) (p q : ℝ) (h₁ : ConvergesTo a p) (h₂ : ConvergesTo a q) : p = q :=
by
  -- We prove this by contradiction. Assume that the limits p and q are not equal.
  by_contra h_neq

  -- If p and q are different, the distance between them, |p - q|, is strictly positive.
  have h_dist_pos : |p - q| > 0 := by
    -- `abs_pos` states that the absolute value is positive if the argument is non-zero.
    -- `sub_ne_zero` states that p - q is non-zero if p ≠ q.
    exact abs_pos.mpr (sub_ne_zero.mpr h_neq)

  -- The core idea is to choose an ε that is too small for the sequence to be
  -- close to both p and q simultaneously. Let ε be half of the distance between p and q.
  -- The open interval (p - ε, p + ε) and (q - ε, q + ε) will be disjoint.
  let ε := |p - q| / 2
  have hε_pos : ε > 0 := half_pos h_dist_pos

  -- From the hypothesis `h₁` (a converges to p), for our chosen ε, there exists an
  -- index `n₁` such that all subsequent terms of the sequence are within ε of p.
  rcases h₁ ε hε_pos with ⟨n₁, hn₁⟩

  -- Similarly, from `h₂` (a converges to q), there is an index `n₂` such that
  -- all subsequent terms are within ε of q.
  rcases h₂ ε hε_pos with ⟨n₂, hn₂⟩

  -- We need a point in the sequence that is close to *both* p and q.
  -- We can pick an index `N` that is greater than or equal to both `n₁` and `n₂`.
  -- The maximum of `n₁` and `n₂` is a suitable choice.
  let N := max n₁ n₂

  -- By construction of N, the term `a N` must satisfy both closeness conditions.
  have h_close_p : |a N - p| < ε := hn₁ N (Nat.le_max_left n₁ n₂)
  have h_close_q : |a N - q| < ε := hn₂ N (Nat.le_max_right n₁ n₂)

  -- Now, we use the triangle inequality to show this situation is impossible.
  -- We will derive the contradiction that |p - q| is strictly less than itself.
  have h_contr : |p - q| < |p - q| := calc
    |p - q| = |(p - a N) + (a N - q)|   := by rw [sub_add_sub_cancel]
    _       ≤ |p - a N| + |a N - q|   := abs_add _ _
    _       = |a N - p| + |a N - q|   := by rw [abs_sub_comm p (a N)]
    _       < ε + ε                   := by gcongr -- Applies h_close_p and h_close_q to the sum
    _       = |p - q|                 := by
                                           -- Substitute back ε = |p - q| / 2 and simplify.
                                           simp [ε, add_halves]

  -- The strict inequality `|p - q| < |p - q|` is a logical contradiction.
  -- Thus, our initial assumption `p ≠ q` must be false.
  exact lt_irrefl |p - q| h_contr


theorem UniquenessSeq'''
  (a : ℕ → ℝ) (p q : ℝ) (h₁ : ConvergesTo a p) (h₂ : ConvergesTo a q) : p = q :=
by
  classical
  by_contra hpq
  -- From `p ≠ q` we get `0 < |p - q|`, so we can use ε = |p-q|/2
  have hpq' : p - q ≠ 0 := by
    intro h0
    apply hpq
    -- if p - q = 0 then p = q
    linarith
  have hpos : 0 < |p - q| := by
    -- `abs_pos` needs `p - q ≠ 0`
    simpa [abs_pos] using (abs_pos.mpr hpq')

  set ε : ℝ := |p - q| / 2
  have hε : ε > 0 := by
    -- half of a positive number is positive
    have : (0 : ℝ) < |p - q| / 2 := by nlinarith
    simpa [ε] using this

  -- get tails close to p and close to q
  rcases h₁ ε hε with ⟨N₁, hN₁⟩
  rcases h₂ ε hε with ⟨N₂, hN₂⟩

  -- take n ≥ max N₁ N₂
  let N := max N₁ N₂
  have hNp : |a N - p| < ε := by
    apply hN₁ N
    exact le_of_max_le_left (le_rfl)
  have hNq : |a N - q| < ε := by
    apply hN₂ N
    exact le_of_max_le_right (le_rfl)

  -- now use triangle inequality:
  -- |p - q| = |(p - aN) + (aN - q)| ≤ |p - aN| + |aN - q| < ε + ε = |p-q|
  have htri : |p - q| ≤ |p - a N| + |a N - q| := by
    have hdecomp : p - q = (p - a N) + (a N - q) := by ring
    -- Rewrite the LHS using congrArg; no simp with [hdecomp]
    -- (This gives exactly the equality we need.)
    have habs : |p - q| = |(p - a N) + (a N - q)| :=
      congrArg (fun t => |t|) hdecomp
    -- Now triangle inequality
    -- abs_add (x) (y) : |x + y| ≤ |x| + |y|
    -- so after rewriting by habs we're done
    simpa [habs] using (abs_add (p - a N) (a N - q))

  have hlt1 : |p - a N| < ε := by
    -- |p - aN| = |aN - p|
    simpa [abs_sub_comm] using hNp
  have hlt2 : |a N - q| < ε := hNq

  have hsum : |p - a N| + |a N - q| < |p - q| := by
    have hsum' : |p - a N| + |a N - q| < ε + ε :=
      add_lt_add hlt1 hlt2
    -- ε+ε = |p-q| since ε = |p-q|/2
    have : ε + ε = |p - q| := by
      -- unfold ε and do linear arithmetic
      -- (|p-q|/2) + (|p-q|/2) = |p-q|
      simp [ε,  div_eq_mul_inv]
      ring
    -- conclude
    exact lt_of_lt_of_eq hsum' this

  have : |p - q| < |p - q| := lt_of_le_of_lt htri hsum
  exact lt_irrefl _ this
