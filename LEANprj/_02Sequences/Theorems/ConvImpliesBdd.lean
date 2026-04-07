import LEANprj.defs
open Classical
open Real
noncomputable section

def max_upto (a : Sequence) : Sequence
  | 0 => |a 0|
  | (n + 1) => max (|a (n + 1)|) (max_upto a n)

#eval max_upto (λ n ↦ (n - 5)^2) 9

lemma le_max_upto
  (a : Sequence) (n k : ℕ) (h : k ≤ n) :
  |a k| ≤ max_upto a n :=
by
  induction' n with d hd
  · have : k = 0 := by exact Nat.eq_zero_of_le_zero h
    rw [this, max_upto]
  · rw [max_upto]
    by_cases h₁ : k = d + 1
    · exact le_sup_of_le_left (by rw [h₁])
    · push_neg at h₁
      have : k ≤ d := by
        have : k < d + 1 := by exact Nat.lt_of_le_of_ne h h₁
        exact Nat.le_of_lt_succ this
      exact le_sup_of_le_right (hd this)

theorem conv_implies_bdd
  {a : Sequence} (a_conv : Convergent a) :
  BoundedSequence a :=
by
  obtain ⟨c, hc⟩ := a_conv
  obtain ⟨n₀, hn₀⟩ := hc 1 (by linarith)
  let K₀ := max_upto a n₀
  let K := max K₀ (|c| + 1)
  have : K > 0 := by
    dsimp [K]
    simp
    right
    exact Right.add_pos_of_nonneg_of_pos (abs_nonneg c) (by linarith)
  use K, this
  intro n
  dsimp [K]
  by_cases h : n ≤ n₀
  · simp
    left
    exact le_max_upto a n₀ n h
  · simp
    right
    have : |a n| - |c| ≤ |a n - c| := by exact abs_sub_abs_le_abs_sub (a n) c
    calc |a n|
      _ ≤ |a n - c| + |c| := by linarith
      _ ≤ 1 + |c| := by
        simp
        push_neg at h
        specialize hn₀ n (by linarith)
        exact le_of_lt hn₀
    linarith





























  -- obtain ⟨c, hc⟩ := a_conv
  -- obtain ⟨n₀, hn₀⟩ := hc 1 (by linarith)
  -- unfold BoundedSequence
  -- let K₀ := max_upto a n₀
  -- let K := max K₀ (|c| + 1)
  -- have K_pos : K > 0 := by
  --   apply lt_of_lt_of_le zero_lt_one
  --   calc 1 ≤ |c| + 1 := le_add_of_nonneg_left (abs_nonneg c)
  --        _ ≤ K       := le_max_right _ _
  -- use K, K_pos
  -- intro n
  -- by_cases h : n ≤ n₀
  -- · dsimp [K]
  --   refine le_sup_of_le_left ?_
  --   dsimp [K₀]
  --   exact le_max_upto a n₀ n h
  -- · push_neg at h
  --   dsimp [K]
  --   refine le_sup_of_le_right ?_
  --   specialize hn₀ n (by linarith)
  --   have : |a n| - |c| ≤ |a n - c| := by exact abs_sub_abs_le_abs_sub (a n) c
  --   calc |a n|
  --   _ ≤ |c| + |a n - c| := by linarith
  --   _ ≤ |c| + 1 := by linarith


theorem ConvImpliesBdd' {a : Sequence} (a_conv : Convergent a) : BoundedSequence a := by
  -- Since a is convergent, there exists a limit q
  rcases a_conv with ⟨q, hq⟩
  -- Take ε = 1 in the definition of convergence
  specialize hq 1 (by norm_num)
  rcases hq with ⟨n₀, hn₀⟩

  -- For the tail (n ≥ n₀), we have |a n - q| < 1, so |a n| ≤ |q| + 1
  have tail_bound : ∀ n ≥ n₀, |a n| ≤ |q| + 1 := by
    intro n hn
    have := hn₀ n hn
    calc |a n| = |q + (a n - q)| := by ring_nf
         _ ≤ |q| + |a n - q| := abs_add q (a n - q)
         _ ≤ |q| + 1 := by linarith [this]

  -- Handle the initial segment differently based on whether n₀ = 0
  by_cases hn₀_zero : n₀ = 0
  · -- Special case when n₀ = 0 means the tail bound applies to all n
    use |q| + 1
    constructor
    · linarith [abs_nonneg q]
    · intro n
      exact tail_bound n (by rw [hn₀_zero]; exact Nat.zero_le n)

  · -- General case when n₀ > 0
    let initial_values := Finset.image a (Finset.range n₀)
    have init_nonempty : initial_values.Nonempty := by
      unfold initial_values
      apply Finset.Nonempty.image
      rw [Finset.nonempty_range_iff]
      exact hn₀_zero

    let M := initial_values.sup' init_nonempty abs
    let K := max M (|q| + 1)
    use K
    constructor
    · apply lt_of_lt_of_le (by linarith [abs_nonneg q]) (le_max_right _ _)
    · intro n
      by_cases h : n < n₀
      · -- Case when n < n₀
        have : a n ∈ initial_values := Finset.mem_image_of_mem a (Finset.mem_range.mpr h)
        exact le_trans (Finset.le_sup' abs this) (le_max_left _ _)
      · -- Case when n ≥ n₀
        push_neg at h
        exact le_trans (tail_bound n h) (le_max_right _ _)



theorem ConvImpliesBdd'' {a : Sequence} (a_conv : Convergent a) : BoundedSequence a := by
  -- A convergent sequence has a limit `q`.
  obtain ⟨q, h_conv⟩ := a_conv

  -- By the definition of convergence for ε = 1, there exists an index `n₀`
  -- such that for all `n ≥ n₀`, the terms `a n` are within distance 1 of `q`.
  obtain ⟨n₀, hn₀⟩ := h_conv 1 (by linarith)

  -- We will construct a bound `K` that works for all terms of the sequence.
  -- The bound must be larger than the absolute values of the initial `n₀` terms
  -- and also larger than the bound for the rest of the sequence (the "tail").

  -- For `n ≥ n₀`, we have `|a n| = |(a n - q) + q| ≤ |a n - q| + |q| < 1 + |q|`.
  -- So, `|q| + 1` serves as a bound for the tail of the sequence.

  -- Let's define a finite set of real numbers containing the absolute values
  -- of the first `n₀` terms, as well as the bound for the tail.
  let S : Finset ℝ := insert (|q| + 1) ((Finset.range n₀).image (fun i => |a i|))

  -- This set `S` is guaranteed to be non-empty because we explicitly inserted `|q| + 1`.
  have h_nonempty : S.Nonempty := Finset.insert_nonempty _ _

  -- As a non-empty, finite set of real numbers, `S` has a maximum element.
  -- We'll use this maximum as our overall bound `K`.
  let K := S.sup' h_nonempty id

  -- First, we must show that `K` is positive, as required by the definition of `BoundedSequence`.
  have hK_pos : K > 0 := by
    -- We know `|q| + 1` is an element of `S`.
    have h_mem : |q| + 1 ∈ S := Finset.mem_insert_self _ _
    -- Since `K` is the supremum of `S`, it must be greater than or equal to any element in `S`.
    have h_le : |q| + 1 ≤ K := Finset.le_sup' id h_mem
    -- Since `|q| ≥ 0`, we have `|q| + 1 > 0`.
    have h_pos : |q| + 1 > 0 := by linarith [abs_nonneg q]
    -- Therefore, `K` must also be positive.
    exact lt_of_le_of_lt' h_le h_pos

  -- Now, we use `K` to prove the sequence is bounded.
  use K, hK_pos
  intro n

  -- We consider two cases: `n` is in the initial part (`n < n₀`), or `n` is in the tail (`n ≥ n₀`).
  by_cases h_case : n < n₀

  · -- Case 1: `n` is in the initial part of the sequence.
    -- In this case, `|a n|` is an element of the set `S` by construction.
    have h_mem_S : |a n| ∈ S := by
      apply Finset.mem_insert_of_mem
      rw [Finset.mem_image]
      exact ⟨n, Finset.mem_range.mpr h_case, rfl⟩
    -- Any element of `S` is less than or equal to its supremum, `K`.
    exact Finset.le_sup' id h_mem_S

  · -- Case 2: n is in the tail of the sequence (n ≥ n₀).
  -- `push_neg` converts the hypothesis `¬(n < n₀)` into the more usable `n ≥ n₀`.
    push_neg at h_case

    -- First, we establish a bound for `|a n|` for `n ≥ n₀`.
    -- By the triangle inequality: `|a n| = |(a n - q) + q| ≤ |a n - q| + |q|`.
    -- From the definition of convergence, we know `|a n - q| < 1` for `n ≥ n₀`.
    -- Combining these gives `|a n| < 1 + |q|`.
    have h_tail_lt : |a n| < 1 + |q| :=
      calc
        |a n| = |(a n - q) + q|   := by rw [sub_add_cancel]
        _     ≤ |a n - q| + |q|   := by exact abs_add (a n - q) q
        _     < 1 + |q|           := by exact add_lt_add_right (hn₀ n h_case) |q|

    -- Second, we know that `K` is the supremum of the set `S`, and `|q| + 1` is an element of `S`.
    -- Therefore, `|q| + 1` must be less than or equal to `K`.
    have h_K_bound : |q| + 1 ≤ K := Finset.le_sup' id (Finset.mem_insert_self _ _)

    -- Finally, we combine our two findings: `|a n| < 1 + |q|` and `1 + |q| ≤ K`.
    -- The transitivity of `≤` allows us to conclude that `|a n| ≤ K`.
    -- We use `le_of_lt` to convert our strict inequality `h_tail_lt` to a non-strict one.
    rw [add_comm] at h_tail_lt
    exact (le_of_lt h_tail_lt).trans h_K_bound



theorem ConvImpliesBdd''' {a : Sequence} (a_conv : Convergent a) : BoundedSequence a := by
  rcases a_conv with ⟨q, hq⟩

  -- tail control with ε = 1
  have h1 : ∃ n₀ : ℕ, ∀ n ≥ n₀, |a n - q| < 1 := by
    simpa using hq 1 (by linarith)

  rcases h1 with ⟨n₀, hn₀⟩

  -- Define an explicit bound for the initial segment: sum of absolutes + 1
  let K0 : ℝ := (∑ i ∈ Finset.range n₀, |a i|) + 1
  have K0_pos : 0 < K0 := by
    have : (0 : ℝ) < (1 : ℝ) := by linarith
    have hsum : 0 ≤ (∑ i ∈ Finset.range n₀, |a i|) := by
      exact Finset.sum_nonneg (by intro i hi; exact abs_nonneg (a i))
    linarith

  -- For n < n₀, we have |a n| ≤ ∑_{i<n₀} |a i| ≤ K0
  have h_init : ∀ n : ℕ, n < n₀ → |a n| ≤ K0 := by
    intro n hn
    have hnmem : n ∈ Finset.range n₀ := by
      simpa [Finset.mem_range] using hn
    have hle_sum : |a n| ≤ ∑ i ∈ Finset.range n₀, |a i| := by
      -- standard lemma: a term is ≤ the sum of nonnegative terms
      have := Finset.single_le_sum (fun i hi => abs_nonneg (a i)) hnmem
      simpa using this
    dsimp [K0]
    linarith

  -- For n ≥ n₀, use triangle inequality to get |a n| ≤ |q| + 1
  have h_tail : ∀ n : ℕ, n ≥ n₀ → |a n| ≤ |q| + 1 := by
    intro n hn
    have hlt : |a n - q| < 1 := hn₀ n hn
    have htri : |a n| ≤ |a n - q| + |q| := by
      -- |a| = |(a-q)+q| ≤ |a-q|+|q|
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (abs_add (a n - q) q)
    have : |a n| < 1 + |q| := lt_of_le_of_lt htri (by linarith)
    have : |a n| ≤ 1 + |q| := le_of_lt this
    simpa [add_comm, add_left_comm, add_assoc] using this

  -- Final bound: K = max K0 (|q| + 1)
  refine ⟨max K0 (|q| + 1), ?_, ?_⟩
  · -- positivity
    have : 0 < K0 := K0_pos
    exact lt_of_lt_of_le this (le_max_left _ _)
  · intro n
    by_cases hn : n < n₀
    · exact le_trans (h_init n hn) (le_max_left _ _)
    · have hn' : n ≥ n₀ := le_of_not_gt hn
      exact le_trans (h_tail n hn') (le_max_right _ _)
