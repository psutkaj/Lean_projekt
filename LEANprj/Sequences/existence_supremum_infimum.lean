import LEANprj.Sequences.definitions
noncomputable section
open Classical

variable (A : Set ℝ) (l₀ u₀ : ℝ) (n : ℕ)

-- chci si vytvorit pulleni intervalu, a aby ho rozeznavalo simp
@[simp] def mid (l u : ℝ) : ℝ := (l + u) / 2

lemma sub_mid (l u : ℝ) : u - mid l u = (u - l) / 2 := by
  simp
  ring
lemma mid_sub (l u : ℝ) : mid l u - l = (u - l) / 2 := by
  simp
  ring

-- definuju krok puleni, beru bud levou nebo pravou cast, podle toho kde mam a ∈ A
def step (l u : ℝ) : ℝ × ℝ :=
  if _ : ∃ a : A, mid l u < a then (mid l u, u) else (l, mid l u)

-- definuju si posloupnost dvojic (lₙ, uₙ)
def luNext : ℕ → ℝ × ℝ
  | 0 => (l₀, u₀)
  | n+1 => step A (luNext n).1 (luNext n).2

-- zadefinuju si posloupnosti pro samostatne lₙ, uₙ
def lSeq (n : ℕ) : ℝ := (luNext A l₀ u₀ n).1
def uSeq (n : ℕ) : ℝ := (luNext A l₀ u₀ n).2

lemma left_le_mid {l u : ℝ} (h : l ≤ u) : l ≤ mid l u := by
  unfold mid
  have : l = (l + l) / 2 := by ring
  have : l + l ≤ l + u := by linarith
  linarith

lemma mid_le_right {l u : ℝ} (h : l ≤ u) : mid l u ≤ u := by
  unfold mid
  have : (u + u) / 2 = u := by ring
  have : u + l ≤ u + u := by linarith
  linarith

-- exsitence a jednoznacnost suprema (infima)
theorem exists_supremum (A : Set ℝ) (hA : A.Nonempty) (hUpperBdd : ∃ u : ℝ, ∀ a ∈ A, a ≤ u): ∃ s : ℝ, IsSup A s := by
  obtain ⟨l₀, hl₀⟩ := hA
  obtain ⟨u₀, hu₀⟩ := hUpperBdd
  have h_l₀_leq_u₀ : l₀ ≤ u₀ := by exact hu₀ l₀ hl₀
  -- lₙ ≤ uₙ
  have lₙ_leq_uₙ : ∀ n : ℕ, lSeq A l₀ u₀ n ≤ uSeq A l₀ u₀ n := by
    intro n
    induction' n with d hd
    · simp [lSeq, uSeq, luNext]
      exact h_l₀_leq_u₀
    · simp [lSeq, uSeq, luNext]
      let l_d := lSeq A l₀ u₀ d
      let u_d := uSeq A l₀ u₀ d
      let lu_d_next := step A l_d u_d
      change lu_d_next.1 ≤ lu_d_next.2
      unfold lu_d_next step mid
      simp_all only [Subtype.exists, exists_prop, dite_eq_ite, l_d, u_d]
      split
      next h =>
        simp_all only
        obtain ⟨w, h⟩ := h
        obtain ⟨left, right⟩ := h
        linarith
      next h =>
        simp_all only [not_exists, not_and, not_lt]
        linarith

  -- horni zavora
  have upperBound : ∀ n : ℕ, ∀ a ∈ A, a ≤ uSeq A l₀ u₀ n := by
    intro n a ha
    induction' n with d hd
    · unfold uSeq luNext
      simp
      exact hu₀ a ha
    · unfold uSeq luNext step
      simp only [Subtype.exists, exists_prop, dite_eq_ite]
      split_ifs with h
      · exact hd
      · push_neg at h
        exact h a ha

  -- do sebe vlozene intervaly neprazdne
  have nestedNonempty : ∀ n : ℕ, ∃ a ∈ A, lSeq A l₀ u₀ n ≤ a ∧ a ≤ uSeq A l₀ u₀ n := by
    intro n
    induction' n with d hd
    · use l₀
      constructor
      · exact hl₀
      · constructor
        · simp [lSeq, luNext]
        · simp [uSeq, luNext]
          exact hu₀ l₀ hl₀
    · obtain ⟨a, ha, ha_l, ha_u⟩ := hd
      unfold lSeq uSeq luNext step
      simp only [Subtype.exists, exists_prop, dite_eq_ite]
      split_ifs with h
      · obtain ⟨w, hw_mem, hw_gt⟩ := h
        use w
        refine ⟨hw_mem, ?_, upperBound d w hw_mem⟩
        show mid (luNext A l₀ u₀ d).1 (luNext A l₀ u₀ d).2 ≤ w
        have : lSeq A l₀ u₀ d = (luNext A l₀ u₀ d).1 := rfl
        have : uSeq A l₀ u₀ d = (luNext A l₀ u₀ d).2 := rfl
        exact le_of_lt hw_gt
      · push_neg at h
        use a
        refine ⟨ha, ha_l, ?_⟩
        show a ≤ mid (lSeq A l₀ u₀ d) (uSeq A l₀ u₀ d)
        exact h a ha

  -- puleni intervalu
  have shrink : ∀ n : ℕ, uSeq A l₀ u₀ (n+1) - lSeq A l₀ u₀ (n+1) = (uSeq A l₀ u₀ n - lSeq A l₀ u₀ n) / 2 := by
    intro n
    set l := lSeq A l₀ u₀ n with hl
    set u := uSeq A l₀ u₀ n with hu
    have : lSeq A l₀ u₀ n = (luNext A l₀ u₀ n).1 := rfl
    have : uSeq A l₀ u₀ n = (luNext A l₀ u₀ n).2 := rfl
    by_cases hRight : ∃ a : A, mid l u < a
    · have h_l_succ : lSeq A l₀ u₀ (n+1) = mid l u := by
        simp [lSeq, luNext, step]
        split_ifs with h
        · simp
          rw [hl, hu]
          unfold lSeq uSeq
          ring
        · simp
          rw [hl, hu]
          unfold lSeq uSeq
          simp_all only [mid, Subtype.exists, exists_prop, l, u]
      have h_u_succ : uSeq A l₀ u₀ (n+1) = u := by
        simp [uSeq, luNext, step]
        split_ifs with h
        · simp
          exact hu
        · simp
          rw [hu]
          unfold uSeq
          simp_all only [mid, Subtype.exists, exists_prop, l, u]
      calc
        uSeq A l₀ u₀ (n+1) - lSeq A l₀ u₀ (n+1) = u - mid l u := by simp_all only [mid, Subtype.exists, exists_prop, l, u]
        _ = (u - l) / 2 := by exact sub_mid l u
    · have h_l_succ : lSeq A l₀ u₀ (n+1) = l := by
        simp [lSeq, luNext, step]
        split_ifs with h
        · simp
          rw [hl]
          unfold lSeq
          simp_all only [mid, Subtype.exists, exists_prop, not_true_eq_false, l, u]
        · simp
          rw [hl]
          unfold lSeq
          exact hl
      have h_u_succ : uSeq A l₀ u₀ (n+1) = mid l u := by
        simp [uSeq, luNext, step]
        split_ifs with h
        · simp
          rw [hl, hu]
          unfold lSeq uSeq
          simp_all only [mid, Subtype.exists, exists_prop, not_true_eq_false, l, u]
        · simp
          rw [hu]
          unfold uSeq
          exact rfl
      calc
        uSeq A l₀ u₀ (n + 1) - lSeq A l₀ u₀ (n + 1) = mid l u - l := by simp_all only [mid, Subtype.exists, exists_prop, not_exists, not_and, not_lt, l, u]
        _ = (u - l) / 2 := by exact mid_sub l u

  -- lₙ rostouci posloupnost
  have lInc : IncreasingSequence (lSeq A l₀ u₀) := by
    unfold IncreasingSequence
    intro n
    set l := lSeq A l₀ u₀ n with hl
    set u := uSeq A l₀ u₀ n with hu
    have : lSeq A l₀ u₀ n = (luNext A l₀ u₀ n).1 := rfl
    have : uSeq A l₀ u₀ n = (luNext A l₀ u₀ n).2 := rfl
    by_cases hRight : ∃ a : A, mid l u < a
    · have h_l_succ : lSeq A l₀ u₀ (n+1) = mid l u := by
        simp [lSeq, luNext, step]
        split_ifs with h
        · simp
          rw [hl, hu]
          unfold lSeq uSeq
          ring
        · simp
          rw [hl, hu]
          unfold lSeq uSeq
          simp_all only [mid, Subtype.exists, exists_prop, l, u]
      rw [h_l_succ]
      exact left_le_mid (lₙ_leq_uₙ n)
    · have h_l_succ : lSeq A l₀ u₀ (n+1) = l := by
        simp [lSeq, luNext, step]
        split_ifs with h
        · simp
          rw [hl]
          unfold lSeq
          simp_all only [mid, Subtype.exists, exists_prop, not_true_eq_false, l, u]
        · simp
          rw [hl]
          unfold lSeq
          exact hl
      rw [h_l_succ]

  -- uₙ klesajici posloupnost
  have uDec : DecreasingSequence (uSeq A l₀ u₀) := by
    unfold DecreasingSequence
    intro n
    set l := lSeq A l₀ u₀ n with hl
    set u := uSeq A l₀ u₀ n with hu
    have : lSeq A l₀ u₀ n = (luNext A l₀ u₀ n).1 := rfl
    have : uSeq A l₀ u₀ n = (luNext A l₀ u₀ n).2 := rfl
    by_cases hRight : ∃  a : A, mid l u < a
    · have h_u_succ : uSeq A l₀ u₀ (n+1) = u := by
        simp [uSeq, luNext, step]
        split_ifs with h
        · simp
          exact hu
        · simp
          rw [hu]
          unfold uSeq
          simp_all only [mid, Subtype.exists, exists_prop, l, u]
      rw [h_u_succ]
    · have h_u_succ : uSeq A l₀ u₀ (n+1) = mid l u := by
        simp [uSeq, luNext, step]
        split_ifs with h
        · simp
          rw [hl, hu]
          unfold lSeq uSeq
          simp_all only [mid, Subtype.exists, exists_prop, not_true_eq_false, l, u]
        · simp
          rw [hu]
          unfold uSeq
          exact rfl
      rw [h_u_succ]
      exact mid_le_right (lₙ_leq_uₙ n)

  have abs_le_gap (s t : ℝ) (hs : ∀ n, lSeq A l₀ u₀ n ≤ s ∧ s ≤ uSeq A l₀ u₀ n) (ht : ∀ n, lSeq A l₀ u₀ n ≤ t ∧ t ≤ uSeq A l₀ u₀ n) : ∀ n : ℕ, |s - t| ≤ uSeq A l₀ u₀ n - lSeq A l₀ u₀ n := by
    intro n
    set l := lSeq A l₀ u₀ n with hl
    set u := uSeq A l₀ u₀ n with hu
    have l_leq_s : l ≤ s := (hs n).1
    have s_leq_u : s ≤ u := (hs n).2
    have l_leq_t : l ≤ t := (ht n).1
    have t_leq_u : t ≤ u := (ht n).2
    exact abs_sub_le_of_le_of_le l_leq_s s_leq_u l_leq_t t_leq_u


  have gap_shrink : ∀ n : ℕ, uSeq A l₀ u₀ n - lSeq A l₀ u₀ n = (u₀ - l₀) / 2^n := by
    intro n
    induction' n with d hd
    · simp
      rfl
    · simp_all
      ring

  have gap_to_0  : ∀ ε > 0, ∃ n₀, ∀ n > n₀, |((u₀ - l₀) / 2^n)| < ε := by
    intros ε ε_pos
    have h_pos : u₀ - l₀ ≥ 0 := by linarith
    have h_abs : ∀ n, |(u₀ - l₀) / 2^n| = (u₀ - l₀) / 2^n := by
      intro n
      simp [div_nonneg h_pos]
    by_cases hGap : u₀ - l₀ = 0
    · refine ⟨0, ?_⟩
      intros n n_pos
      rw [hGap]
      simp
      linarith
    · have gap_pos : u₀ - l₀ > 0 := by exact lt_of_le_of_ne h_pos fun a => hGap (id (Eq.symm a))
      have x_pos : (u₀ - l₀) / ε > 0 := by exact div_pos gap_pos ε_pos
      have nat_le_pow_two : ∀ N : ℕ, (N : ℝ) ≤ (2 : ℝ) ^ N := by
        intro N
        induction' N with k ih
        · simp
        · have : (k : ℝ) ≤ (2 : ℝ) ^ k := ih
          have one_le : (1 : ℝ) ≤ (2 : ℝ) ^ k := by
            have : (0 : ℝ) < 2 := by norm_num
            have : (1 : ℝ) ≤ 2 ^ k := by refine one_le_pow₀ ?_; linarith
            exact this
          have : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k + (2 : ℝ) ^ k := add_le_add ih one_le
          -- 2 * (2^k) = (2^k) + (2^k)
          have : (2 : ℝ) ^ k + (2 : ℝ) ^ k = 2 * (2 : ℝ) ^ k := by ring
          calc (↑k.succ : ℝ) = (k : ℝ) + 1 := by simp [Nat.succ_eq_add_one]
            _ ≤ (2 : ℝ) ^ k + (2 : ℝ) ^ k := add_le_add ih one_le
            _ = 2 * (2 : ℝ) ^ k := by ring
            _ = (2 : ℝ) ^ k.succ := by exact Eq.symm (pow_succ' 2 k)
      sorry





  -- prunik do sebe vlozenych intervalu je prave jeden prvek
  have nestedUnique : ∃! s : ℝ, ∀ n, lSeq A l₀ u₀ n ≤ s ∧ s ≤ uSeq A l₀ u₀ n := by

    --refine ⟨?_, ?_, ?_⟩
    sorry


  sorry




end
