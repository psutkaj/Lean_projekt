import LEANprj.Sequences.definitions
noncomputable section
open Classical

variable (A : Set ℝ) (l₀ u₀ : ℝ)

-- chci si vytvorit pulleni intervalu, a aby ho rozeznavalo simp
@[simp] def mid (l u : ℝ) : ℝ := (l + u) / 2

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
  have intNonempty : ∀ n : ℕ, ∃ a ∈ A, lSeq A l₀ u₀ n ≤ a ∧ a ≤ uSeq A l₀ u₀ n := by
    intro n
    induction' n with d hd
    · use l₀
      constructor
      · exact hl₀
      · simp [lSeq, uSeq, luNext]
        exact hu₀ l₀ hl₀
    · obtain ⟨a, ha₁, ha₂⟩ := hd
      unfold lSeq uSeq luNext step
      simp only [Subtype.exists, exists_prop, dite_eq_ite]
      split_ifs with h
      · obtain ⟨w, hw⟩ := h
        use w
        constructor
        · exact hw.1
        · constructor
          · have mid_le := mid_le_right (lₙ_leq_uₙ d)
            have h_upper := upperBound d w hw.1
            unfold uSeq luNext at h_upper
            linarith
          · have := upperBound d w hw.1
            dsimp
            simp
            simp_all only [mid, and_true]
            obtain ⟨left, right⟩ := hw
            unfold luNext
            split
            · simp
              exact hu₀ w left
            · simp_all only [Nat.succ_eq_add_one]
              sorry
      · use a
        sorry

  sorry










theorem exists_unique_infimum (A : Set ℝ) : ∃! i : ℝ, IsInf A i := by
  sorry

end
