import LEANprj.defs
import LEANprj._01Sets.Theorems.AxSupOfAxNIP
import LEANprj._05Continuity.Theorems.ContinuityKeepsSgn

theorem BolzanoZeroValue
  (f : ℝ → ℝ) (a b : ℝ) (h_ab : a ≤ b)
  (h_cont : ∀ x ∈ Set.Icc a b, FunctionContinuousAt f x)
  (h_fa : f a < 0) (h_fb : f b > 0) :
  AxNIP →
  ∃ c ∈ Set.Icc a b, f c = 0 := by
  intro ax_NIP
  let M := {x | a ≤ x ∧ x ≤ b ∧ f x < 0}
  have ha_in_M : a ∈ M := by simp [M, h_ab, h_fa]
  have M_nonempty : M.Nonempty := by use a
  have M_bdd : ∃ u, ∀ x ∈ M, x ≤ u := by
    use b
    intro x xM
    exact xM.2.1
  obtain ⟨c, hc_sup, _⟩ := axSup_of_axNip ax_NIP M M_nonempty M_bdd
  unfold IsSup at hc_sup
  have h_UB : ∀ x ∈ M, x ≤ c := λ x hx ↦ (hc_sup).1 x hx
  have h_Approx : ∀ ε > 0, ∃ x ∈ M, c - ε < x := (hc_sup).2
  have c_in_Icc : c ∈ Set.Icc a b := by
    constructor
    · exact (hc_sup).1 a ha_in_M
    · by_contra hne
      push_neg at hne
      let ε := c - b
      obtain ⟨x, hx_M, hx_close⟩ := h_Approx ε (by linarith)
      have : x > b := by linarith
      have : x ≤ b := by exact hx_M.2.1
      linarith
  use c, c_in_Icc
  by_cases h_fc_neg : f c < 0
  · have h_cont_c := h_cont c c_in_Icc
    obtain ⟨δ, δ_pos, h_neg_neigh⟩ := ContinuityKeepsSgnNeg h_cont_c h_fc_neg
    have h_c_lt_b : c < b := by
      by_contra h_eq
      have : c = b := le_antisymm c_in_Icc.2 (not_lt.mp h_eq)
      rw [this] at h_fc_neg
      linarith
    let step := min (δ/2) (b - c)
    let x := c + step
    have step_pos : step > 0 := by exact lt_min (half_pos δ_pos) (sub_pos.mpr h_c_lt_b)
    have hx_in_M : x ∈ M := by
      constructor
      · linarith [c_in_Icc.1]
      · constructor
        · dsimp [x, step]
          linarith [min_le_right (δ/2) (b-c)]
        · apply h_neg_neigh
          dsimp [x, step]
          simp
          rw [abs_of_pos]
          linarith [min_le_left (δ/2) (b-c)]
          linarith
    have : x ≤ c := h_UB x hx_in_M
    linarith
  · by_cases h_fc_pos : f c > 0
    · have h_cont_c := h_cont c c_in_Icc
      obtain ⟨δ, hδ_pos, h_pos_neigh⟩ := ContinuityKeepsSgnPos h_cont_c h_fc_pos
      let y := c - δ/2
      have h_y_UB : ∀ z ∈ M, z ≤ y := by
        intro z zM
        by_contra hz_gt_y
        push_neg at hz_gt_y
        have h_dist : |z - c| < δ := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (h_UB z zM))]
          calc c - z
            _ < c - y := by linarith
            _ = δ/2 := by ring
          linarith
        have : f z > 0 := h_pos_neigh z h_dist
        linarith [zM.2.2]
      obtain ⟨x, xM, hx_gt_y⟩ := h_Approx (δ/2) (half_pos hδ_pos)
      have : x ≤ y := h_y_UB x xM
      dsimp [y] at this
      linarith
    · linarith
