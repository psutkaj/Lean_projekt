import LEANprj.defs
import LEANprj._02Sequences.Theorems.BolzanoWeierstrass

theorem HeineBorel (M : Set ℝ) : BoundedSet M ∧ ClosedSet M ↔ CompactSet M := by
  unfold BoundedSet ClosedSet CompactSet
  constructor
  · intro a
    cases' a with bddM clsM
    intro a ha
    obtain ⟨c, c_pos, c_bound⟩ := bddM
    have ha_bdd : BoundedSequence a := by
      unfold BoundedSequence
      use c
      refine ⟨c_pos, ?_⟩
      intro n
      have : a n ∈ M := ha n
      exact c_bound (a n) (ha n)
    obtain ⟨k, ⟨hk_inc, ⟨L, hL⟩⟩⟩ := BolzanoWeierstrass a ha_bdd
    have LinM : L ∈ M := by
      apply clsM (Subsequence a k) L
      · intro n
        exact ha (k n)
      · exact hL
    exact ⟨k, hk_inc, L, hL, LinM⟩
  · intro compactM
    constructor
    ·
      sorry
    ·
      sorry
