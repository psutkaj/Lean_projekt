import LEANprj.defs

theorem HeineBorel (M : Set ℝ) : BoundedSet M ∧ ClosedSet M ↔ CompactSet M := by
  constructor
  · intro a
    cases' a with bddM clsM
    sorry
  · intro compactM
    constructor
    ·
      sorry
    ·
      sorry
