import LEANprj.defs

axiom HeineBorel
  (M : Set ℝ) :
  BoundedSet M ∧ ClosedSet M
  ↔ CompactSet M
