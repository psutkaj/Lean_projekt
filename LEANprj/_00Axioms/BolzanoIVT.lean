import LEANprj.defs

axiom BolzanoIVT
  (f : ℝ → ℝ) (a b y₀ : ℝ)
  (h_ab : a ≤ b) (Int : Set ℝ) (hInt : Int = Set.Icc a b)
  (h_cont : FunctionContinuousOnSet Int f)
  (h_val : f a < y₀ ∧ y₀ < f b) :
  ∃ c ∈ Int, f c = y₀
