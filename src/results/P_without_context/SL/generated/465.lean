

theorem P2_implies_P3 {A : Set X} : P2 A → P3 A := by
  intro hP2
  -- First, establish the monotonicity inclusion
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hcl : closure (interior A) ⊆ closure A := by
      have hint : interior A ⊆ A := interior_subset
      exact closure_mono hint
    exact interior_mono hcl
  -- Combine the inclusions to obtain the desired result
  have hfin : A ⊆ interior (closure A) := by
    intro x hx
    have : x ∈ interior (closure (interior A)) := hP2 hx
    exact hsubset this
  simpa [P3] using hfin