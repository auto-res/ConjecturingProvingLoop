

theorem interior_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior ((A ∩ B) : Set X) ⊆ interior A ∩ interior B := by
  intro x hx
  -- First, show `x ∈ interior A`.
  have hA : x ∈ interior A := by
    -- Since `A ∩ B ⊆ A`, monotonicity of `interior` gives the inclusion.
    have hSub : (A ∩ B : Set X) ⊆ A := by
      intro y hy
      exact hy.1
    exact (interior_mono hSub) hx
  -- Next, show `x ∈ interior B`.
  have hB : x ∈ interior B := by
    -- Similarly, `A ∩ B ⊆ B`.
    have hSub : (A ∩ B : Set X) ⊆ B := by
      intro y hy
      exact hy.2
    exact (interior_mono hSub) hx
  -- Combine the two inclusions.
  exact And.intro hA hB