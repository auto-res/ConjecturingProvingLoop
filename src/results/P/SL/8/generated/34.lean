

theorem closed_P3_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    interior A = A := by
  -- `closure A = A` since `A` is closed
  have h_cl : closure A = A := hA_closed.closure_eq
  -- From `P3`, we have `A ⊆ interior (closure A)`; rewrite using `h_cl`
  have h₁ : A ⊆ interior A := by
    dsimp [Topology.P3] at hP3
    simpa [h_cl] using hP3
  -- Always, `interior A ⊆ A`
  have h₂ : interior A ⊆ A := interior_subset
  -- Combine the two inclusions to get equality
  exact Set.Subset.antisymm h₂ h₁