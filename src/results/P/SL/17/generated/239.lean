

theorem Topology.dense_interior_iff_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) ↔ closure (interior A) = (Set.univ : Set X) := by
  constructor
  · intro hDense
    simpa using hDense.closure_eq
  · intro hEq
    -- Build the `Dense` property from the closure equality.
    have hDense : Dense (interior A) := by
      intro x
      have : (x : X) ∈ (Set.univ : Set X) := by
        simp
      simpa [hEq] using this
    exact hDense