

theorem Topology.dense_iff_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense A ↔ closure A = (Set.univ : Set X) := by
  constructor
  · intro hDense
    exact hDense.closure_eq
  · intro hEq
    have hDense : Dense A := by
      intro x
      have : (x : X) ∈ (Set.univ : Set X) := by
        simp
      simpa [hEq] using this
    exact hDense