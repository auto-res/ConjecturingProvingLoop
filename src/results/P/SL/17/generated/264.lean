

theorem Topology.frontier_subset_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : frontier A ⊆ A := by
  intro x hx
  have hx_cl : x ∈ closure A := hx.1
  simpa [hA_closed.closure_eq] using hx_cl