

theorem Topology.frontier_subset_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    frontier A ⊆ A := by
  intro x hx
  have hx_closure : x ∈ closure A := hx.1
  simpa [hA.closure_eq] using hx_closure