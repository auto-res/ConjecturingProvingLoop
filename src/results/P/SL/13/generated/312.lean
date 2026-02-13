

theorem Topology.boundary_subset_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    closure (A : Set X) \ interior A ⊆ (A : Set X) := by
  intro x hx
  have hx_cl : (x : X) ∈ closure (A : Set X) := hx.1
  simpa [hA_closed.closure_eq] using hx_cl