

theorem Topology.P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : Dense (interior A)) : Topology.P2 A := by
  unfold Topology.P2
  intro x hxA
  have hclosure : closure (interior A) = (Set.univ : Set X) := h_dense.closure_eq
  have hint : interior (closure (interior A)) = (Set.univ : Set X) := by
    simpa [hclosure] using interior_univ
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hint] using this