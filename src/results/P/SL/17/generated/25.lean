

theorem Topology.P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : Dense (interior A)) : Topology.P1 A := by
  unfold Topology.P1
  intro x hxA
  have h_closure : closure (interior A) = (Set.univ : Set X) := h_dense.closure_eq
  have h_univ : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h_closure] using h_univ