

theorem Topology.P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P2 (X := X) A := by
  dsimp [Topology.P2]
  intro x hxA
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [h_dense, interior_univ] using hx_univ