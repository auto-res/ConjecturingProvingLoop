

theorem Topology.P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 (X := X) A := by
  dsimp [Topology.P1]
  intro x hxA
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [h_dense] using hx_univ