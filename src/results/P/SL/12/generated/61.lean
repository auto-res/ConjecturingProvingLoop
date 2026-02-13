

theorem Topology.P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior A : Set X) = Set.univ) :
    Topology.P2 (X := X) A := by
  dsimp [Topology.P2]
  intro x hx
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [hA, interior_univ] using this