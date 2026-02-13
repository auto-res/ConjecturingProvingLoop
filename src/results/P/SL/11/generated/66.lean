

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hxA
  have : x ∈ (Set.univ : Set X) := Set.mem_univ x
  simpa [hDense, interior_univ] using this