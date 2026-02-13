

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hxA
  have : x ∈ (Set.univ : Set X) := Set.mem_univ x
  simpa [hDense] using this