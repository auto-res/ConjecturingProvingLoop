

theorem Topology.P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure A = (Set.univ : Set X)) : Topology.P3 (X := X) A := by
  dsimp [Topology.P3]
  intro x hxA
  simp [h_dense]