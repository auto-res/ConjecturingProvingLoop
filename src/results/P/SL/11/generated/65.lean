

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure A = (Set.univ : Set X)) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  simpa [hDense, interior_univ] using (Set.mem_univ x)