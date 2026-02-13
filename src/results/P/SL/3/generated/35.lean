

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (A : Set X) = Set.univ) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  intro x _
  simpa [hA, interior_univ] using (Set.mem_univ (x : X))