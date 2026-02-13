

theorem Topology.P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior A) = (Set.univ : Set X)) : Topology.P1 A := by
  simpa [Topology.P1, hA] using (Set.subset_univ (A := A))