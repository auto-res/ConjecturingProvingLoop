

theorem Topology.P2_of_dense_interiorClosureInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : interior (closure (interior A)) = (Set.univ : Set X)) :
    Topology.P2 A := by
  simpa [Topology.P2, hA] using (Set.subset_univ (A := A))