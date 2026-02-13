

theorem Topology.P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior A) = (Set.univ : Set X)) : Topology.P2 A := by
  have hInt : interior (closure (interior A)) = (Set.univ : Set X) := by
    simpa [hA] using (isOpen_univ.interior_eq)
  simpa [Topology.P2, hInt] using (Set.subset_univ (A := A))