

theorem Topology.P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure A = (Set.univ : Set X)) : Topology.P3 A := by
  have hint : interior (closure A) = (Set.univ : Set X) := by
    simpa [hA] using (isOpen_univ.interior_eq)
  simpa [Topology.P3, hint] using (Set.subset_univ (A := A))