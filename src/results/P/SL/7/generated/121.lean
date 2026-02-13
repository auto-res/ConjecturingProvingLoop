

theorem Topology.P3_of_dense_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure (A : Set X)) = (Set.univ : Set X)) : Topology.P3 A := by
  simpa [Topology.P3, h] using (Set.subset_univ (A := A))