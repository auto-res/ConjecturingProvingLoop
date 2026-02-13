

theorem Topology.P3_of_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure A = (Set.univ : Set X)) : Topology.P3 A := by
  have hInt : interior (closure A) = (Set.univ : Set X) := by
    simpa [h] using
      (interior_univ : interior (Set.univ : Set X) = Set.univ)
  exact Topology.P3_of_interior_closure_eq_univ (A := A) hInt