

theorem Topology.disjoint_interior_frontier {X : Type*} [TopologicalSpace X] {A : Set X} :
    Disjoint (interior A) (frontier A) := by
  have h :=
    Topology.interior_inter_frontier_eq_empty (X := X) (A := A)
  simpa [Set.disjoint_iff_inter_eq_empty] using h