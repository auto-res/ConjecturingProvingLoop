

theorem Topology.P1_of_boundary_subset_closureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X}
    (h_boundary : (closure (A : Set X) \ interior A) ⊆ closure (interior A)) :
    Topology.P1 (X := X) A := by
  exact
    (Topology.P1_iff_boundary_subset_closureInterior (X := X) (A := A)).2
      h_boundary