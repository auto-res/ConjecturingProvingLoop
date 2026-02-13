

theorem Topology.interior_inter_eq_inter_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A ∩ B : Set X) = interior A ∩ interior B := by
  apply subset_antisymm
  · exact
      Topology.interior_inter_subset_inter_interior (X := X) (A := A) (B := B)
  · exact
      Topology.inter_interior_subset_interior_inter (X := X) (A := A) (B := B)