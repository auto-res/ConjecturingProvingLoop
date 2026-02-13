

theorem Topology.boundary_eq_compl_interior_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure A = (Set.univ : Set X)) :
    closure A \ interior A = (interior A)ᶜ := by
  calc
    closure A \ interior A
        = (Set.univ : Set X) \ interior A := by
          simpa [h_dense]
    _ = (interior A)ᶜ := by
          simpa [Set.diff_eq]