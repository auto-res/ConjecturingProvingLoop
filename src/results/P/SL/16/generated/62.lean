

theorem Topology.interior_closure_eq_univ_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure A = (Set.univ : Set X)) :
    interior (closure A) = (Set.univ : Set X) := by
  calc
    interior (closure A) = interior (Set.univ : Set X) := by
      simpa [h_dense]
    _ = (Set.univ : Set X) := by
      simpa [interior_univ]