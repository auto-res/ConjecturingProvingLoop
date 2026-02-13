

theorem Topology.interiorClosureInterior_eq_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    interior (closure (interior A)) = interior A := by
  apply Set.Subset.antisymm
  ·
    have h_closure_subset : closure (interior A) ⊆ A :=
      closure_minimal (interior_subset : interior A ⊆ A) hA_closed
    exact interior_mono h_closure_subset
  ·
    have h_subset : (interior A : Set X) ⊆ closure (interior A) := subset_closure
    exact interior_maximal h_subset isOpen_interior