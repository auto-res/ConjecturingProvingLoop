

theorem interior_closure_interior_eq_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    interior (closure (interior A)) = interior A := by
  apply Set.Subset.antisymm
  ·
    have h_subset : closure (interior A) ⊆ A :=
      closure_interior_subset_of_isClosed (X := X) (A := A) hA_closed
    exact interior_mono h_subset
  ·
    exact interior_subset_interiorClosureInterior (X := X) (A := A)