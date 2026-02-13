

theorem interior_inter_closure_eq_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∩ closure A = interior A := by
  have h : interior (A : Set X) ⊆ closure A :=
    interior_subset.trans subset_closure
  simpa [Set.inter_eq_left.mpr h]