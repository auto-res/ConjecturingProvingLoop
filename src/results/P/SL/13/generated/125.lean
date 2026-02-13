

theorem Topology.interior_closure_subset_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    interior (closure (A : Set X)) ⊆ A := by
  -- First, we have the general inclusion into the closure of `A`.
  have h_subset : interior (closure (A : Set X)) ⊆ closure A :=
    Topology.interior_closure_subset_closure (X := X) (A := A)
  -- Since `A` is closed, `closure A = A`.
  simpa [hA_closed.closure_eq] using h_subset