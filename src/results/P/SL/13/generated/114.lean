

theorem Topology.closureInterior_subset_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) ⊆ A := by
  -- Start from the basic inclusion `interior A ⊆ A`.
  have h_subset : interior (A : Set X) ⊆ A := interior_subset
  -- Taking closures on both sides preserves the inclusion.
  have h_closure : closure (interior (A : Set X)) ⊆ closure A :=
    closure_mono h_subset
  -- Use the closedness of `A` to rewrite `closure A` as `A`.
  simpa [hA_closed.closure_eq] using h_closure