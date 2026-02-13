

theorem Topology.interior_closure_interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  -- Since `interior A ⊆ A`, applying `closure` preserves the inclusion,
  -- and then `interior_mono` yields the desired result.
  apply interior_mono
  exact closure_mono (interior_subset : interior A ⊆ A)