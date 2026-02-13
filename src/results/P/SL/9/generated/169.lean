

theorem Topology.closure_inter_interior_eq_closureInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A ∩ interior A) = closure (interior A) := by
  -- Since `interior A ⊆ A`, the intersection simplifies.
  have h_inter : (A ∩ interior A : Set X) = interior A := by
    have : interior A ⊆ A := interior_subset
    exact Set.inter_eq_right.mpr this
  simpa [h_inter]