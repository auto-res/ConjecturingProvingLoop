

theorem Topology.closure_inter_interior_eq_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure A ∩ interior A = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    have hx_closure : x ∈ closure A := by
      have : x ∈ A := interior_subset hx
      exact Set.subset_closure this
    exact ⟨hx_closure, hx⟩