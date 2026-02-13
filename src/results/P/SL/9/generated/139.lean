

theorem Topology.interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure A := by
  intro x hx_int
  -- From `x ∈ interior A`, we know `x ∈ A`.
  have hxA : x ∈ A := interior_subset hx_int
  -- Since `A ⊆ closure A`, we conclude `x ∈ closure A`.
  exact subset_closure hxA