

theorem Topology.closure_iUnion_interior_subset_closure_iUnion
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    closure (⋃ i, interior (A i) : Set X) ⊆
      closure (⋃ i, A i) := by
  -- The union of the interiors is contained in the union of the sets themselves.
  have h_subset :
      (⋃ i, interior (A i) : Set X) ⊆ ⋃ i, A i := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hx_int⟩
    have hxAi : x ∈ A i :=
      (interior_subset : interior (A i) ⊆ A i) hx_int
    exact Set.mem_iUnion.2 ⟨i, hxAi⟩
  -- Taking closures preserves inclusions.
  exact closure_mono h_subset