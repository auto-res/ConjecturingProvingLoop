

theorem Topology.interior_iUnionClosure_subset_interiorClosure_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X} :
    interior (⋃ i, closure (𝒜 i)) ⊆ interior (closure (⋃ i, 𝒜 i)) := by
  -- Use the previously proven inclusion between the unions themselves.
  have h_subset :
      (⋃ i, closure (𝒜 i) : Set X) ⊆ closure (⋃ i, 𝒜 i) :=
    Topology.iUnion_closure_subset_closure_iUnion (𝒜 := 𝒜)
  -- Monotonicity of `interior` yields the desired inclusion.
  exact interior_mono h_subset