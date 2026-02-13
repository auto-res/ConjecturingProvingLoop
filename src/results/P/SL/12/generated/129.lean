

theorem Topology.iUnion_interior_subset_interior_iUnion {X ι : Type*}
    [TopologicalSpace X] (A : ι → Set X) :
    (⋃ i, interior (A i) : Set X) ⊆ interior (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  -- Use monotonicity of `interior` with the inclusion `A i ⊆ ⋃ j, A j`.
  have h_sub : (interior (A i) : Set X) ⊆ interior (⋃ j, A j) := by
    have : (A i : Set X) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact interior_mono this
  exact h_sub hxAi