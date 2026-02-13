

theorem Topology.closure_iUnionInterior_subset_closureInterior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} :
    closure (⋃ i, interior (F i) : Set X) ⊆
      closure (interior (⋃ i, F i)) := by
  -- First show that the union of the interiors is contained in the interior of the union.
  have hSub : (⋃ i, interior (F i) : Set X) ⊆ interior (⋃ i, F i) := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
    -- Monotonicity of `interior` for the inclusion `F i ⊆ ⋃ i, F i`.
    have hIncl : (interior (F i) : Set X) ⊆ interior (⋃ j, F j) := by
      apply interior_mono
      intro y hy
      exact Set.mem_iUnion_of_mem i hy
    exact hIncl hxFi
  -- Taking closures preserves inclusions.
  exact closure_mono hSub