

theorem Topology.closureInterior_iUnion_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} :
    (⋃ i, closure (interior (F i))) ⊆ closure (interior (⋃ i, F i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `interior (F i)` is contained in `⋃ i, F i`,
  -- hence its closure is contained in the closure of the interior of that union.
  have hSub :
      closure (interior (F i)) ⊆ closure (interior (⋃ j, F j)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion_of_mem i hy
  exact hSub hx_i