

theorem Topology.closure_iUnion_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort _} {F : ι → Set X} :
    (⋃ i, closure (F i) : Set X) ⊆ closure (⋃ i, F i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hIncl : closure (F i) ⊆ closure (⋃ j, F j) := by
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion_of_mem i hy
  exact hIncl hxFi