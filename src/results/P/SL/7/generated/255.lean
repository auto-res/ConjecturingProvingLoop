

theorem Topology.iUnion_interior_subset_interior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} :
    (⋃ i, interior (F i)) ⊆ interior (⋃ i, F i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hSub : interior (F i) ⊆ interior (⋃ j, F j) := by
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion_of_mem i hy
  exact hSub hxFi