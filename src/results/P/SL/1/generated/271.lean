

theorem Topology.closure_iUnion_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (⋃ i, closure (A i) : Set X) ⊆ closure (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hsubset : closure (A i) ⊆ closure (⋃ j, A j) := by
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  exact hsubset hxAi