

theorem Topology.interiorClosure_iUnion_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort _} {F : ι → Set X} :
    (⋃ i, interior (closure (F i))) ⊆ interior (closure (⋃ i, F i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hSub : interior (closure (F i)) ⊆ interior (closure (⋃ j, F j)) := by
    apply interior_mono
    have : (closure (F i) : Set X) ⊆ closure (⋃ j, F j) := by
      apply closure_mono
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact this
  exact hSub hxFi