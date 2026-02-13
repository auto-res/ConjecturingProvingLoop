

theorem closure_iUnion_subset {ι : Sort _} {X : Type _} [TopologicalSpace X]
    (A : ι → Set X) :
    (⋃ i, closure (A i : Set X)) ⊆ closure (⋃ i, A i : Set X) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hIncl : closure (A i : Set X) ⊆ closure (⋃ j, A j : Set X) := by
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  exact hIncl hxAi