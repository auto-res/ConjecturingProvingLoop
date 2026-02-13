

theorem interior_iUnion_subset
    {ι : Sort _} {X : Type _} [TopologicalSpace X] (A : ι → Set X) :
    (⋃ i, interior (A i : Set X)) ⊆ interior (⋃ i, A i : Set X) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hIncl :
      interior (A i : Set X) ⊆ interior (⋃ j, A j : Set X) := by
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  exact hIncl hx_i