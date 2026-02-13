

theorem closure_interior_iUnion_subset
    {ι : Sort _} {X : Type _} [TopologicalSpace X] (A : ι → Set X) :
    (⋃ i, closure (interior (A i : Set X))) ⊆
      closure (interior (⋃ i, A i : Set X)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hIncl :
      closure (interior (A i : Set X)) ⊆
        closure (interior (⋃ j, A j : Set X)) := by
    apply closure_mono
    have hInt :
        interior (A i : Set X) ⊆ interior (⋃ j, A j : Set X) := by
      apply interior_mono
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact hInt
  exact hIncl hx_i