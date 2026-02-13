

theorem closure_iUnion_closure_eq {X ι : Type*} [TopologicalSpace X] {A : ι → Set X} :
    closure (⋃ i, closure (A i)) = closure (⋃ i, A i) := by
  apply subset_antisymm
  ·
    -- `closure (⋃ i, closure (A i)) ⊆ closure (⋃ i, A i)`
    have hSub : (⋃ i, closure (A i)) ⊆ closure (⋃ i, A i) := by
      intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
      have hCl : closure (A i) ⊆ closure (⋃ j, A j) :=
        closure_mono (Set.subset_iUnion _ _)
      exact hCl hx_i
    have : closure (⋃ i, closure (A i)) ⊆ closure (closure (⋃ i, A i)) :=
      closure_mono hSub
    simpa [closure_closure] using this
  ·
    -- `closure (⋃ i, A i) ⊆ closure (⋃ i, closure (A i))`
    have hSub : (⋃ i, A i) ⊆ ⋃ i, closure (A i) := by
      intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
      exact Set.mem_iUnion.2 ⟨i, subset_closure hx_i⟩
    exact closure_mono hSub