

theorem iUnion_closure_subset_closure_iUnion {X ι : Type*} [TopologicalSpace X]
    {A : ι → Set X} :
    (⋃ i, closure (A i)) ⊆ closure (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hsubset : closure (A i) ⊆ closure (⋃ j, A j) :=
    closure_mono (Set.subset_iUnion _ _)
  exact hsubset hx_i