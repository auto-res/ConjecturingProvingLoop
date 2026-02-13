

theorem iUnion_interior_closure_subset_interior_closure_iUnion
    {X ι : Type*} [TopologicalSpace X] {F : ι → Set X} :
    (⋃ i, interior (closure (F i : Set X))) ⊆
      interior (closure (⋃ i, F i : Set X)) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxFi⟩
  have h_closure :
      closure (F i : Set X) ⊆ closure (⋃ j, F j : Set X) := by
    have h_subset : (F i : Set X) ⊆ ⋃ j, F j :=
      Set.subset_iUnion _ _
    exact closure_mono h_subset
  have h_mono :
      interior (closure (F i : Set X)) ⊆
        interior (closure (⋃ j, F j : Set X)) :=
    interior_mono h_closure
  exact h_mono hxFi