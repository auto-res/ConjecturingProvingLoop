

theorem iUnion_interiors_subset_interior_iUnion
    {X ι : Type*} [TopologicalSpace X] {F : ι → Set X} :
    (⋃ i, interior (F i : Set X)) ⊆ interior (⋃ i, F i : Set X) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxInt⟩
  have h_mono :
      interior (F i : Set X) ⊆ interior (⋃ j, F j : Set X) :=
    interior_mono (Set.subset_iUnion _ _)
  exact h_mono hxInt