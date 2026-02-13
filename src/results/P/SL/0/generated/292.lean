

theorem interior_iUnion_eq_iUnion_of_open {X ι : Type*} [TopologicalSpace X]
    {F : ι → Set X} (hF : ∀ i, IsOpen (F i : Set X)) :
    interior (⋃ i, F i : Set X) = (⋃ i, F i : Set X) := by
  have hOpen : IsOpen (⋃ i, F i : Set X) := isOpen_iUnion (by
    intro i; exact hF i)
  simpa [hOpen.interior_eq]