

theorem interior_iUnion_eq_iUnion_of_isOpen {X : Type*} [TopologicalSpace X]
    {ι : Sort _} (f : ι → Set X) (h : ∀ i, IsOpen (f i)) :
    interior (⋃ i, f i : Set X) = ⋃ i, f i := by
  have hOpen : IsOpen (⋃ i, f i : Set X) := isOpen_iUnion (λ i => h i)
  simpa [hOpen.interior_eq] using hOpen.interior_eq