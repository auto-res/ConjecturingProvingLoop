

theorem interior_iUnion_eq_iUnion_of_open {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {S : ι → Set X} (hS : ∀ i, IsOpen (S i)) :
    interior (⋃ i, S i : Set X) = ⋃ i, S i := by
  have hOpen : IsOpen (⋃ i, S i : Set X) := by
    simpa using isOpen_iUnion (fun i => hS i)
  simpa [hOpen.interior_eq]