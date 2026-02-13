

theorem interior_iUnion_of_open {ι : Sort _} {X : Type _} [TopologicalSpace X]
    (A : ι → Set X) (hOpen : ∀ i, IsOpen (A i)) :
    interior (⋃ i, A i : Set X) = ⋃ i, A i := by
  -- The union of open sets is open.
  have hUnionOpen : IsOpen (⋃ i, A i : Set X) := isOpen_iUnion hOpen
  -- For an open set, its interior coincides with itself.
  simpa using hUnionOpen.interior_eq