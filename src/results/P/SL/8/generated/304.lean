

theorem interior_inter_eq_of_isOpen {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∩ B) = A ∩ B := by
  have h_open : IsOpen (A ∩ B) := IsOpen.inter hA hB
  simpa using h_open.interior_eq