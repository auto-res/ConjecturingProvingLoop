

theorem interior_inter_left_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) : interior (A ∩ B) = A ∩ interior B := by
  calc
    interior (A ∩ B) = interior A ∩ interior B := by
      simpa using interior_inter
    _ = A ∩ interior B := by
      simpa [hA.interior_eq]