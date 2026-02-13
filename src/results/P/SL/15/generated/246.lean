

theorem interior_inter_right_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsOpen B) : interior (A ∩ B) = interior A ∩ B := by
  calc
    interior (A ∩ B) = interior A ∩ interior B := by
      simpa using interior_inter (A := A) (B := B)
    _ = interior A ∩ B := by
      simpa [hB.interior_eq]