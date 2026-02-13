

theorem interior_inter_of_isOpen {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∩ B) = A ∩ B := by
  -- Start from the general description of the interior of an intersection.
  have h : interior (A ∩ B) = interior A ∩ interior B := by
    simpa using interior_inter (A := A) (B := B)
  -- Use the fact that the interior of an open set is the set itself.
  simpa [hA.interior_eq, hB.interior_eq] using h