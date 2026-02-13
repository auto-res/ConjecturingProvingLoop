

theorem interior_union_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∪ B) = interior A ∪ interior B := by
  have hA_eq : interior A = A := hA.interior_eq
  have hB_eq : interior B = B := hB.interior_eq
  have hUnion_eq : interior (A ∪ B) = A ∪ B := (hA.union hB).interior_eq
  simpa [hA_eq, hB_eq, hUnion_eq]