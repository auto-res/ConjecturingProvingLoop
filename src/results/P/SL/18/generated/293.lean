

theorem interior_union_eq_union_interiors_of_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∪ B : Set X) = interior A ∪ interior B := by
  have hUnionOpen : IsOpen (A ∪ B : Set X) := hA.union hB
  have hIntUnion : interior (A ∪ B : Set X) = A ∪ B := hUnionOpen.interior_eq
  have hIntA : interior A = A := hA.interior_eq
  have hIntB : interior B = B := hB.interior_eq
  simpa [hIntUnion, hIntA, hIntB]