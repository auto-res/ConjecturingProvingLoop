

theorem interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∪ B : Set X) = A ∪ B := by
  -- The union of two open sets is open.
  have hOpen : IsOpen (A ∪ B : Set X) := hA.union hB
  -- For an open set, its interior coincides with itself.
  simpa using hOpen.interior_eq