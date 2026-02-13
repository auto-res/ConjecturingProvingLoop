

theorem interior_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) (hC : IsOpen (C : Set X)) :
    interior (A ∪ B ∪ C : Set X) = A ∪ B ∪ C := by
  -- The union of three open sets is open.
  have hOpen : IsOpen (A ∪ B ∪ C : Set X) := by
    have hAB : IsOpen (A ∪ B : Set X) := hA.union hB
    exact hAB.union hC
  -- The interior of an open set is the set itself.
  simpa using hOpen.interior_eq