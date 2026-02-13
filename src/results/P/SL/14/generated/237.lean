

theorem Topology.interior_union_three_eq_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) :
    interior (A ∪ B ∪ C : Set X) = A ∪ B ∪ C := by
  -- The union of three open sets is open.
  have hOpen : IsOpen (A ∪ B ∪ C : Set X) := by
    have hAB : IsOpen (A ∪ B : Set X) := IsOpen.union hA hB
    exact IsOpen.union hAB hC
  -- The interior of an open set is the set itself.
  simpa using hOpen.interior_eq