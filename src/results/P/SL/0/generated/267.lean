

theorem interior_union_three_eq_self_of_open
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X))
    (hC : IsOpen (C : Set X)) :
    interior (A ∪ B ∪ C : Set X) = (A ∪ B ∪ C : Set X) := by
  -- The triple union of open sets is open.
  have hOpen : IsOpen ((A ∪ B ∪ C) : Set X) := (hA.union hB).union hC
  simpa using hOpen.interior_eq