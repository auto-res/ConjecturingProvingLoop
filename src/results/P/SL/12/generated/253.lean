

theorem Topology.interior_union_three_eq_self_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) (hC : IsOpen (C : Set X)) :
    interior (A ∪ B ∪ C : Set X) = A ∪ B ∪ C := by
  -- The union of three open sets is open.
  have h_open : IsOpen (A ∪ B ∪ C : Set X) := (hA.union hB).union hC
  -- For an open set `U`, `interior U = U`.
  simpa using h_open.interior_eq