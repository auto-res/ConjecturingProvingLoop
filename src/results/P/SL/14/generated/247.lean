

theorem Topology.interior_inter_three_eq_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) (hC : IsOpen (C : Set X)) :
    interior (A ∩ B ∩ C : Set X) = A ∩ B ∩ C := by
  have hOpen : IsOpen (A ∩ B ∩ C : Set X) := by
    -- `A ∩ B` is open since both `A` and `B` are open.
    have hAB : IsOpen (A ∩ B : Set X) := IsOpen.inter hA hB
    -- Intersect once more with `C`, which is also open.
    simpa [Set.inter_assoc] using IsOpen.inter hAB hC
  -- The interior of an open set coincides with the set itself.
  simpa using hOpen.interior_eq