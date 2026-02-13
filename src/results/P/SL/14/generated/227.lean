

theorem Topology.isOpen_union_three_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) :
    Topology.P1 (A ∪ B ∪ C) ∧ Topology.P2 (A ∪ B ∪ C) ∧ Topology.P3 (A ∪ B ∪ C) := by
  -- Establish that the union `A ∪ B ∪ C` is open.
  have hOpen : IsOpen (A ∪ B ∪ C) := by
    have hAB : IsOpen (A ∪ B) := IsOpen.union hA hB
    exact IsOpen.union hAB hC
  -- Invoke the generic result for open sets.
  simpa using
    Topology.isOpen_satisfies_P1_P2_P3 (X := X) (A := A ∪ B ∪ C) hOpen