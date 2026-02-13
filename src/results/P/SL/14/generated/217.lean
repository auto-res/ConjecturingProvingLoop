

theorem Topology.isOpen_inter_three_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) :
    Topology.P1 (A ∩ B ∩ C) ∧ Topology.P2 (A ∩ B ∩ C) ∧ Topology.P3 (A ∩ B ∩ C) := by
  -- The intersection of three open sets is open.
  have hOpen : IsOpen (A ∩ B ∩ C) := by
    have hAB : IsOpen (A ∩ B) := IsOpen.inter hA hB
    have hABC : IsOpen ((A ∩ B) ∩ C) := IsOpen.inter hAB hC
    simpa [Set.inter_assoc] using hABC
  -- Any open set satisfies `P1`, `P2`, and `P3`.
  exact
    Topology.isOpen_satisfies_P1_P2_P3
      (X := X) (A := A ∩ B ∩ C) hOpen