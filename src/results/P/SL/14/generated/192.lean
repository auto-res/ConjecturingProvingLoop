

theorem Topology.P3_inter_three_of_closed
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B) (hC_closed : IsClosed C)
    (hA_P3 : Topology.P3 A) (hB_P3 : Topology.P3 B) (hC_P3 : Topology.P3 C) :
    Topology.P3 (A ∩ B ∩ C) := by
  -- From `P3` and closedness we deduce that `A`, `B`, and `C` are open.
  have hA_open : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed).1 hA_P3
  have hB_open : IsOpen B :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := B) hB_closed).1 hB_P3
  have hC_open : IsOpen C :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := C) hC_closed).1 hC_P3
  -- The intersection of finitely many open sets is open.
  have hABC_open : IsOpen (A ∩ B ∩ C) := by
    have hAB_open : IsOpen (A ∩ B) := IsOpen.inter hA_open hB_open
    simpa [Set.inter_assoc] using IsOpen.inter hAB_open hC_open
  -- Any open set satisfies `P3`.
  exact Topology.isOpen_implies_P3 (X := X) (A := A ∩ B ∩ C) hABC_open