

theorem isOpen_imp_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  exact
    And.intro
      (Topology.isOpen_P1 (A := A) hA)
      (And.intro
        (Topology.isOpen_P2 (A := A) hA)
        (Topology.isOpen_P3 (A := A) hA))