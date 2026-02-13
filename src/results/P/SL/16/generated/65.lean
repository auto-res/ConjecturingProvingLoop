

theorem Topology.isOpen_satisfies_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) :
    Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A := by
  exact
    ⟨Topology.isOpen_implies_P1 (X := X) (A := A) hOpen,
      Topology.isOpen_implies_P2 (X := X) (A := A) hOpen,
      Topology.isOpen_implies_P3 (X := X) (A := A) hOpen⟩