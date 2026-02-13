

theorem isOpen_has_all_P {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  exact
    ⟨Topology.isOpen_implies_P1 (X := X) (A := A) hA,
     Topology.isOpen_implies_P2 (X := X) (A := A) hA,
     Topology.isOpen_implies_P3 (X := X) (A := A) hA⟩