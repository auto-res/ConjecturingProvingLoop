

theorem Topology.P1_P2_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 (A := A) ∧ Topology.P2 (A := A) ∧ Topology.P3 (A := A) := by
  exact
    ⟨Topology.P1_of_isOpen (A := A) hA,
     Topology.P2_of_isOpen (A := A) hA,
     Topology.P3_of_isOpen (A := A) hA⟩