

theorem isOpen_P1_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ Topology.P3 A := by
  have h12 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.isOpen_P1_iff_P2 (X := X) (A := A) hA
  have h23 : Topology.P2 A ↔ Topology.P3 A :=
    Topology.isOpen_P2_iff_P3 (X := X) (A := A) hA
  exact h12.trans h23