

theorem Topology.P1_iff_P3_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ Topology.P3 A := by
  have h1 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h2 : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isOpen (A := A) hA
  exact h1.trans h2