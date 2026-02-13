

theorem P1_implies_P2_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 (A : Set X) → Topology.P2 A := by
  intro hP1
  have hEquiv := (Topology.P1_iff_P2_of_isOpen (A := A) hA)
  exact hEquiv.1 hP1