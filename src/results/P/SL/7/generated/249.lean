

theorem Topology.P3_of_P1_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) :
    Topology.P1 A → Topology.P3 A := by
  intro hP1
  have hEquiv := (Topology.P1_iff_P3_of_isOpen (A := A) hOpen)
  exact hEquiv.1 hP1