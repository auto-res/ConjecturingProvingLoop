

theorem Topology.P3_implies_P1_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P3 (A := A) → Topology.P1 (A := A) := by
  intro hP3
  have hEquiv := Topology.P1_iff_P3_of_open (A := A) hA
  exact (hEquiv.mpr hP3)