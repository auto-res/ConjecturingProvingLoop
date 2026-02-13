

theorem Topology.P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 (A := A) := by
  have hP3 : Topology.P3 (A := A) := Topology.P3_of_isOpen (A := A) hA
  have hIff := Topology.P2_iff_P3_of_open (A := A) hA
  exact hIff.mpr hP3