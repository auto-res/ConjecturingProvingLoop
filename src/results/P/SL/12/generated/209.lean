

theorem Topology.P3_implies_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) (hP3 : Topology.P3 (X := X) A) :
    Topology.P2 (X := X) A := by
  have h_equiv := Topology.P2_iff_P3_of_isOpen (X := X) (A := A) hA
  exact h_equiv.mpr hP3