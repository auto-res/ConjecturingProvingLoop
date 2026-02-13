

theorem P1_iff_P2_and_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  have h12 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h23 : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isOpen (A := A) hA
  constructor
  · intro hP1
    have hP2 : Topology.P2 A := (h12.mp hP1)
    have hP3 : Topology.P3 A := (h23.mp hP2)
    exact And.intro hP2 hP3
  · rintro ⟨hP2, _⟩
    exact (h12.mpr hP2)