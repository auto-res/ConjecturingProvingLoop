

theorem P1_iff_P2_and_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  -- Equivalences already established for open sets.
  have h12 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_open (A := A) hA
  have h13 : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_open (A := A) hA
  constructor
  · intro hP1
    exact ⟨(h12.mp hP1), (h13.mp hP1)⟩
  · rintro ⟨hP2, _hP3⟩
    exact (h12.mpr hP2)