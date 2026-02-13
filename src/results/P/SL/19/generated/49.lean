

theorem Topology.P1_iff_P2_and_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 (A := A) ↔ (Topology.P2 (A := A) ∧ Topology.P3 (A := A)) := by
  constructor
  · intro hP1
    have hP2 : Topology.P2 (A := A) :=
      (Topology.P1_iff_P2_of_open (A := A) hA).1 hP1
    have hP3 : Topology.P3 (A := A) :=
      (Topology.P1_iff_P3_of_open (A := A) hA).1 hP1
    exact And.intro hP2 hP3
  · rintro ⟨hP2, _⟩
    exact Topology.P2_implies_P1 (A := A) hP2