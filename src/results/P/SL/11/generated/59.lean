

theorem P1_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ↔ Topology.P3 A := by
  have hP1 : Topology.P1 A := Topology.P1_of_open (A := A) hA
  have hP3 : Topology.P3 A := Topology.P3_of_open (A := A) hA
  exact ⟨fun _ => hP3, fun _ => hP1⟩