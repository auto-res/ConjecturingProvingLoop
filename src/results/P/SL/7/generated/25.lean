

theorem Topology.P1_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ↔ Topology.P3 A := by
  have h := Topology.IsOpen_P1_and_P3 (A := A) hA
  exact ⟨fun _ => h.2, fun _ => h.1⟩