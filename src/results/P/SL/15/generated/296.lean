

theorem interior_inter_has_all_P {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (interior A ∩ interior B) ∧
      Topology.P2 (interior A ∩ interior B) ∧
        Topology.P3 (interior A ∩ interior B) := by
  have hA : IsOpen (interior A) := isOpen_interior
  have hB : IsOpen (interior B) := isOpen_interior
  simpa using
    (Topology.isOpen_inter_has_all_P
      (X := X) (A := interior A) (B := interior B) hA hB)