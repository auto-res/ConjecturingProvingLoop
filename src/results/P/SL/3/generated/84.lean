

theorem P1_P2_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP1 : Topology.P1 (A : Set X) := P1_of_isOpen (A := A) hA
  have hP2 : Topology.P2 (A : Set X) := P2_of_isOpen (A := A) hA
  have hP3 : Topology.P3 (A : Set X) := P3_of_isOpen (A := A) hA
  exact ⟨hP1, hP2, hP3⟩