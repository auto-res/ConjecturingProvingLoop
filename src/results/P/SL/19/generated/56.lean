

theorem Topology.isOpen_is_P1_and_P2_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P1 (A := A) ∧ Topology.P2 (A := A) ∧ Topology.P3 (A := A) := by
  have hP1 : Topology.P1 (A := A) := Topology.P1_of_isOpen (A := A) hA
  have hP2 : Topology.P2 (A := A) := Topology.P2_of_isOpen (A := A) hA
  have hP3 : Topology.P3 (A := A) := Topology.P3_of_isOpen (A := A) hA
  exact And.intro hP1 (And.intro hP2 hP3)