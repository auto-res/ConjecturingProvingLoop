

theorem P123_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  exact
    ⟨Topology.P1_of_open (A := A) hA,
      Topology.P2_of_open (A := A) hA,
      Topology.P3_of_open (A := A) hA⟩