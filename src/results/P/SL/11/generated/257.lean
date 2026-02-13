

theorem P123_iUnion_open {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, IsOpen (A i)) :
    Topology.P1 (⋃ i, A i) ∧ Topology.P2 (⋃ i, A i) ∧ Topology.P3 (⋃ i, A i) := by
  exact
    ⟨Topology.P1_iUnion_open hA,
      Topology.P2_iUnion_open hA,
      Topology.P3_iUnion_open hA⟩