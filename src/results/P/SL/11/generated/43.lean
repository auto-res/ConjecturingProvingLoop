

theorem P2_iUnion {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, Topology.P2 (A i)) :
    Topology.P2 (⋃ i, A i) := by
  -- Obtain `P1` and `P3` for each `A i`.
  have hP1 : ∀ i, Topology.P1 (A i) := fun i => Topology.P2_implies_P1 (hA i)
  have hP3 : ∀ i, Topology.P3 (A i) := fun i => Topology.P2_implies_P3 (hA i)
  -- Deduce `P1` and `P3` for the union.
  have hP1Union : Topology.P1 (⋃ i, A i) := Topology.P1_iUnion hP1
  have hP3Union : Topology.P3 (⋃ i, A i) := Topology.P3_iUnion hP3
  -- Conclude `P2` for the union.
  exact Topology.P2_of_P1_and_P3 (A := ⋃ i, A i) ⟨hP1Union, hP3Union⟩