

theorem P123_iUnion {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, Topology.P1 (A i) ∧ Topology.P2 (A i) ∧ Topology.P3 (A i)) :
    Topology.P1 (⋃ i, A i) ∧ Topology.P2 (⋃ i, A i) ∧ Topology.P3 (⋃ i, A i) := by
  -- Extract each component property for every `A i`.
  have hP1 : ∀ i, Topology.P1 (A i) := fun i => (hA i).1
  have hP2 : ∀ i, Topology.P2 (A i) := fun i => (hA i).2.1
  have hP3 : ∀ i, Topology.P3 (A i) := fun i => (hA i).2.2
  -- Apply the existing `iUnion` lemmas for each property.
  have hP1Union : Topology.P1 (⋃ i, A i) := Topology.P1_iUnion hP1
  have hP3Union : Topology.P3 (⋃ i, A i) := Topology.P3_iUnion hP3
  have hP2Union : Topology.P2 (⋃ i, A i) := Topology.P2_iUnion hP2
  exact ⟨hP1Union, hP2Union, hP3Union⟩