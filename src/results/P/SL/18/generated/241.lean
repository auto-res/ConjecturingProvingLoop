

theorem P123_iUnion {ι : Sort _} {X : Type _} [TopologicalSpace X]
    (A : ι → Set X)
    (h : ∀ i, Topology.P1 (A i) ∧ Topology.P2 (A i) ∧ Topology.P3 (A i)) :
    Topology.P1 (⋃ i, A i) ∧ Topology.P2 (⋃ i, A i) ∧ Topology.P3 (⋃ i, A i) := by
  have hP1 : ∀ i, Topology.P1 (A i) := fun i => (h i).1
  have hP2 : ∀ i, Topology.P2 (A i) := fun i => (h i).2.1
  have hP3 : ∀ i, Topology.P3 (A i) := fun i => (h i).2.2
  exact
    ⟨Topology.P1_iUnion (A := A) hP1,
      Topology.P2_iUnion (A := A) hP2,
      Topology.P3_iUnion (A := A) hP3⟩