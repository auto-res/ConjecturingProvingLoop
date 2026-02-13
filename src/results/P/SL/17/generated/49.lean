

theorem Topology.P1_iUnion_of_P2 {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    (∀ i, Topology.P2 (A i)) → Topology.P1 (Set.iUnion A) := by
  intro hP2
  have hP1 : ∀ i, Topology.P1 (A i) := fun i =>
    Topology.P2_implies_P1 (A := A i) (hP2 i)
  exact Topology.P1_iUnion (A := A) hP1