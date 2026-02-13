

theorem Topology.P3_iUnion_of_P2 {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    (∀ i, Topology.P2 (A i)) → Topology.P3 (Set.iUnion A) := by
  intro hP2
  have hP3 : ∀ i, Topology.P3 (A i) :=
    fun i => Topology.P2_implies_P3 (A := A i) (hP2 i)
  exact Topology.P3_iUnion (A := A) hP3