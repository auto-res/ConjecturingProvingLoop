

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  have hInterSubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hClosureMono : closure (interior A) ⊆ closure A := by
      have hInt : interior A ⊆ A := interior_subset
      exact closure_mono hInt
    exact interior_mono hClosureMono
  exact subset_trans hP2 hInterSubset