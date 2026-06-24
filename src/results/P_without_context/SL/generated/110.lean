

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (X := X) A → P1 (X := X) A := by
  intro hP2
  have hstep : interior (closure (interior A)) ⊆ closure (interior A) := by
    simpa using (interior_subset (s := closure (interior A)))
  exact Set.Subset.trans hP2 hstep