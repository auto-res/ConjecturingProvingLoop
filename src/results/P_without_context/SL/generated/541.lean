

theorem P2_implies_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P3 (X := X) A := by
  intro hP2
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hcl : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset)
    exact interior_mono hcl
  exact Set.Subset.trans hP2 hsubset