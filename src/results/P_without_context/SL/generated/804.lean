

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P3 (X := X) A := by
  intro h
  dsimp [Topology.P2, Topology.P3] at *
  have hSub : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact Set.Subset.trans h hSub