

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro h
  have h' : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact Set.Subset.trans h h'