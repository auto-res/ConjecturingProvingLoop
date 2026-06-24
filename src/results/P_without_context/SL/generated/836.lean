

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at hP2 ⊢
  have hsubset : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have hinter : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono hsubset
  exact Set.Subset.trans hP2 hinter