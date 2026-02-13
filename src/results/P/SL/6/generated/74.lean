

theorem P2_implies_P1_v2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 A := by
  intro hP2
  dsimp [Topology.P2] at hP2
  dsimp [Topology.P1]
  have hIntSub : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset (s := closure (interior A))
  exact hP2.trans hIntSub