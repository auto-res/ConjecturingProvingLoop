

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 (A := A) := by
  intro hP2
  dsimp [Topology.P2, Topology.P1] at hP2 ⊢
  have hInt : interior (closure (interior A)) ⊆ closure (interior A) :=
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A))
  exact Set.Subset.trans hP2 hInt