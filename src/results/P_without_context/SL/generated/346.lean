

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hA
  unfold Topology.P2 Topology.P1 at *
  have h_sub : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact hA.trans h_sub