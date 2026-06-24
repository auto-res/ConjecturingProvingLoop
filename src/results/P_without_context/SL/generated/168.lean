

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) : Topology.P1 (A := A) := by
  dsimp [Topology.P1, Topology.P2] at *
  exact fun x hx =>
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) (h hx)