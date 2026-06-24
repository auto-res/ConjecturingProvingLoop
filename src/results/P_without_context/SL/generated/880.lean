

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (A := A)) : Topology.P1 (A := A) := by
  intro x hx
  exact (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) (hA hx)