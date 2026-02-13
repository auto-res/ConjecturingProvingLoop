

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior A)) := by
  dsimp [Topology.P1]
  exact Topology.closure_interior_subset_closure_interior_closure_interior (A := A)