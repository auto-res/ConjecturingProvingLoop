

theorem Topology.eq_closure_interior_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = A) : Topology.P1 (X := X) A := by
  dsimp [Topology.P1]
  intro x hxA
  simpa [h] using hxA