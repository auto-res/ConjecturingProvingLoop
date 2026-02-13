

theorem Topology.P1_of_closureInterior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = (A : Set X)) : Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hx
  simpa [h] using hx