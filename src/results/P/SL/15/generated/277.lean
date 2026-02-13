

theorem closureInterior_eq_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (A : Set X) → Topology.P1 A := by
  intro hEq
  dsimp [Topology.P1]
  intro x hx
  simpa [hEq] using hx