

theorem P1_and_denseInterior_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Dense (interior A) → Topology.P2 A := by
  intro _ hDenseInt
  exact
    Topology.denseInterior_implies_P2 (X := X) (A := A) hDenseInt