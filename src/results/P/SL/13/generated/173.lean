

theorem Topology.denseInterior_implies_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P2 (X := X) (closure (A : Set X)) := by
  intro hDense
  have h_closure : closure (A : Set X) = (Set.univ : Set X) :=
    Topology.denseInterior_implies_closure_eq_univ (X := X) (A := A) hDense
  simpa [h_closure] using Topology.P2_univ (X := X)