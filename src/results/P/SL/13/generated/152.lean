

theorem Topology.denseInterior_implies_interior_closure_interior_eq_univ {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) →
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
  intro hDense
  have h_closure : closure (interior (A : Set X)) = (Set.univ : Set X) :=
    hDense.closure_eq
  simpa [h_closure, interior_univ]