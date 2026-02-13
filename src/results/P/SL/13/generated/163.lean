

theorem Topology.closed_denseInterior_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (h_denseInt : Dense (interior (A : Set X))) :
    (A : Set X) = (Set.univ : Set X) := by
  -- From the density of `interior A`, we know that `closure A = univ`.
  have h_closure_univ :
      closure (A : Set X) = (Set.univ : Set X) :=
    Topology.denseInterior_implies_closure_eq_univ (X := X) (A := A) h_denseInt
  -- Since `A` is closed, its closure is itself.
  simpa [hA_closed.closure_eq] using h_closure_univ