

theorem Topology.denseInterior_implies_P2_closureInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) →
      Topology.P2 (X := X) (closure (interior (A : Set X))) := by
  intro hDense
  -- The density assumption yields `closure (interior A) = univ`.
  have h_closure : closure (interior (A : Set X)) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- `P2` holds for `univ`, and rewriting via `h_closure` gives the desired result.
  simpa [h_closure] using Topology.P2_univ (X := X)