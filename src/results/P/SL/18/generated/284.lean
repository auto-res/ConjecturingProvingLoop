

theorem P2_of_P1_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A : Set X)) (hDense : Dense (A : Set X)) :
    Topology.P2 (A : Set X) := by
  -- First, `closure (interior A) = univ` by the existing lemma.
  have hClos : closure (interior (A : Set X)) = (Set.univ : Set X) :=
    Topology.closure_interior_eq_univ_of_P1_and_dense (A := A) hP1 hDense
  -- Consequently, `interior (closure (interior A)) = univ`.
  have hInt : interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
    simpa [hClos, interior_univ]
  -- Apply the lemma that turns this interior equality into `P2`.
  exact
    Topology.P2_of_interior_closure_interior_eq_univ (A := A) hInt