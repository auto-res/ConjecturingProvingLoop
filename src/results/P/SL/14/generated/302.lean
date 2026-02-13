

theorem Topology.eq_univ_of_isClosed_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hDense : Dense (A : Set X)) :
    (A : Set X) = (Set.univ : Set X) := by
  -- Use the existing equivalence for closed sets and density.
  exact
    ((Topology.dense_iff_eq_univ_of_isClosed
        (X := X) (A := A) hA_closed).1) hDense