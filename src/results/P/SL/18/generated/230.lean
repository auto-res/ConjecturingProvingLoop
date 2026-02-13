

theorem P3_of_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P3 A := by
  -- Obtain density of `interior A` from the closure equality.
  have hDenseInt : Dense (interior (A : Set X)) :=
    (Topology.dense_iff_closure_eq_univ
        (A := interior (A : Set X))).2 h
  -- Convert density into the desired property.
  exact Topology.P3_of_dense_interior (A := A) hDenseInt