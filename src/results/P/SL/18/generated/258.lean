

theorem P2_of_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P2 A := by
  -- The hypothesis yields the density of `interior A`.
  have hDenseInt : Dense (interior (A : Set X)) :=
    (Topology.dense_interior_iff_closure_interior_eq_univ (A := A)).2 h
  -- Density of `interior A` implies `P2` for `A`.
  exact Topology.P2_of_dense_interior (A := A) hDenseInt