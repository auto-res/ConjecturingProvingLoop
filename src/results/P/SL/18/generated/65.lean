

theorem interior_closure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (A : Set X)) :
    interior (closure (A : Set X)) = Set.univ := by
  have hCl : closure (A : Set X) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ).1 hDense
  simpa [hCl, interior_univ]