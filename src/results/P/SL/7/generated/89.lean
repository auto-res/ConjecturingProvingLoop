

theorem Topology.closure_eq_univ_of_P1_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A)
    (hDense : closure (interior A) = (Set.univ : Set X)) :
    closure (A : Set X) = (Set.univ : Set X) := by
  have hEq : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (A := A)).1 hP1
  simpa using hEq.trans hDense