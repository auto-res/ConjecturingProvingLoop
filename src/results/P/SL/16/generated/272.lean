

theorem Topology.interior_closure_interior_eq_univ_of_dense_and_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure A = (Set.univ : Set X))
    (hP1 : Topology.P1 (X := X) A) :
    interior (closure (interior A)) = (Set.univ : Set X) := by
  -- From `P1`, the two closures coincide.
  have h_eq : closure (interior A) = closure A :=
    Topology.closure_interior_eq_closure_of_P1 (X := X) (A := A) hP1
  -- Rewrite using both equalities and simplify.
  calc
    interior (closure (interior A)) = interior (closure A) := by
      simpa [h_eq]
    _ = interior (Set.univ : Set X) := by
      simpa [h_dense]
    _ = (Set.univ : Set X) := by
      simpa [interior_univ]