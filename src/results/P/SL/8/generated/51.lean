

theorem P1_imp_interior_closure_interior_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP1 : Topology.P1 A) :
    interior (closure (interior A)) = interior (closure A) := by
  have hEq : closure (interior A) = closure A :=
    Topology.P1_imp_closure_interior_eq_closure (X := X) (A := A) hP1
  simpa [hEq]