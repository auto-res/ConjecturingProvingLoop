

theorem P2_imp_interior_closure_interior_eq_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) :
    interior (closure (interior A)) = interior (closure A) := by
  have h_eq : closure (interior A) = closure A :=
    Topology.P2_imp_closure_interior_eq_closure (X := X) (A := A) hP2
  simpa [h_eq]