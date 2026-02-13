

theorem P2_imp_closure_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) :
    closure (interior A) = closure A := by
  have hP1 : Topology.P1 A :=
    Topology.P2_imp_P1 (X := X) (A := A) hP2
  exact P1_imp_closure_interior_eq_closure (X := X) (A := A) hP1