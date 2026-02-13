

theorem P2_imp_closureInteriorClosure_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) :
    closure (interior (closure A)) = closure A := by
  -- First upgrade `P2 A` to `P3 A`.
  have hP3 : Topology.P3 A :=
    Topology.P2_imp_P3 (X := X) (A := A) hP2
  -- Then apply the existing result for `P3 A`.
  exact
    Topology.P3_imp_closureInteriorClosure_eq_closure (X := X) (A := A) hP3