

theorem P1_imp_closureInteriorClosure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    closure (interior (closure A)) = closure A := by
  -- First, upgrade `P1 A` to `P1 (closure A)`.
  have hP1_cl : Topology.P1 (closure A) :=
    Topology.P1_imp_P1_closure (X := X) (A := A) hP1
  -- Use the established equivalence for `closure A`.
  exact
    ((Topology.P1_closure_iff_closureInterior_eq_closure (X := X) (A := A)).1
      hP1_cl)