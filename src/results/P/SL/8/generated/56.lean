

theorem P3_imp_closureInteriorClosure_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) :
    closure (interior (closure A)) = closure A := by
  -- First, upgrade `P3 A` to `P1 (closure A)`
  have hP1 : Topology.P1 (closure A) :=
    Topology.P3_imp_P1_closure (X := X) (A := A) hP3
  -- Use the equivalence between `P1 (closure A)` and the desired equality
  exact
    ((Topology.P1_closure_iff_closureInterior_eq_closure (X := X) (A := A)).1 hP1)