

theorem closure_eq_closure_interior_closure_of_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 A → closure A = closure (interior (closure A)) := by
  intro hP3
  -- First, `P3 A` yields `P1 (closure A)`.
  have hP1 : Topology.P1 (closure A) :=
    Topology.P3_imp_P1_closure (A := A) hP3
  -- Apply the `P1` result to `closure A`.
  have hEq : closure (closure A) = closure (interior (closure A)) :=
    Topology.closure_eq_closure_interior_of_P1 (A := closure A) hP1
  -- Simplify `closure (closure A)` to `closure A`.
  simpa [closure_closure] using hEq