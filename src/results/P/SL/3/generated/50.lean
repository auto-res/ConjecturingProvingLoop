

theorem interior_closure_eq_closure_interior_closure_of_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 (A : Set X) →
      interior (closure (A : Set X)) =
        interior (closure (interior (closure (A : Set X)))) := by
  intro hA
  have hEq := closure_eq_closure_interior_closure_of_P3 (A := A) hA
  simpa using congrArg interior hEq