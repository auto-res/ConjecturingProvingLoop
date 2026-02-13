

theorem closure_interior_closure_eq_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) →
      closure (interior (closure (A : Set X))) =
        closure (interior (A : Set X)) := by
  intro hA
  have hEq := closure_eq_closure_interior_of_P1 (A := A) hA
  calc
    closure (interior (closure (A : Set X)))
        = closure (interior (closure (interior (A : Set X)))) := by
          simpa [hEq]
    _ = closure (interior (A : Set X)) := by
          simpa using closure_interior_closure_interior (A := A)