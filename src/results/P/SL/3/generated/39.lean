

theorem interior_closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A : Set X) →
      interior (closure (A : Set X)) =
        interior (closure (interior (A : Set X))) := by
  intro hA
  have hEq : closure (A : Set X) = closure (interior (A : Set X)) :=
    closure_eq_closure_interior_of_P1 (A := A) hA
  simpa [hEq]