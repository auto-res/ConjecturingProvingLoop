

theorem closure_interior_eq_univ_of_P1_and_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A : Set X) →
      closure (A : Set X) = (Set.univ : Set X) →
      closure (interior (A : Set X)) = (Set.univ : Set X) := by
  intro hP1 hDense
  have hEq := closure_eq_closure_interior_of_P1 (A := A) hP1
  calc
    closure (interior (A : Set X))
        = closure (A : Set X) := by
          simpa using hEq.symm
    _ = (Set.univ : Set X) := hDense