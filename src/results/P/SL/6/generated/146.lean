

theorem interior_closure_eq_self_of_P3_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) →
      interior (closure (A : Set X)) = closure A := by
  intro hP3
  have hOpen : IsOpen (closure (A : Set X)) :=
    Topology.open_of_P3_closure (A := A) hP3
  simpa using hOpen.interior_eq