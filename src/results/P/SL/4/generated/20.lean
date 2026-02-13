

theorem interior_closure_eq_interior_closure_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A → interior (closure A) = interior (closure (interior A)) := by
  intro hP1
  have h : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  simpa [h]