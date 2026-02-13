

theorem closure_interior_eq_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → closure (interior A) = closure A := by
  intro hP1
  exact (Topology.P1_iff_closure_interior_eq_closure (A := A)).1 hP1