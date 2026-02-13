

theorem P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure A = closure (interior A) := by
  constructor
  · intro h
    exact closure_eq_closure_interior_of_P1 h
  · intro h
    exact P1_of_closure_eq_closure_interior h