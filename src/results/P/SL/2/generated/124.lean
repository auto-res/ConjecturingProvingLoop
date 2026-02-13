

theorem Topology.P1_of_closure_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (hEq : closure (interior A) = (A : Set X)) :
    Topology.P1 A := by
  intro x hxA
  simpa [hEq] using hxA