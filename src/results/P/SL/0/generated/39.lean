

theorem closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → closure (A : Set X) = closure (interior A) := by
  intro hP1
  exact ((Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A))).1 hP1