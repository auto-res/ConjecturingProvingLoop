

theorem Topology.closure_eq_closure_interior_closure_of_isOpen {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    closure A = closure (interior (closure A)) := by
  have hP3 : Topology.P3 A :=
    Topology.isOpen_implies_P3 (X := X) (A := A) hA
  exact
    Topology.closure_eq_closure_interior_closure_of_P3
      (X := X) (A := A) hP3