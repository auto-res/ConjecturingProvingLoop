

theorem Topology.closure_eq_closureInterior_of_denseInterior {X : Type*}
    [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior (A : Set X))) :
    closure (A : Set X) = closure (interior A) := by
  have hP1 : Topology.P1 (X := X) A :=
    Topology.denseInterior_implies_P1 (X := X) (A := A) hDense
  exact
    (Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)).1 hP1