

theorem closure_interior_eq_closure_interior_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      closure (interior (A : Set X)) =
        closure (interior (closure (A : Set X))) := by
  intro hP2
  -- Upgrade `P2` to `P1`.
  have hP1 : Topology.P1 A :=
    (Topology.P2_implies_P1 (X := X) (A := A)) hP2
  -- Apply the equality obtained from `P1`.
  exact
    (Topology.P1_implies_closure_interior_eq_closure_interior_closure
      (X := X) (A := A)) hP1