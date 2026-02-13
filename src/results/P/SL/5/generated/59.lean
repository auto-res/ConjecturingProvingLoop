

theorem interior_closure_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) (hA : A.Nonempty) :
    (interior (closure (A : Set X))).Nonempty := by
  -- From `P2` we obtain `P3`.
  have hP3 : Topology.P3 (X := X) A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  -- Apply the corresponding result for `P3`.
  exact
    Topology.interior_closure_nonempty_of_P3 (X := X) (A := A) hP3 hA