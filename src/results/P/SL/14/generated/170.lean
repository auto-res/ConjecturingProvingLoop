

theorem Topology.closureInteriorClosure_eq_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → closure (interior (closure A)) = closure A := by
  intro hP2
  -- From `P2` we immediately obtain `P3`.
  have hP3 : Topology.P3 A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  -- The desired equality follows from the corresponding lemma for `P3`.
  exact
    Topology.closureInteriorClosure_eq_closure_of_P3
      (X := X) (A := A) hP3