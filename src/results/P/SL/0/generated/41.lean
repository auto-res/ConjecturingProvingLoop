

theorem interior_closure_has_all_Ps {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure (A : Set X))) ∧
    Topology.P2 (interior (closure (A : Set X))) ∧
    Topology.P3 (interior (closure (A : Set X))) := by
  -- Obtain `P1` and `P3` for `interior (closure A)`.
  have hP1P3 := Topology.interior_closure_has_P1_and_P3 (X := X) (A := A)
  -- Obtain `P2` for `interior (closure A)`.
  have hP2 := Topology.interior_closure_has_P2 (X := X) (A := A)
  -- Assemble the triple conjunction.
  exact And.intro hP1P3.1 (And.intro hP2 hP1P3.2)