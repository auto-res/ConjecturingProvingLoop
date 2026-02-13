

theorem P2_and_interior_closure_empty_implies_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      interior (closure (A : Set X)) = ∅ →
      A = ∅ := by
  intro hP2 hIntEmpty
  -- Derive `P3` from `P2`.
  have hP3 : Topology.P3 (A : Set X) :=
    Topology.P2_implies_P3 (A := A) hP2
  -- Apply the existing lemma for `P3`.
  exact
    Topology.P3_and_interior_closure_empty_implies_empty
      (A := A) hP3 hIntEmpty