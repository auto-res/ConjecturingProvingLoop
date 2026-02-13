

theorem P2_and_interior_empty_implies_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → interior (A : Set X) = ∅ → A = ∅ := by
  intro hP2 hIntEmpty
  -- Derive `P1` from `P2`.
  have hP1 : Topology.P1 (A : Set X) :=
    Topology.P2_implies_P1 (A := A) hP2
  -- Apply the existing lemma for `P1`.
  exact
    Topology.P1_and_interior_empty_implies_empty
      (A := A) hP1 hIntEmpty