

theorem nonempty_interior_of_nonempty_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → A.Nonempty → (interior (A : Set X)).Nonempty := by
  intro hP2 hNon
  -- Derive `P1` from `P2`.
  have hP1 : Topology.P1 (A : Set X) :=
    Topology.P2_implies_P1 (A := A) hP2
  -- Apply the existing lemma for `P1`.
  exact nonempty_interior_of_nonempty_P1 (A := A) hP1 hNon