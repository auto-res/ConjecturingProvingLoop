

theorem nonempty_interior_closure_of_nonempty_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → A.Nonempty →
      (interior (closure (A : Set X))).Nonempty := by
  intro hP2 hNon
  -- From `P2` we can derive `P3`.
  have hP3 : Topology.P3 (A : Set X) :=
    Topology.P2_implies_P3 (A := A) hP2
  -- Apply the existing lemma for `P3`.
  exact nonempty_interior_closure_of_nonempty_P3 (A := A) hP3 hNon