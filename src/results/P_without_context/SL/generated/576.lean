

theorem P2_implies_P1_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X:=X) A →
      (Topology.P1 (X:=X) A ∧ Topology.P3 (X:=X) A) := by
  intro hP2
  -- Derive P1 from P2
  have hP1 : Topology.P1 (X:=X) A := by
    dsimp [Topology.P1, Topology.P2] at hP2 ⊢
    exact Set.Subset.trans hP2 interior_subset
  -- Derive P3 from P2
  have hP3 : Topology.P3 (X:=X) A := by
    dsimp [Topology.P2] at hP2
    dsimp [Topology.P3]
    have h_closure : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    have h_mono : interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono h_closure
    exact Set.Subset.trans hP2 h_mono
  exact And.intro hP1 hP3