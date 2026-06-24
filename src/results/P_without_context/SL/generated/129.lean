

theorem P2_implies_P1_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A ∧ Topology.P3 A :=
by
  intro hP2
  have hP1 : Topology.P1 A := by
    exact
      (Set.Subset.trans hP2
        (show interior (closure (interior A)) ⊆ closure (interior A) from
          interior_subset))
  have hP3 : Topology.P3 A := by
    have h₁ : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    have h₂ : interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono h₁
    exact Set.Subset.trans hP2 h₂
  exact And.intro hP1 hP3