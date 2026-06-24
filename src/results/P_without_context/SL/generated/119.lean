

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P3 A := by
  intro hP2
  have h₁ : closure (interior (A : Set X)) ⊆ closure A :=
    closure_mono (interior_subset)
  have h₂ : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h₁
  exact Set.Subset.trans hP2 h₂