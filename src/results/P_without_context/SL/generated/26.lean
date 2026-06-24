

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P3 A := by
  intro hA
  dsimp [Topology.P2, Topology.P3] at hA ⊢
  have h_sub : interior (closure (interior (A : Set X))) ⊆ interior (closure A) := by
    have h_closure : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    exact interior_mono h_closure
  exact Set.Subset.trans hA h_sub