

theorem P2_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P3 (X := X) A := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at *
  have h_closure : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have h_interior : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_closure
  exact Set.Subset.trans hP2 h_interior