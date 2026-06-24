

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 A) : Topology.P3 A := by
  dsimp [Topology.P2] at h
  dsimp [Topology.P3]
  refine Set.Subset.trans h ?_
  have h_closure : closure (interior A) ⊆ closure A := by
    have : interior A ⊆ A := interior_subset
    exact closure_mono this
  have h_int : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_closure
  exact h_int