

theorem P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) :
    Topology.P1 (A := A) ∧ Topology.P3 (A := A) := by
  dsimp [Topology.P2] at h
  constructor
  · dsimp [Topology.P1]
    have : interior (closure (interior A)) ⊆ closure (interior A) := interior_subset
    exact Set.Subset.trans h this
  · dsimp [Topology.P3]
    have hsub : closure (interior A) ⊆ closure A := by
      have : interior A ⊆ A := interior_subset
      exact closure_mono this
    have : interior (closure (interior A)) ⊆ interior (closure A) := interior_mono hsub
    exact Set.Subset.trans h this