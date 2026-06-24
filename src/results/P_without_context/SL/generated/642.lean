

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X := X) (A := A)) :
    Topology.P1 (X := X) (A := A) := by
  dsimp [Topology.P2, Topology.P1] at h ⊢
  have h' : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact Set.Subset.trans h h'