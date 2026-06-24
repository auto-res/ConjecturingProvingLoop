

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X := X) (A := A)) : Topology.P3 (X := X) (A := A) := by
  dsimp [Topology.P2, Topology.P3] at h
  have hmono : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hcl : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    exact interior_mono hcl
  exact Set.Subset.trans h hmono