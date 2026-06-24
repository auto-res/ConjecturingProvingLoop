

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P3 (X := X) A := by
  intro h
  dsimp [Topology.P2, Topology.P3] at h ⊢
  have hsubset : closure (interior A) ⊆ closure A := by
    exact closure_mono interior_subset
  have hsubset' : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono hsubset
  exact subset_trans h hsubset'