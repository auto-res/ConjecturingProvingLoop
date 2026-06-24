

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P3 (A := A) := by
  intro h
  dsimp [Topology.P2, Topology.P3] at h ⊢
  have h₁ : closure (interior A) ⊆ closure A := closure_mono interior_subset
  have h₂ : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h₁
  exact Set.Subset.trans h h₂