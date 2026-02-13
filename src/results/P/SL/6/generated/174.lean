

theorem P2_implies_P3_alt {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at *
  -- `closure (interior A)` sits inside `closure A`.
  have h₁ : closure (interior (A : Set X)) ⊆ closure A :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  -- Taking interiors preserves the inclusion.
  have h₂ :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h₁
  exact hP2.trans h₂