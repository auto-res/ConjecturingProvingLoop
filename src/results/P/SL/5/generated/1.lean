

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P3 A := by
  dsimp [P2, P3] at *
  intro x hxA
  have hsubset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  exact (interior_mono hsubset) (h hxA)