

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A := A) → P3 (A := A) := by
  intro hA
  dsimp [P2, P3] at *
  have hmono : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hsub : closure (interior A) ⊆ closure A := by
      exact closure_mono interior_subset
    exact interior_mono hsub
  exact hA.trans hmono