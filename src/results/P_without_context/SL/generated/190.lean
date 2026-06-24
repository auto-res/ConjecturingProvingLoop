

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P3 A := by
  intro h2
  dsimp [P2, P3] at *
  have hcl : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  have hmono : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono hcl
  exact Set.Subset.trans h2 hmono