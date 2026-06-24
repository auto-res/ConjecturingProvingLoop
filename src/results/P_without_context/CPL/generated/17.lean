

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A := by
  intro hP2
  exact hP2.trans
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A))

theorem closure_interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    P1 A → closure (interior A) ⊆ closure A := by
  intro _
  simpa using (closure_mono (interior_subset : interior A ⊆ A))

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    P1 (interior A) := by
  dsimp [P1]
  simpa [interior_interior] using
    (subset_closure : interior A ⊆ closure (interior A))