

theorem isOpen_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    P3 (X := X) A := by
  dsimp [P3]
  intro x hxA
  have hsubset : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal (subset_closure : (A : Set X) ⊆ closure A) hA
  exact hsubset hxA