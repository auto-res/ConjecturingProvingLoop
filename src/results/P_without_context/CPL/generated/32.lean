

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hP2
  exact
    hP2.trans
      (by
        simpa using interior_subset)

theorem P2_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A ↔ P3 A := by
  have hInt : interior A = A := hA.interior_eq
  simpa [P2, P3, hInt]

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : P2 A := by
  dsimp [P2]
  have hInt : interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
    simpa [h, interior_univ]
  simpa [hInt.symm] using (Set.subset_univ A)

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A = Set.univ) : P3 A := by
  dsimp [P3]
  have hInt : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa [h, interior_univ]
  simpa [hInt] using (Set.subset_univ A)