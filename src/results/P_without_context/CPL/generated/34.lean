

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hP2
  exact Set.Subset.trans hP2 interior_subset

theorem P1_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A := by
  simpa [P1, hA.interior_eq] using
    (subset_closure : (A : Set X) ⊆ closure A)

theorem P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A := by
  simpa [P2, hA.interior_eq] using
    (interior_maximal (subset_closure : (A : Set X) ⊆ closure A) hA)

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  simp [P1]

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  simp [P2]

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  dsimp [P1] at hA hB ⊢
  refine Set.union_subset ?_ ?_
  ·
    have h : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
      closure_mono
        (interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))
    exact hA.trans h
  ·
    have h : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
      closure_mono
        (interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B))
    exact hB.trans h

theorem closure_eq_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P1 A) : closure (interior A) = closure A := by
  apply Set.Subset.antisymm
  ·
    exact closure_mono (interior_subset : interior A ⊆ A)
  ·
    have h' : closure A ⊆ closure (closure (interior A)) :=
      closure_mono (h : (A : Set X) ⊆ closure (interior A))
    simpa [closure_closure] using h'

theorem P1_iff_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro h
    exact closure_eq_of_P1 h
  · intro hEq
    dsimp [P1]
    simpa [hEq.symm] using (subset_closure : (A : Set X) ⊆ closure A)