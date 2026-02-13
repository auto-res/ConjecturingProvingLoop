

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P1_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ P3 A := by
  have hP2_P3 := (P2_iff_P3_of_open (X := X) (A := A) hA)
  constructor
  · intro _hP1
    exact P3_of_open (X := X) (A := A) hA
  · intro hP3
    have hP2 : P2 A := (hP2_P3).2 hP3
    exact P2_subset_P1 (A := A) hP2

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A → P3 (interior A) := by
  intro _hP3
  intro x hx
  have hsubset : interior A ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · exact subset_closure
    · exact isOpen_interior
  exact hsubset hx

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx