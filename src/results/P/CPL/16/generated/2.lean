

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  unfold P1
  intro x hx
  cases hx

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  unfold P1
  simpa [interior_univ, closure_univ]

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  unfold P2
  intro x hx
  cases hx

theorem P3_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) := by
  unfold P3
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  unfold P2
  intro x hx
  have : x ∈ interior (closure (interior A)) :=
    (interior_mono (subset_closure)) (by
      simpa [interior_interior] using hx)
  simpa [interior_interior] using this