

theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P3 A := by
  intro x hx
  exact (interior_mono (closure_mono interior_subset)) (hA hx)

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P3 A) (hB : P3 B) : P3 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hAx =>
      exact (interior_mono (closure_mono (Set.subset_union_left))) (hA hAx)
  | inr hBx =>
      exact (interior_mono (closure_mono (Set.subset_union_right))) (hB hBx)