

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P3 A) (hB : P3 B) : P3 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : x ∈ interior (closure A) := hA hAx
      have h_subset :
          (interior (closure A) : Set X) ⊆ interior (closure (A ∪ B)) :=
        interior_mono
          (closure_mono
            (by
              simpa using (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)))
      exact h_subset hxA
  | inr hBx =>
      have hxB : x ∈ interior (closure B) := hB hBx
      have h_subset :
          (interior (closure B) : Set X) ⊆ interior (closure (A ∪ B)) :=
        interior_mono
          (closure_mono
            (by
              simpa using (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)))
      exact h_subset hxB

theorem P1_open {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen A) : P1 A := by
  exact P1_of_P2 (P2_open h_open)

theorem P3_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  exact Set.empty_subset _

theorem P3_empty {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) := by
  exact Set.empty_subset _