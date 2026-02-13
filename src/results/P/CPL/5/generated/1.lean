

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_empty {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P1_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P1 A := by
  intro x hx
  exact interior_subset (hA hx)

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hx
  have hsubset : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal (subset_closure) hA
  simpa [hA.interior_eq] using hsubset hx

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hAx =>
      have hsubset :
        interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) :=
        interior_mono
          (closure_mono
            (interior_mono
              (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)))
      exact hsubset (hA hAx)
  | inr hBx =>
      have hsubset :
        interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) :=
        interior_mono
          (closure_mono
            (interior_mono
              (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)))
      exact hsubset (hB hBx)