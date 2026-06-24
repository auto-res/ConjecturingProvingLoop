

theorem P1_closed_under_union {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  rintro hA hB
  dsimp [P1] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hxC : x ∈ closure (interior A) := hA hxA
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono Set.subset_union_left)
      exact hsubset hxC
  | inr hxB =>
      have hxC : x ∈ closure (interior B) := hB hxB
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono Set.subset_union_right)
      exact hsubset hxC

theorem P3_empty : P3 (∅ : Set X) := by
  dsimp [P3]
  exact Set.empty_subset _