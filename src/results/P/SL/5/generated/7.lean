

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : P1 (X := X) A) (hB : P1 (X := X) B) : P1 (A ∪ B) := by
  dsimp [P1] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' : x ∈ closure (interior A) := hA hxA
      have hsubset : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact (closure_mono hsubset) hxA'
  | inr hxB =>
      have hxB' : x ∈ closure (interior B) := hB hxB
      have hsubset : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact (closure_mono hsubset) hxB'