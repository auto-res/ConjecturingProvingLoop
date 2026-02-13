

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : P3 (X := X) A) (hB : P3 (X := X) B) :
    P3 (A ∪ B) := by
  dsimp [P3] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' : x ∈ interior (closure A) := hA hxA
      have hsubset : closure (A : Set X) ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact (interior_mono hsubset) hxA'
  | inr hxB =>
      have hxB' : x ∈ interior (closure B) := hB hxB
      have hsubset : closure (B : Set X) ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact (interior_mono hsubset) hxB'