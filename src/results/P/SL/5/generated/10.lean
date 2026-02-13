

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : P2 (X := X) A) (hB : P2 (X := X) B) :
    P2 (A ∪ B) := by
  dsimp [P2] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' : x ∈ interior (closure (interior A)) := hA hxA
      have hsubset_inner : (interior A : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_inner
      exact (interior_mono hsubset) hxA'
  | inr hxB =>
      have hxB' : x ∈ interior (closure (interior B)) := hB hxB
      have hsubset_inner : (interior B : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_inner
      exact (interior_mono hsubset) hxB'