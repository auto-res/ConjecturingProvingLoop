

theorem P2_of_dense_interior {X} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = (Set.univ : Set X)) : P2 A := by
  intro x hxA
  have hinterior : interior (closure (interior A)) = (Set.univ : Set X) := by
    simpa [h, interior_univ]
  simpa [hinterior] using (by
    simp : x ∈ (Set.univ : Set X))

theorem P1_union {X} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` originates from `A`
      have hx_closureA : x ∈ closure (interior A) := hA hxA
      -- `closure (interior A)` is contained in the desired closure
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        have hsubset_int : interior A ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        exact closure_mono hsubset_int
      exact hsubset hx_closureA
  | inr hxB =>
      -- `x` originates from `B`
      have hx_closureB : x ∈ closure (interior B) := hB hxB
      -- `closure (interior B)` is contained in the desired closure
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        have hsubset_int : interior B ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        exact closure_mono hsubset_int
      exact hsubset hx_closureB