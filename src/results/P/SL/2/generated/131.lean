

theorem interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B : Set X) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` lies in `interior A`, hence also in `interior (A ∪ B)`
      have hAB : (A : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inl hy
      have hsubset : (interior A : Set X) ⊆ interior (A ∪ B : Set X) :=
        interior_mono hAB
      exact hsubset hxA
  | inr hxB =>
      -- `x` lies in `interior B`, hence also in `interior (A ∪ B)`
      have hBB : (B : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inr hy
      have hsubset : (interior B : Set X) ⊆ interior (A ∪ B : Set X) :=
        interior_mono hBB
      exact hsubset hxB