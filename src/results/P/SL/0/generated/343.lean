

theorem union_four_interiors_subset_interior_union_four
    {X : Type*} [TopologicalSpace X] {A B C D : Set X} :
    (interior (A : Set X) ∪ interior (B : Set X) ∪
        interior (C : Set X) ∪ interior (D : Set X)) ⊆
      interior (A ∪ B ∪ C ∪ D : Set X) := by
  intro x hx
  -- Split membership in the four‐way union into two cases.
  -- 1. `x` belongs to one of the first three interiors.
  -- 2. `x` belongs to `interior D`.
  cases hx with
  | inl hABC =>
      -- Reinterpret `hABC` as membership in `interior A ∪ interior B ∪ interior C`.
      have hABC' :
          x ∈ (interior (A : Set X) ∪ interior (B : Set X) ∪
              interior (C : Set X)) := by
        simpa [Set.union_assoc] using hABC
      -- Apply the existing three‐set lemma.
      have h₁ :=
        (Topology.union_three_interiors_subset_interior_union_three
            (X := X) (A := A) (B := B) (C := C)) hABC'
      -- Enlarge the target from the triple to the quadruple union.
      have hMono :
          interior (A ∪ B ∪ C : Set X) ⊆
            interior (A ∪ B ∪ C ∪ D : Set X) := by
        have hSub :
            (A ∪ B ∪ C : Set X) ⊆ (A ∪ B ∪ C ∪ D : Set X) := by
          intro y hy
          -- Interpret the right‐hand side as `(A ∪ B ∪ C) ∪ D`.
          have : y ∈ ((A ∪ B ∪ C) ∪ D : Set X) := Or.inl hy
          simpa [Set.union_assoc] using this
        exact interior_mono hSub
      exact hMono h₁
  | inr hD =>
      -- `x` lies in `interior D`; enlarge the target as in the previous case.
      have hSub :
          (D : Set X) ⊆ (A ∪ B ∪ C ∪ D : Set X) := by
        intro y hy
        have : y ∈ ((A ∪ B ∪ C) ∪ D : Set X) := Or.inr hy
        simpa [Set.union_assoc] using this
      have hMono :
          interior (D : Set X) ⊆
            interior (A ∪ B ∪ C ∪ D : Set X) :=
        interior_mono hSub
      exact hMono hD