

theorem frontier_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∪ B) ⊆ frontier A ∪ frontier B := by
  intro x hx
  -- Unpack the definition of `frontier`.
  rcases hx with ⟨hx_cl_union, hx_not_int_union⟩
  -- A point in `closure (A ∪ B)` lies in `closure A ∪ closure B`.
  have h_cl : x ∈ closure A ∪ closure B := by
    simpa [closure_union] using hx_cl_union
  -- Split on the two possibilities.
  cases h_cl with
  | inl hx_clA =>
      -- Show `x` is *not* in `interior A`.
      have hx_not_intA : x ∉ interior A := by
        intro hx_intA
        have : x ∈ interior (A ∪ B) := by
          have h_sub : interior A ⊆ interior (A ∪ B) :=
            interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
          exact h_sub hx_intA
        exact hx_not_int_union this
      -- Conclude `x ∈ frontier A`.
      exact Or.inl ⟨hx_clA, hx_not_intA⟩
  | inr hx_clB =>
      -- Symmetric argument for `B`.
      have hx_not_intB : x ∉ interior B := by
        intro hx_intB
        have : x ∈ interior (A ∪ B) := by
          have h_sub : interior B ⊆ interior (A ∪ B) :=
            interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
          exact h_sub hx_intB
        exact hx_not_int_union this
      exact Or.inr ⟨hx_clB, hx_not_intB⟩