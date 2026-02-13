

theorem frontier_union_subset_frontier_left_union_closure_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∪ B : Set X) ⊆ frontier A ∪ closure B := by
  intro x hx
  rcases hx with ⟨hx_cl_union, hx_not_int_union⟩
  by_cases hB : x ∈ closure B
  · exact Or.inr hB
  ·
    -- First, rewrite `closure (A ∪ B)` as `closure A ∪ closure B`
    have hx_clA_or : x ∈ closure A ∪ closure B := by
      have h_eq := closure_union (s := A) (t := B)
      simpa [h_eq] using hx_cl_union
    -- Since `x ∉ closure B`, we deduce `x ∈ closure A`
    have hx_clA : x ∈ closure A := by
      cases hx_clA_or with
      | inl hA   => exact hA
      | inr hB'  => exact (hB hB').elim
    -- Show that `x ∉ interior A`
    have hx_not_intA : x ∉ interior A := by
      intro hx_intA
      -- `interior A ⊆ interior (A ∪ B)` by monotonicity
      have hx_int_union : x ∈ interior (A ∪ B) := by
        have h_subset :
            interior A ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        exact h_subset hx_intA
      exact hx_not_int_union hx_int_union
    -- Therefore `x ∈ frontier A`
    have hx_frontA : x ∈ frontier A := And.intro hx_clA hx_not_intA
    exact Or.inl hx_frontA