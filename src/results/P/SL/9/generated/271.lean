

theorem Topology.frontier_union_eq_union_frontier_of_open_disjoint
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X))
    (hAB : Disjoint (A : Set X) B) :
    frontier (A ∪ B : Set X) = frontier A ∪ frontier B := by
  classical
  -- One inclusion is already available.
  have h₁ :
      frontier (A ∪ B : Set X) ⊆ frontier A ∪ frontier B :=
    frontier_union_subset_of_open (A := A) (B := B) hA hB
  -- For the reverse inclusion, treat each frontier separately.
  have h₂ :
      frontier A ∪ frontier B ⊆ frontier (A ∪ B : Set X) := by
    intro x hx
    cases hx with
    | inl hxA =>
        -- `x` lies in the frontier of `A`.
        have hx_clA : x ∈ closure (A : Set X) := hxA.1
        have hx_not_intA : x ∉ interior (A : Set X) := hxA.2
        -- `interior A = A` since `A` is open.
        have h_intA : interior (A : Set X) = A := hA.interior_eq
        have hx_not_A : x ∉ A := by
          simpa [h_intA] using hx_not_intA
        -- Show that `x ∉ B`.
        have hx_not_B : x ∉ B := by
          intro hxB
          -- Every open neighbourhood of `x` meets `A`, contradiction with disjointness.
          have hForall := (mem_closure_iff).1 hx_clA
          have h_nonempty : ((B : Set X) ∩ A).Nonempty :=
            hForall B hB hxB
          have h_empty : (A ∩ B : Set X) = ∅ := hAB.eq_bot
          have : (A ∩ B : Set X).Nonempty := by
            -- Convert `B ∩ A` to `A ∩ B`.
            simpa [Set.inter_comm] using h_nonempty
          simpa [h_empty] using this
        -- Membership in the closure of the union.
        have hx_cl_union : x ∈ closure (A ∪ B : Set X) :=
          (closure_mono (by
            intro y hy; exact Or.inl hy)) hx_clA
        -- `A ∪ B` is open, hence its interior equals itself.
        have h_int_union : interior (A ∪ B : Set X) = A ∪ B := by
          have h_open_union : IsOpen (A ∪ B) := IsOpen.union hA hB
          simpa using h_open_union.interior_eq
        -- `x` is not in the interior of the union.
        have hx_not_int_union : x ∉ interior (A ∪ B : Set X) := by
          have : x ∉ A ∪ B := by
            intro h_in
            cases h_in with
            | inl hA_in => exact hx_not_A hA_in
            | inr hB_in => exact hx_not_B hB_in
          simpa [h_int_union] using this
        exact ⟨hx_cl_union, hx_not_int_union⟩
    | inr hxB =>
        -- Symmetric argument with roles of `A` and `B` swapped.
        have hx_clB : x ∈ closure (B : Set X) := hxB.1
        have hx_not_intB : x ∉ interior (B : Set X) := hxB.2
        have h_intB : interior (B : Set X) = B := hB.interior_eq
        have hx_not_B : x ∉ B := by
          simpa [h_intB] using hx_not_intB
        -- Show `x ∉ A`.
        have hx_not_A : x ∉ A := by
          intro hxA
          have hForall := (mem_closure_iff).1 hx_clB
          have h_nonempty : ((A : Set X) ∩ B).Nonempty :=
            hForall A hA hxA
          have h_empty : (A ∩ B : Set X) = ∅ := hAB.eq_bot
          have : (A ∩ B : Set X).Nonempty := by
            simpa using h_nonempty
          simpa [h_empty] using this
        have hx_cl_union : x ∈ closure (A ∪ B : Set X) :=
          (closure_mono (by
            intro y hy; exact Or.inr hy)) hx_clB
        have h_int_union : interior (A ∪ B : Set X) = A ∪ B := by
          have h_open_union : IsOpen (A ∪ B) := IsOpen.union hA hB
          simpa using h_open_union.interior_eq
        have hx_not_int_union : x ∉ interior (A ∪ B : Set X) := by
          have : x ∉ A ∪ B := by
            intro h_in
            cases h_in with
            | inl hA_in => exact hx_not_A hA_in
            | inr hB_in => exact hx_not_B hB_in
          simpa [h_int_union] using this
        exact ⟨hx_cl_union, hx_not_int_union⟩
  exact subset_antisymm h₁ h₂