

theorem Topology.closure_union_closure_compl_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∪ closure (Aᶜ) = (Set.univ : Set X) := by
  classical
  ext x
  constructor
  · intro _; trivial
  · intro _
    by_cases h : x ∈ closure A
    · exact Or.inl h
    · -- If `x ∉ closure A`, then `x` lies in the interior of `Aᶜ`,
      -- hence in `closure (Aᶜ)`.
      have hIntAcompl : x ∈ interior (Aᶜ) := by
        -- `interior (Aᶜ) = (closure A)ᶜ`.
        have h_eq :=
          Topology.interior_compl_eq_compl_closure (X := X) (A := A)
        have : x ∈ (closure A)ᶜ := by
          simpa using h
        simpa [h_eq] using this
      -- The interior is contained in the closure.
      have hClAcompl : x ∈ closure (Aᶜ) := by
        have : x ∈ (Aᶜ) := interior_subset hIntAcompl
        exact subset_closure this
      exact Or.inr hClAcompl