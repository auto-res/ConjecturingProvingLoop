

theorem closure_union_closure_complement {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) ∪ closure ((Aᶜ) : Set X) = (Set.univ : Set X) := by
  apply Set.Subset.antisymm
  · intro x _; exact Set.mem_univ x
  · intro x _
    classical
    by_cases h : (x : X) ∈ closure (A : Set X)
    · exact Or.inl h
    · have h_not_int : (x : X) ∉ interior (A : Set X) := by
        intro hx_int
        have hx_cl : (x : X) ∈ closure (A : Set X) :=
          (interior_subset_closure_self (A := A)) hx_int
        exact h hx_cl
      -- `closure (Aᶜ) = (interior A)ᶜ`
      have h_eq := closure_compl_eq_complement_interior (A := A)
      have hx_cl_compl : (x : X) ∈ closure ((Aᶜ) : Set X) := by
        have : (x : X) ∈ (interior (A : Set X))ᶜ := h_not_int
        simpa [h_eq] using this
      exact Or.inr hx_cl_compl