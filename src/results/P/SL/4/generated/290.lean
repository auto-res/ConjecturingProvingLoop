

theorem interior_closure_union_frontier_eq_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure A) ∪ frontier (A : Set X) = closure A := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hIntCl => exact interior_subset hIntCl
    | inr hFront => exact hFront.1
  · intro hxCl
    by_cases hIntCl : x ∈ interior (closure A)
    · exact Or.inl hIntCl
    ·
      have h_not_intA : x ∉ interior A := by
        intro hIntA
        have h_sub : interior A ⊆ interior (closure A) :=
          Topology.interior_subset_interior_closure (A := A)
        have : x ∈ interior (closure A) := h_sub hIntA
        exact hIntCl this
      have hFront : x ∈ frontier A := And.intro hxCl h_not_intA
      exact Or.inr hFront