

theorem Topology.closure_eq_interior_closure_union_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) =
      interior (closure (A : Set X)) ∪ frontier (A : Set X) := by
  ext x
  constructor
  · intro hxCl
    by_cases hIntCl : x ∈ interior (closure (A : Set X))
    · exact Or.inl hIntCl
    ·
      -- `x` is not in `interior (closure A)`; we show it lies in the frontier.
      have hNotIntA : x ∉ interior (A : Set X) := by
        intro hIntA
        have : x ∈ interior (closure (A : Set X)) :=
          (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hIntA
        exact hIntCl this
      have hxFront : x ∈ frontier (A : Set X) :=
        And.intro hxCl hNotIntA
      exact Or.inr hxFront
  · intro h
    cases h with
    | inl hIntCl => exact interior_subset hIntCl
    | inr hFront => exact hFront.1