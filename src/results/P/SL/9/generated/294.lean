

theorem Topology.closure_eq_self_union_frontier {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) = A ∪ frontier A := by
  classical
  ext x
  constructor
  · intro hx_cl
    by_cases hxA : x ∈ A
    · exact Or.inl hxA
    · -- `x` is in `closure A` but not in `A`; hence it lies in the frontier.
      have hx_not_int : x ∉ interior (A : Set X) := by
        intro hx_int
        exact hxA (interior_subset hx_int)
      exact Or.inr ⟨hx_cl, hx_not_int⟩
  · intro hx_union
    cases hx_union with
    | inl hxA      => exact subset_closure hxA
    | inr hxFront  => exact hxFront.1