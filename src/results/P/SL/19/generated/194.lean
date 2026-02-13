

theorem Topology.closure_interior_union_frontier_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ∪ frontier A = closure A := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hIntClos =>
        have hSub :
            closure (interior A) ⊆ closure A :=
          Topology.closure_interior_subset_closure (A := A)
        exact hSub hIntClos
    | inr hFront =>
        exact hFront.1
  · intro hxClos
    by_cases hInt : x ∈ interior A
    · -- `x ∈ interior A`, hence in `closure (interior A)`
      have hxIntClos : x ∈ closure (interior A) := subset_closure hInt
      exact Or.inl hxIntClos
    · -- `x ∉ interior A`, so `x` lies in the frontier of `A`
      have hxFront : x ∈ frontier A := And.intro hxClos hInt
      exact Or.inr hxFront