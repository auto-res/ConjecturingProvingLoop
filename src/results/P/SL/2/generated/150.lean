

theorem Topology.P3_union_of_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Topology.P3 A → (B ⊆ interior (closure (A : Set X))) → Topology.P3 (A ∪ B) := by
  intro hP3A hBsub
  intro x hxUnion
  -- First, note that `interior (closure A)` is contained in
  -- `interior (closure (A ∪ B))`; this inclusion will be reused.
  have hsubset : interior (closure (A : Set X)) ⊆
      interior (closure (A ∪ B : Set X)) := by
    -- Since `A ⊆ A ∪ B`, the same holds after taking closures,
    -- and then interiors.
    have hcl : closure (A : Set X) ⊆ closure (A ∪ B : Set X) := by
      have hIncl : (A : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inl hy
      exact closure_mono hIncl
    exact interior_mono hcl
  -- Now distinguish whether `x` comes from `A` or from `B`.
  cases hxUnion with
  | inl hxA =>
      -- Case `x ∈ A`
      have hx_int : x ∈ interior (closure (A : Set X)) := hP3A hxA
      exact hsubset hx_int
  | inr hxB =>
      -- Case `x ∈ B`
      have hx_int : x ∈ interior (closure (A : Set X)) := hBsub hxB
      exact hsubset hx_int