

theorem Topology.P1_union_of_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Topology.P1 A → (B ⊆ closure (interior A)) → Topology.P1 (A ∪ B) := by
  intro hP1A hBsub
  intro x hxUnion
  -- We will show that `x` belongs to `closure (interior (A ∪ B))`
  -- by distinguishing the cases `x ∈ A` or `x ∈ B`.
  have hIncl :
      closure (interior A) ⊆ closure (interior (A ∪ B)) := by
    -- First, note that `interior A ⊆ interior (A ∪ B)`.
    have hIntSub : (interior A : Set X) ⊆ interior (A ∪ B) := by
      have hASub : (A : Set X) ⊆ A ∪ B := by
        intro y hy; exact Or.inl hy
      exact interior_mono hASub
    -- Taking closures preserves inclusions.
    exact closure_mono hIntSub
  cases hxUnion with
  | inl hxA =>
      -- Case `x ∈ A`
      have hx_cl : x ∈ closure (interior A) := hP1A hxA
      exact hIncl hx_cl
  | inr hxB =>
      -- Case `x ∈ B`
      have hx_cl : x ∈ closure (interior A) := hBsub hxB
      exact hIncl hx_cl