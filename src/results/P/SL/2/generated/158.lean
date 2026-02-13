

theorem Topology.P2_union_of_subset_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → (B ⊆ interior (closure (interior A))) →
      Topology.P2 (A ∪ B) := by
  intro hP2A hBsub
  intro x hxUnion
  -- First, we build a useful inclusion that will be used in both cases.
  have hsubset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (A ∪ B))) := by
    -- Step 1: `interior A ⊆ interior (A ∪ B)`
    have hInt : (interior A : Set X) ⊆ interior (A ∪ B) := by
      have hSub : (A : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inl hy
      exact interior_mono hSub
    -- Step 2: take closures of both sides
    have hCl : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
      closure_mono hInt
    -- Step 3: take interiors again
    exact interior_mono hCl
  -- Now distinguish whether `x` comes from `A` or from `B`.
  cases hxUnion with
  | inl hxA =>
      -- Case `x ∈ A`
      have hx_int : x ∈ interior (closure (interior A)) := hP2A hxA
      exact hsubset hx_int
  | inr hxB =>
      -- Case `x ∈ B`
      have hx_int : x ∈ interior (closure (interior A)) := hBsub hxB
      exact hsubset hx_int