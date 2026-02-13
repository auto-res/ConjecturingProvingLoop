

theorem Topology.closure_interior_union_frontier_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X) ∪ frontier (A : Set X)) = closure (A : Set X) := by
  -- We prove the two inclusions separately.
  apply Set.Subset.antisymm
  · -- `⊆` : the left‐hand side is contained in `closure A`
    intro x hx
    -- First note that `interior A ⊆ A` and `frontier A ⊆ closure A`.
    have h₁ : (interior (A : Set X) ∪ frontier (A : Set X) : Set X) ⊆
        closure (A : Set X) := by
      intro y hy
      cases hy with
      | inl hyInt =>
          exact subset_closure (interior_subset hyInt)
      | inr hyFront =>
          exact (Topology.frontier_subset_closure (A := A)) hyFront
    -- Taking closures preserves inclusions; simplify with `closure_closure`.
    have : (closure (interior (A : Set X) ∪ frontier (A : Set X)) : Set X) ⊆
        closure (closure (A : Set X)) := closure_mono h₁
    simpa [closure_closure] using this hx
  · -- `⊇` : `closure A` is contained in the left‐hand side
    intro x hxClA
    -- It suffices to show `A ⊆ interior A ∪ frontier A`, because
    -- then monotonicity of `closure` yields the result.
    have hIncl : (A : Set X) ⊆ interior (A : Set X) ∪ frontier (A : Set X) := by
      intro y hyA
      by_cases hyInt : y ∈ interior (A : Set X)
      · exact Or.inl hyInt
      ·
        have hyFront : (y : X) ∈ frontier (A : Set X) :=
          And.intro (subset_closure hyA) hyInt
        exact Or.inr hyFront
    -- Apply monotonicity of `closure` to the inclusion `A ⊆ interior A ∪ frontier A`.
    have hClIncl :
        (closure (A : Set X) : Set X) ⊆
          closure (interior (A : Set X) ∪ frontier (A : Set X)) :=
      closure_mono hIncl
    exact hClIncl hxClA