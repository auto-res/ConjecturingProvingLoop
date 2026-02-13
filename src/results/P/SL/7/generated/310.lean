

theorem Topology.interiorClosure_union_eq_interiorClosure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : (B : Set X) ⊆ interior (closure (A : Set X))) :
    interior (closure (A ∪ B : Set X)) = interior (closure (A : Set X)) := by
  apply Set.Subset.antisymm
  · -- `⊆` : from left to right
    -- First, show `A ∪ B ⊆ closure A`.
    have hAB : (A ∪ B : Set X) ⊆ closure (A : Set X) := by
      intro x hx
      cases hx with
      | inl hxA =>
          exact subset_closure hxA
      | inr hxB =>
          have : x ∈ interior (closure (A : Set X)) := hB hxB
          exact interior_subset this
    -- Taking closures preserves this inclusion.
    have hCl : closure (A ∪ B : Set X) ⊆ closure (A : Set X) := by
      have h := closure_mono hAB
      simpa [closure_closure] using h
    -- Applying `interior` yields the desired inclusion.
    exact interior_mono hCl
  · -- `⊇` : from right to left
    -- `A ⊆ A ∪ B`, hence `closure A ⊆ closure (A ∪ B)`.
    have hCl : closure (A : Set X) ⊆ closure (A ∪ B : Set X) :=
      closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
    -- Monotonicity of `interior` gives the required inclusion.
    exact interior_mono hCl