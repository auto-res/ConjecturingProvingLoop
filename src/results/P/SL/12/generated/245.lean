

theorem Topology.P3_and_empty_interior_closure_iff_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (Topology.P3 (X := X) A ∧ interior (closure (A : Set X)) = ∅) ↔ A = ∅ := by
  constructor
  · rintro ⟨hP3, hInt⟩
    -- From `P3`, we have `A ⊆ interior (closure A)`.
    have h_sub : (A : Set X) ⊆ interior (closure A) := hP3
    -- Using the hypothesis `interior (closure A) = ∅`, we deduce `A ⊆ ∅`.
    have h_empty : (A : Set X) ⊆ (∅ : Set X) := by
      simpa [hInt] using h_sub
    -- Combine with the trivial inclusion `∅ ⊆ A` to get the desired equality.
    exact Set.Subset.antisymm h_empty (Set.empty_subset _)
  · intro hA
    -- Rewrite everything in terms of `∅`.
    have hP3 : Topology.P3 (X := X) A := by
      simpa [hA] using Topology.P3_empty (X := X)
    have hInt : interior (closure (A : Set X)) = (∅ : Set X) := by
      simpa [hA] using Topology.interior_closure_empty (X := X)
    exact And.intro hP3 hInt