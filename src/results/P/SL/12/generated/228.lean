

theorem Topology.P1_and_empty_interior_iff_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (Topology.P1 (X := X) A ∧ interior (A : Set X) = ∅) ↔ A = ∅ := by
  constructor
  · rintro ⟨hP1, hInt⟩
    -- From `P1` we have `A ⊆ closure (interior A)`.
    have h_sub : (A : Set X) ⊆ (∅ : Set X) := by
      have hA_sub : (A : Set X) ⊆ closure (interior A) := hP1
      simpa [hInt, closure_empty] using hA_sub
    -- The reverse inclusion is trivial.
    have h_empty_sub : (∅ : Set X) ⊆ A := Set.empty_subset _
    -- Conclude the desired equality of sets.
    exact Set.Subset.antisymm h_sub h_empty_sub
  · intro hA
    -- Rewrite everything in terms of `∅`.
    have hP1 : Topology.P1 (X := X) A := by
      simpa [hA] using Topology.P1_empty (X := X)
    have hInt : interior (A : Set X) = (∅ : Set X) := by
      simpa [hA] using (interior_empty : interior (∅ : Set X) = ∅)
    exact And.intro hP1 hInt