

theorem Topology.boundary_union_subset_union_boundary {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∪ B) \ interior (A ∪ B) ⊆
      (closure A \ interior A) ∪ (closure B \ interior B) := by
  intro x hx
  rcases hx with ⟨hxClUnion, hxNotIntUnion⟩
  -- Express `x ∈ closure (A ∪ B)` in terms of the closures of the summands.
  have hCl : x ∈ closure A ∪ closure B := by
    have h_eq : closure (A ∪ B) = closure A ∪ closure B := by
      simpa using closure_union A B
    simpa [h_eq] using hxClUnion
  -- Distinguish the two cases of the union.
  cases hCl with
  | inl hxClA =>
      -- Show that `x ∉ interior A`, otherwise we contradict `hxNotIntUnion`.
      have hxNotIntA : x ∉ interior A := by
        intro hxIntA
        have hxIntUnion : x ∈ interior (A ∪ B) := by
          have h_subset : interior A ⊆ interior (A ∪ B) :=
            interior_mono (Set.subset_union_left : A ⊆ A ∪ B)
          exact h_subset hxIntA
        exact hxNotIntUnion hxIntUnion
      exact Or.inl ⟨hxClA, hxNotIntA⟩
  | inr hxClB =>
      -- Analogous argument for the second summand.
      have hxNotIntB : x ∉ interior B := by
        intro hxIntB
        have hxIntUnion : x ∈ interior (A ∪ B) := by
          have h_subset : interior B ⊆ interior (A ∪ B) :=
            interior_mono (Set.subset_union_right : B ⊆ A ∪ B)
          exact h_subset hxIntB
        exact hxNotIntUnion hxIntUnion
      exact Or.inr ⟨hxClB, hxNotIntB⟩