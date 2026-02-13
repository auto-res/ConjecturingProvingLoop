

theorem Topology.boundary_inter_subset_union_boundary {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∩ B) \ interior (A ∩ B) ⊆
      (closure A \ interior A) ∪ (closure B \ interior B) := by
  intro x hx
  rcases hx with ⟨hxClAB, hxNotIntAB⟩
  -- `x` lies in the closure of each factor.
  have hxClA : x ∈ closure A :=
    (closure_mono (Set.inter_subset_left : A ∩ B ⊆ A)) hxClAB
  have hxClB : x ∈ closure B :=
    (closure_mono (Set.inter_subset_right : A ∩ B ⊆ B)) hxClAB
  -- Express the interior of the intersection in terms of the interiors.
  have hIntEq :
      interior (A ∩ B) = interior A ∩ interior B :=
    Topology.interior_inter_eq_inter (X := X) (A := A) (B := B)
  have hxNotIntInt : x ∉ interior A ∩ interior B := by
    intro hIntInt
    have : x ∈ interior (A ∩ B) := by
      simpa [hIntEq] using hIntInt
    exact hxNotIntAB this
  classical
  by_cases hIntA : x ∈ interior A
  · -- Then `x ∉ interior B`, hence `x` is in the boundary of `B`.
    have hNotIntB : x ∉ interior B := by
      intro hIntB
      exact hxNotIntInt ⟨hIntA, hIntB⟩
    exact Or.inr ⟨hxClB, hNotIntB⟩
  · -- Otherwise, `x` is in the boundary of `A`.
    exact Or.inl ⟨hxClA, hIntA⟩