

theorem Topology.frontier_inter_eq_union_frontier_inter_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    frontier (A ∩ B : Set X) =
      (frontier A ∩ B) ∪ (frontier B ∩ A) := by
  classical
  -- Useful rewrites for frontiers of closed sets.
  have hFrontA :
      frontier (A : Set X) = A \ interior A :=
    (Topology.frontier_eq_diff_interior_of_isClosed (A := A) hA)
  have hFrontB :
      frontier (B : Set X) = B \ interior B :=
    (Topology.frontier_eq_diff_interior_of_isClosed (A := B) hB)
  have hClosedAB : IsClosed (A ∩ B : Set X) := IsClosed.inter hA hB
  have hFrontAB :
      frontier (A ∩ B : Set X) = (A ∩ B) \ interior (A ∩ B) :=
    (Topology.frontier_eq_diff_interior_of_isClosed
      (A := A ∩ B) hClosedAB)
  -- The interior of an intersection.
  have hIntAB :
      interior (A ∩ B : Set X) = interior A ∩ interior B :=
    Topology.interior_inter_eq_inter (A := A) (B := B)

  -- Establish the set equality.
  ext x; constructor
  · -- `→`  direction.
    intro hx
    -- Rewrite membership in `frontier (A ∩ B)`.
    have hxAB : x ∈ (A ∩ B) \ interior (A ∩ B) := by
      simpa [hFrontAB] using hx
    rcases hxAB with ⟨⟨hxA, hxB⟩, hNotIntAB⟩
    -- `x` fails to lie in `interior A ∩ interior B`.
    have hNotBoth : x ∉ interior A ∩ interior B := by
      simpa [hIntAB] using hNotIntAB
    -- Hence, `¬ x ∈ interior A ∧ x ∈ B` or `¬ x ∈ interior B ∧ x ∈ A`.
    have hCase : x ∉ interior A ∨ x ∉ interior B := by
      by_cases hIntA : x ∈ interior A
      · right
        intro hIntB; exact hNotBoth ⟨hIntA, hIntB⟩
      · left; exact hIntA
    cases hCase with
    | inl hNotIntA =>
        -- Build membership in `frontier A ∩ B`.
        have hxFrontA : x ∈ frontier A := by
          have : x ∈ A \ interior A := ⟨hxA, hNotIntA⟩
          simpa [hFrontA] using this
        exact Or.inl ⟨hxFrontA, hxB⟩
    | inr hNotIntB =>
        -- Build membership in `frontier B ∩ A`.
        have hxFrontB : x ∈ frontier B := by
          have : x ∈ B \ interior B := ⟨hxB, hNotIntB⟩
          simpa [hFrontB] using this
        exact Or.inr ⟨hxFrontB, hxA⟩
  · -- `←` direction.
    intro hx
    cases hx with
    | inl hLeft =>
        rcases hLeft with ⟨hxFrontA, hxB⟩
        -- Extract data from `hxFrontA`.
        have hxA : x ∈ A := by
          have : x ∈ A \ interior A := by
            simpa [hFrontA] using hxFrontA
          exact this.1
        have hNotIntA : x ∉ interior A := by
          have : x ∈ A \ interior A := by
            simpa [hFrontA] using hxFrontA
          exact this.2
        -- Show `x ∉ interior (A ∩ B)`.
        have hNotIntAB : x ∉ interior (A ∩ B) := by
          intro hIntAB
          have : x ∈ interior A ∩ interior B := by
            simpa [hIntAB] using hIntAB
          exact hNotIntA this.1
        -- Conclude membership in `frontier (A ∩ B)`.
        have : x ∈ (A ∩ B) \ interior (A ∩ B) :=
          ⟨⟨hxA, hxB⟩, hNotIntAB⟩
        simpa [hFrontAB] using this
    | inr hRight =>
        rcases hRight with ⟨hxFrontB, hxA⟩
        -- Extract data from `hxFrontB`.
        have hxB : x ∈ B := by
          have : x ∈ B \ interior B := by
            simpa [hFrontB] using hxFrontB
          exact this.1
        have hNotIntB : x ∉ interior B := by
          have : x ∈ B \ interior B := by
            simpa [hFrontB] using hxFrontB
          exact this.2
        -- Show `x ∉ interior (A ∩ B)`.
        have hNotIntAB : x ∉ interior (A ∩ B) := by
          intro hIntAB
          have : x ∈ interior A ∩ interior B := by
            simpa [hIntAB] using hIntAB
          exact hNotIntB this.2
        -- Conclude membership in `frontier (A ∩ B)`.
        have : x ∈ (A ∩ B) \ interior (A ∩ B) :=
          ⟨⟨hxA, hxB⟩, hNotIntAB⟩
        simpa [hFrontAB] using this