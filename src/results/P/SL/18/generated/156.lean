

theorem P1_inter_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenB : IsOpen (B : Set X)) :
    Topology.P1 A → Topology.P1 (A ∩ B) := by
  intro hP1
  -- Unfold the definition of `P1`.
  dsimp [Topology.P1] at hP1 ⊢
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- `x` lies in the closure of `interior A`.
  have hxClA : x ∈ closure (interior A) := hP1 hxA
  -- We show that `x` belongs to the closure of `interior (A ∩ B)`.
  -- To this end, we establish a more general inclusion.
  have hIncl :
      (closure (interior A) ∩ B) ⊆ closure (interior (A ∩ B)) := by
    intro y hy
    rcases hy with ⟨hyClA, hyB⟩
    -- Characterize membership in a closure via neighbourhoods.
    have : y ∈ closure (interior (A ∩ B)) := by
      -- Use the neighbourhood formulation of `closure`.
      apply (mem_closure_iff).2
      intro U hU_open hyU
      -- Intersect the neighbourhood with `B`, which is open.
      have hU_B_open : IsOpen (U ∩ B) := hU_open.inter hOpenB
      have hyU_B : y ∈ U ∩ B := ⟨hyU, hyB⟩
      -- From `y ∈ closure (interior A)` we obtain a point of `interior A`
      -- meeting `U ∩ B`.
      have hNonempty :
          ((U ∩ B) ∩ interior A).Nonempty :=
        (mem_closure_iff).1 hyClA (U ∩ B) hU_B_open hyU_B
      rcases hNonempty with ⟨z, ⟨⟨hzU, hzB⟩, hzIntA⟩⟩
      -- Identify the interior of the intersection using openness of `B`.
      have hIntEq :
          interior (A ∩ B : Set X) = interior A ∩ B := by
        simpa [hOpenB.interior_eq] using interior_inter
      -- The point `z` lies in `U ∩ interior (A ∩ B)`.
      have hzIntAB : z ∈ interior (A ∩ B) := by
        have : z ∈ interior A ∩ B := ⟨hzIntA, hzB⟩
        simpa [hIntEq] using this
      exact ⟨z, ⟨hzU, hzIntAB⟩⟩
    exact this
  -- Apply the inclusion to our point `x`.
  have : x ∈ closure (interior (A ∩ B)) :=
    hIncl ⟨hxClA, hxB⟩
  exact this