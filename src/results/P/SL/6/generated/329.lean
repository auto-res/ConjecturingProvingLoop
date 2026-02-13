

theorem P2_inter_of_P2_and_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP2A : Topology.P2 (A : Set X)) (hOpenB : IsOpen (B : Set X)) :
    Topology.P2 (A ∩ B) := by
  -- Unfold `P2` for the given set and for the goal.
  dsimp [Topology.P2] at hP2A ⊢
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- From `P2` for `A`, place `x` in the required interior.
  have hxIntA : x ∈ interior (closure (interior A)) := hP2A hxA
  -- Define an auxiliary open neighbourhood of `x`.
  let V : Set X := interior (closure (interior A)) ∩ B
  have hV_open : IsOpen V := isOpen_interior.inter hOpenB
  have hxV    : x ∈ V := by
    dsimp [V]
    exact And.intro hxIntA hxB
  -- Show that this neighbourhood is contained in the desired closure.
  have hV_sub : (V : Set X) ⊆ closure (interior (A ∩ B)) := by
    intro y hyV
    rcases hyV with ⟨hyIntA, hyB⟩
    -- We prove `y ∈ closure (interior (A ∩ B))` via the neighbourhood
    -- characterisation of the closure.
    have hyClA : y ∈ closure (interior A) := by
      -- `interior S ⊆ S`
      exact (interior_subset : interior (closure (interior A)) ⊆
        closure (interior A)) hyIntA
    -- Reformulate the goal using `mem_closure_iff`.
    have : y ∈ closure (interior (A ∩ B)) := by
      -- Use `mem_closure_iff`.
      apply (mem_closure_iff).2
      intro U hU hyU
      -- Intersect the neighbourhood with `B`, which is open and contains `y`.
      have hU' : IsOpen (U ∩ B) := hU.inter hOpenB
      have hyU' : y ∈ U ∩ B := And.intro hyU hyB
      -- Since `y ∈ closure (interior A)`, this new neighbourhood meets `interior A`.
      have hNon : ((U ∩ B) ∩ interior (A : Set X)).Nonempty :=
        (mem_closure_iff).1 hyClA (U ∩ B) hU' hyU'
      rcases hNon with ⟨z, ⟨hzU, hzB⟩, hzIntA⟩
      -- `z` lies in `interior A ∩ B`, hence in `interior (A ∩ B)`
      -- because `B` is open.
      have hzIntAB : z ∈ interior (A ∩ B) := by
        -- `interior (A ∩ B) = interior A ∩ B` for an open `B`.
        have hEq :=
          interior_inter_of_isOpen_right (A := A) (B := B) hOpenB
        have hz : z ∈ interior A ∩ B := And.intro hzIntA hzB
        simpa [hEq] using hz
      -- Provide the witness required by `mem_closure_iff`.
      exact ⟨z, And.intro hzU hzIntAB⟩
    exact this
  -- Apply `interior_maximal` to conclude that `x` lies in the required interior.
  have hxGoal :
      x ∈ interior (closure (interior (A ∩ B))) :=
    (interior_maximal hV_sub hV_open) hxV
  exact hxGoal