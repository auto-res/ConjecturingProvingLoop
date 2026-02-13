

theorem Topology.P1_inter_isOpen_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP1A : Topology.P1 A) (hOpenB : IsOpen B) :
    Topology.P1 (A ∩ B) := by
  -- Expand the definition of `P1`.
  unfold Topology.P1 at *
  -- Take an arbitrary point `x` in `A ∩ B`.
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- From `P1` for `A`, we know `x` is in `closure (interior A)`.
  have h_closure : x ∈ closure (interior A) := hP1A hxA
  -- We aim to prove `x ∈ closure (interior (A ∩ B))`.
  -- Use the neighbourhood‐based characterization of the closure.
  have : x ∈ closure (interior (A ∩ B)) := by
    -- Employ `mem_closure_iff`.
    apply (mem_closure_iff).2
    intro U hU_open hxU
    -- Refine the neighbourhood to stay inside `B`, which is open.
    have hV_open : IsOpen (U ∩ B) := hU_open.inter hOpenB
    have hxV : x ∈ U ∩ B := ⟨hxU, hxB⟩
    -- Since `x ∈ closure (interior A)`, this refined neighbourhood
    -- meets `interior A`.
    have h_nonempty :=
      (mem_closure_iff).1 h_closure (U ∩ B) hV_open hxV
    rcases h_nonempty with ⟨y, ⟨hyU, hyB⟩, hyIntA⟩
    -- Show the intersection point actually lies in `interior (A ∩ B)`.
    have hyIntAB : y ∈ interior (A ∩ B) := by
      -- `interior A` is open, and so is `B`; their intersection is open
      -- and contained in `A ∩ B`.
      have h_open : IsOpen (interior A ∩ B) :=
        isOpen_interior.inter hOpenB
      have h_subset : interior A ∩ B ⊆ A ∩ B := by
        intro z hz
        exact And.intro (interior_subset hz.1) hz.2
      have hy_mem : y ∈ interior A ∩ B := ⟨hyIntA, hyB⟩
      exact interior_maximal h_subset h_open hy_mem
    -- Conclude that `U` meets `interior (A ∩ B)`.
    exact ⟨y, ⟨hyU, hyIntAB⟩⟩
  -- Finish the proof.
  exact this