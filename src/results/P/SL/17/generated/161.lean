

theorem Topology.P1_inter_isOpen_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hOpenA : IsOpen A) (hP1B : Topology.P1 B) :
    Topology.P1 (A ∩ B) := by
  unfold Topology.P1 at *
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- `x` is in the closure of `interior B` by `P1` for `B`
  have h_clB : x ∈ closure (interior B) := hP1B hxB
  -- We prove `x ∈ closure (interior (A ∩ B))` using `mem_closure_iff`
  have : x ∈ closure (interior (A ∩ B)) := by
    apply (mem_closure_iff).2
    intro U hU_open hxU
    -- Consider the open set `U ∩ A` that still contains `x`
    have hV_open : IsOpen (U ∩ A) := hU_open.inter hOpenA
    have hxV : x ∈ U ∩ A := ⟨hxU, hxA⟩
    -- Since `x ∈ closure (interior B)`, `U ∩ A` meets `interior B`
    have h_nonempty :=
      (mem_closure_iff).1 h_clB (U ∩ A) hV_open hxV
    rcases h_nonempty with ⟨y, ⟨hyU, hyA⟩, hyIntB⟩
    -- Show `y ∈ interior (A ∩ B)`
    have hyIntAB : y ∈ interior (A ∩ B) := by
      -- The open set `A ∩ interior B` contains `y` and is included in `A ∩ B`
      have h_open : IsOpen (A ∩ interior B) := hOpenA.inter isOpen_interior
      have h_subset : (A ∩ interior B) ⊆ A ∩ B := by
        intro z hz; exact ⟨hz.1, interior_subset hz.2⟩
      have hy_in : y ∈ A ∩ interior B := ⟨hyA, hyIntB⟩
      exact (interior_maximal h_subset h_open) hy_in
    exact ⟨y, ⟨hyU, hyIntAB⟩⟩
  exact this