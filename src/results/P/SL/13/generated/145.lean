

theorem Topology.P1_inter_left_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hPA : Topology.P1 (X:=X) A) (hB_open : IsOpen (B : Set X)) :
    Topology.P1 (X:=X) (A ∩ B) := by
  dsimp [Topology.P1] at hPA ⊢
  intro x hx
  -- `x` belongs to both `A` and `B`.
  have hA : (x : X) ∈ A := hx.1
  have hB : (x : X) ∈ B := hx.2
  -- From `P1` for `A`, we know that `x` is in the closure of `interior A`.
  have hx_clA : x ∈ closure (interior A) := hPA hA
  -- We prove that `x` lies in the closure of `interior (A ∩ B)`.
  have hx_clAB : x ∈ closure (interior (A ∩ B)) := by
    -- Use the neighbourhood characterization of closure.
    apply (mem_closure_iff).2
    intro U hU hxU
    -- Consider the open neighbourhood `U ∩ B` of `x`.
    have hUB_open : IsOpen (U ∩ B) := hU.inter hB_open
    have hx_UB : (x : X) ∈ U ∩ B := ⟨hxU, hB⟩
    -- Apply the characterization of `hx_clA` with the neighbourhood `U ∩ B`.
    have h_nonempty : ((U ∩ B) ∩ interior A).Nonempty := by
      have h_prop := (mem_closure_iff).1 hx_clA
      have := h_prop (U ∩ B) hUB_open hx_UB
      -- Rearrange intersections to match Lean’s expectations.
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using this
    -- Extract a witness showing that `U` meets `interior (A ∩ B)`.
    rcases h_nonempty with ⟨y, ⟨⟨hyU, hyB⟩, hy_intA⟩⟩
    -- Since `B` is open, `interior B = B`.
    have hy_intB : y ∈ interior B := by
      simpa [hB_open.interior_eq] using hyB
    -- `interior (A ∩ B) = interior A ∩ interior B`.
    have h_int_eq : interior (A ∩ B) = interior A ∩ interior B := by
      simpa [Set.inter_comm] using interior_inter (A := A) (B := B)
    have hy_intAB : y ∈ interior (A ∩ B) := by
      have : y ∈ interior A ∩ interior B := ⟨hy_intA, hy_intB⟩
      simpa [h_int_eq] using this
    -- The required intersection with `U` is non‐empty.
    exact ⟨y, ⟨hyU, hy_intAB⟩⟩
  simpa using hx_clAB