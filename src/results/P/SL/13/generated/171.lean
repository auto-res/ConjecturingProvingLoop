

theorem Topology.P3_inter_left_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen (A : Set X)) (hPB : Topology.P3 (X := X) B) :
    Topology.P3 (X := X) (A ∩ B) := by
  -- Unfold `P3` for `B`.
  dsimp [Topology.P3] at hPB ⊢
  intro x hxAB
  -- Split the membership in the intersection.
  have hxA : (x : X) ∈ A := hxAB.1
  have hxB : (x : X) ∈ B := hxAB.2
  -- Use `P3` for `B` to obtain an interior point.
  have hx_int_clB : (x : X) ∈ interior (closure B) := hPB hxB
  ------------------------------------------------------------------
  --  Construct an open neighbourhood `U := A ∩ interior (closure B)`
  --  that is contained in `closure (A ∩ B)`.
  ------------------------------------------------------------------
  have hU_open : IsOpen (A ∩ interior (closure B)) :=
    hA_open.inter isOpen_interior
  have hxU : (x : X) ∈ (A ∩ interior (closure B)) := ⟨hxA, hx_int_clB⟩
  -- `U` is contained in `closure (A ∩ B)`.
  have hU_subset : (A ∩ interior (closure B) : Set X) ⊆ closure (A ∩ B) := by
    intro y hy
    -- Separate the conditions on `y`.
    have hAy : (y : X) ∈ A := hy.1
    have hy_int : (y : X) ∈ interior (closure B) := hy.2
    -- Hence `y ∈ closure B`.
    have hClB : (y : X) ∈ closure B := interior_subset hy_int
    -- Show `y ∈ closure (A ∩ B)` via the neighbourhood characterization.
    have : (y : X) ∈ closure (A ∩ B) := by
      apply (mem_closure_iff).2
      intro U hUopen hyU
      -- Consider the open neighbourhood `U ∩ A` of `y`.
      have hUA_open : IsOpen (U ∩ A) := hUopen.inter hA_open
      have hyUA : (y : X) ∈ U ∩ A := ⟨hyU, hAy⟩
      -- Since `y ∈ closure B`, this set meets `B`.
      have h_nonempty :
          ((U ∩ A) ∩ B : Set X).Nonempty := by
        have h_prop := (mem_closure_iff).1 hClB
        have := h_prop (U ∩ A) hUA_open hyUA
        simpa [Set.inter_left_comm, Set.inter_assoc] using this
      -- Extract a witness in `U ∩ (A ∩ B)`.
      rcases h_nonempty with ⟨z, ⟨⟨hzU, hzA⟩, hzB⟩⟩
      exact ⟨z, ⟨hzU, ⟨hzA, hzB⟩⟩⟩
    exact this
  ------------------------------------------------------------------
  --  Apply `interior_maximal` to conclude.
  ------------------------------------------------------------------
  have h_into_int :
      (A ∩ interior (closure B) : Set X) ⊆ interior (closure (A ∩ B)) :=
    interior_maximal hU_subset hU_open
  exact h_into_int hxU