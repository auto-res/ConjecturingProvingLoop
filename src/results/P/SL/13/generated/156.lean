

theorem Topology.P2_inter_left_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen (A : Set X)) (hPB : Topology.P2 (X := X) B) :
    Topology.P2 (X := X) (A ∩ B) := by
  -- Unfold the definition of `P2`.
  dsimp [Topology.P2] at hPB ⊢
  intro x hxAB
  -- Split the membership in the intersection.
  have hxA : (x : X) ∈ A := hxAB.1
  have hxB : (x : X) ∈ B := hxAB.2
  -- Use `P2` for `B` to place `x` in an appropriate interior.
  have hx_int : (x : X) ∈ interior (closure (interior B)) := hPB hxB
  -- Define the auxiliary open neighbourhood
  --   U = A ∩ interior (closure (interior B)).
  have hU_open : IsOpen (A ∩ interior (closure (interior B))) :=
    hA_open.inter isOpen_interior
  have hxU : (x : X) ∈ (A ∩ interior (closure (interior B))) :=
    ⟨hxA, hx_int⟩
  ------------------------------------------------------------------
  --  Step 1:  Show `U ⊆ closure (interior (A ∩ B))`.
  ------------------------------------------------------------------
  -- First enlarge `U` to `A ∩ closure (interior B)`.
  have h_step1 :
      (A ∩ interior (closure (interior B)) : Set X) ⊆
        A ∩ closure (interior B) := by
    intro y hy
    exact ⟨hy.1, interior_subset hy.2⟩
  -- Next show `A ∩ closure (interior B) ⊆ closure (interior (A ∩ B))`.
  have h_step2 :
      (A ∩ closure (interior B) : Set X) ⊆
        closure (interior (A ∩ B)) := by
    intro y hy
    have hyA  : (y : X) ∈ A := hy.1
    have hyCl : (y : X) ∈ closure (interior B) := hy.2
    ----------------------------------------------------------------
    --  Use the neighbourhood characterisation of closure.
    ----------------------------------------------------------------
    have hy_in_cl : (y : X) ∈ closure (A ∩ interior B) := by
      -- Characterisation of closure.
      apply (mem_closure_iff).2
      intro U hUopen hyU
      -- Consider `U ∩ A`, an open neighbourhood of `y`.
      have hUA_open : IsOpen (U ∩ A) := hUopen.inter hA_open
      have hyUA     : (y : X) ∈ U ∩ A := ⟨hyU, hyA⟩
      -- Since `y ∈ closure (interior B)`, the set `U ∩ A` meets `interior B`.
      have h_nonempty :
          ((U ∩ A) ∩ interior B : Set X).Nonempty := by
        have h_prop := (mem_closure_iff).1 hyCl
        have := h_prop (U ∩ A) hUA_open hyUA
        simpa [Set.inter_left_comm, Set.inter_assoc] using this
      rcases h_nonempty with ⟨z, ⟨⟨hzU, hzA⟩, hz_intB⟩⟩
      -- Exhibit the required point in `U ∩ (A ∩ interior B)`.
      exact ⟨z, ⟨hzU, hzA, hz_intB⟩⟩
    -- Rewrite using `interior (A ∩ B) = A ∩ interior B`
    -- (valid because `A` is open).
    have h_int_eq :
        interior (A ∩ B : Set X) = A ∩ interior B :=
      (Topology.interior_inter_open_left (X := X) (A := A) (B := B) hA_open)
    -- Convert `hy_in_cl` to the desired form.
    have : (y : X) ∈ closure (interior (A ∩ B)) := by
      simpa [h_int_eq] using hy_in_cl
    exact this
  -- Combine the two inclusions obtained so far.
  have h_subset :
      (A ∩ interior (closure (interior B)) : Set X) ⊆
        closure (interior (A ∩ B)) :=
    Set.Subset.trans h_step1 h_step2
  ------------------------------------------------------------------
  --  Step 2: Use `interior_maximal` to place `x` in the required interior.
  ------------------------------------------------------------------
  have h_into_interior :
      (A ∩ interior (closure (interior B)) : Set X) ⊆
        interior (closure (interior (A ∩ B))) :=
    interior_maximal h_subset hU_open
  exact h_into_interior hxU