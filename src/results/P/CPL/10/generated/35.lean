

theorem P2_inter {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (A ∩ B) := by
  classical
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- `P2` for the two factors
  have hxA_int : (x : X) ∈ interior (closure (interior A)) := hA hxA
  have hxB_int : (x : X) ∈ interior (closure (interior B)) := hB hxB

  -- An auxiliary open neighbourhood of `x`
  set U : Set X :=
      interior (closure (interior A)) ∩ interior (closure (interior B)) with hU_def
  have hU_open : IsOpen U := isOpen_interior.inter isOpen_interior
  have hxU : (x : X) ∈ U := by
    have : (x : X) ∈ interior (closure (interior A)) ∧
          x ∈ interior (closure (interior B)) := ⟨hxA_int, hxB_int⟩
    simpa [hU_def] using this

  ----------------------------------------------------------------
  --  Claim:  `U ⊆ closure (interior (A ∩ B))`
  ----------------------------------------------------------------
  have hU_subset : (U : Set X) ⊆ closure (interior (A ∩ B)) := by
    intro y hyU
    -- Split the membership information carried by `hyU`
    have hyA_int : y ∈ interior (closure (interior A)) := by
      have : y ∈ interior (closure (interior A)) ∧
            y ∈ interior (closure (interior B)) := by
        simpa [hU_def] using hyU
      exact this.1
    have hyB_int : y ∈ interior (closure (interior B)) := by
      have : y ∈ interior (closure (interior A)) ∧
            y ∈ interior (closure (interior B)) := by
        simpa [hU_def] using hyU
      exact this.2
    -- Turn the two facts into membership in the two closures
    have hy_clA : y ∈ closure (interior A) := interior_subset hyA_int
    have hy_clB : y ∈ closure (interior B) := interior_subset hyB_int

    -- Show `y ∈ closure (interior (A ∩ B))` using `mem_closure_iff`
    have : (y : X) ∈ closure (interior (A ∩ B)) := by
      -- Reformulate the goal: every open nbhd of `y` meets `interior (A ∩ B)`
      apply (mem_closure_iff).2
      intro V hV_open hyV
      ----------------------------------------------------------------
      -- 1st step: shrink the neighbourhood so that it lives inside both closures
      ----------------------------------------------------------------
      set W : Set X :=
          V ∩ interior (closure (interior A)) ∩
            interior (closure (interior B)) with hW_def
      have hW_open : IsOpen W := by
        have h₁ : IsOpen (V ∩ interior (closure (interior A))) :=
          hV_open.inter isOpen_interior
        simpa [hW_def, Set.inter_assoc] using h₁.inter isOpen_interior
      have hyW : y ∈ W := by
        have : y ∈ V ∧ y ∈ interior (closure (interior A)) ∧
                y ∈ interior (closure (interior B)) := ⟨hyV, hyA_int, hyB_int⟩
        simpa [hW_def, Set.inter_assoc] using this

      ----------------------------------------------------------------
      -- 2nd step: `W` meets `interior A`
      ----------------------------------------------------------------
      have hWA_nonempty : (W ∩ interior A).Nonempty := by
        -- `y ∈ closure (interior A)` so every neighbourhood meets it
        have := (mem_closure_iff).1 hy_clA W hW_open hyW
        simpa [Set.inter_left_comm, Set.inter_assoc] using this
      rcases hWA_nonempty with ⟨z₁, hz₁W, hz₁_intA⟩

      ----------------------------------------------------------------
      -- 3rd step: shrink once more around `z₁`
      ----------------------------------------------------------------
      set W₁ : Set X :=
          V ∩ interior (closure (interior B)) ∩ interior A with hW₁_def
      have hW₁_open : IsOpen W₁ := by
        have h₁ : IsOpen (V ∩ interior (closure (interior B))) :=
          hV_open.inter isOpen_interior
        simpa [hW₁_def, Set.inter_left_comm, Set.inter_assoc] using
          h₁.inter isOpen_interior

      -- show that `z₁ ∈ W₁`
      have hz₁V : (z₁ : X) ∈ V := by
        -- unpack `hz₁W`
        have : z₁ ∈ V ∧ z₁ ∈ interior (closure (interior A)) ∧
                z₁ ∈ interior (closure (interior B)) := by
          have : z₁ ∈ W := hz₁W
          simpa [hW_def, Set.inter_assoc] using this
        exact this.1
      have hz₁Bcl_int : z₁ ∈ interior (closure (interior B)) := by
        have : z₁ ∈ V ∧ z₁ ∈ interior (closure (interior A)) ∧
                z₁ ∈ interior (closure (interior B)) := by
          have : z₁ ∈ W := hz₁W
          simpa [hW_def, Set.inter_assoc] using this
        exact this.2.2
      have hz₁W₁ : z₁ ∈ W₁ := by
        have h : z₁ ∈ V ∧ z₁ ∈ interior (closure (interior B)) ∧
                 z₁ ∈ interior A :=
          And.intro hz₁V (And.intro hz₁Bcl_int hz₁_intA)
        simpa [hW₁_def, Set.inter_left_comm, Set.inter_assoc] using h

      ----------------------------------------------------------------
      -- 4th step: `W₁` meets `interior B`
      ----------------------------------------------------------------
      have hz₁_clB : z₁ ∈ closure (interior B) := by
        have : z₁ ∈ interior (closure (interior B)) := hz₁Bcl_int
        exact interior_subset this
      have hW₁_nonempty : (W₁ ∩ interior B).Nonempty :=
        (mem_closure_iff).1 hz₁_clB W₁ hW₁_open hz₁W₁
      rcases hW₁_nonempty with ⟨z, hzW₁, hz_intB⟩

      ----------------------------------------------------------------
      -- 5th step: properties of `z`
      ----------------------------------------------------------------
      have hz_components :
          z ∈ V ∧ z ∈ interior (closure (interior B)) ∧
            z ∈ interior A := by
        simpa [hW₁_def, Set.inter_left_comm, Set.inter_assoc] using hzW₁
      have hz_in_V : z ∈ V := hz_components.1
      have hz_intA : z ∈ interior A := hz_components.2.2

      -- `z ∈ interior A ∩ interior B`
      have hz_intAB : z ∈ interior (A ∩ B) := by
        -- `interior A ∩ interior B` is open and contained in `A ∩ B`
        have h_subset :
            (interior A ∩ interior B : Set X) ⊆ A ∩ B := by
          intro w hw
          exact
            ⟨(interior_subset : (interior A : Set X) ⊆ A) hw.1,
             (interior_subset : (interior B : Set X) ⊆ B) hw.2⟩
        have h_open : IsOpen (interior A ∩ interior B) :=
          isOpen_interior.inter isOpen_interior
        have hz_mem : z ∈ interior A ∩ interior B := ⟨hz_intA, hz_intB⟩
        exact (interior_maximal h_subset h_open) hz_mem

      -- Thus `V` meets `interior (A ∩ B)` at the point `z`
      exact ⟨z, hz_in_V, hz_intAB⟩
    exact this

  ----------------------------------------------------------------
  --  Finish:  `x` is in the interior of that closure.
  ----------------------------------------------------------------
  have hx_goal : (x : X) ∈ interior (closure (interior (A ∩ B))) :=
    (interior_maximal hU_subset hU_open) hxU
  exact hx_goal

theorem exists_dense_closed_P2 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, IsClosed A ∧ Dense A ∧ Topology.P2 A := by
  refine ⟨(Set.univ : Set X), isClosed_univ, dense_univ, ?_⟩
  simpa using (Topology.P2_univ (X := X))

theorem P1_iff_closure_interior_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P1 A ↔ closure (interior A) = A := by
  simpa [hA.closure_eq] using (Topology.P1_iff_dense (X := X) (A := A))

theorem P3_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) : Topology.P3 (Set.prod (Set.prod A B) C) := by
  -- Obtain `P3` for the product `A ×ˢ B`
  have hAB : Topology.P3 (Set.prod A B) :=
    Topology.P3_prod (X := X) (Y := Y) (A := A) (B := B) hA hB
  -- Combine with `hC` to get the desired result
  simpa using
    (Topology.P3_prod
        (X := X × Y) (Y := Z)
        (A := Set.prod A B) (B := C)
        hAB hC)