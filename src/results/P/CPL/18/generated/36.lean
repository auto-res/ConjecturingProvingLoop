

theorem P2_preimage_open_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) (h_open : IsOpenMap f) {B : Set Y} (hB : Topology.P2 B) : Topology.P2 (f ⁻¹' B) := by
  -- Unfold `P2` in the hypothesis and in the goal.
  dsimp [Topology.P2] at hB ⊢
  -- Take a point of the preimage.
  intro x hx
  -- Reformulate this point on the image side.
  have hfxB : f x ∈ (B : Set Y) := hx
  -- Apply the hypothesis `hB`.
  have hfx_int :
      f x ∈ interior (closure (interior (B : Set Y))) := hB hfxB
  /-  Consider the open set
        S = f ⁻¹' interior (closure (interior B)). -/
  set S : Set X := f ⁻¹' interior (closure (interior (B : Set Y))) with hSdef
  have hS_open : IsOpen S := by
    have : IsOpen (interior (closure (interior (B : Set Y)))) :=
      isOpen_interior
    simpa [hSdef] using this.preimage hf
  -- `x` belongs to `S`.
  have hxS : x ∈ S := by
    simpa [hSdef] using hfx_int
  -- Main inclusion:  `S ⊆ closure (interior (f ⁻¹' B))`.
  have hS_sub :
      S ⊆ closure (interior (f ⁻¹' (B : Set Y))) := by
    intro z hzS
    -- First, note that `f z ∈ closure (interior B)`.
    have hz_closure : f z ∈ closure (interior (B : Set Y)) := by
      have : f z ∈ interior (closure (interior (B : Set Y))) := by
        simpa [hSdef] using hzS
      exact interior_subset this
    -- We prove that `z` is in the desired closure.
    have : z ∈ closure (interior (f ⁻¹' (B : Set Y))) := by
      -- Use the neighbourhood characterization of the closure.
      apply (mem_closure_iff).2
      intro V hVopen hzV
      -- The image `f '' V` is open and contains `f z`.
      have hVimage_open : IsOpen (f '' V) := h_open _ hVopen
      have hfzV : f z ∈ f '' V := ⟨z, hzV, rfl⟩
      -- Since `f z` is in the closure of `interior B`,
      -- the intersection `(f '' V) ∩ interior B` is non-empty.
      have h_nonempty :
          ((f '' V) ∩ interior (B : Set Y)).Nonempty := by
        have hh := (mem_closure_iff).1 hz_closure
        exact hh _ hVimage_open hfzV
      rcases h_nonempty with ⟨y, ⟨⟨w, hwV, rfl⟩, hy_intB⟩⟩
      -- `w ∈ V` and `f w ∈ interior B`.
      -- Show that `w ∈ interior (f ⁻¹' B)`.
      have hw_int_pre : w ∈ interior (f ⁻¹' (B : Set Y)) := by
        -- First, `w ∈ f ⁻¹' interior B`.
        have hw_in_pre : w ∈ f ⁻¹' interior (B : Set Y) := hy_intB
        -- This set is open and contained in `f ⁻¹' B`.
        have hT_open : IsOpen (f ⁻¹' interior (B : Set Y)) :=
          (isOpen_interior.preimage hf)
        have hT_subset :
            (f ⁻¹' interior (B : Set Y)) ⊆ f ⁻¹' (B : Set Y) := by
          intro u hu
          dsimp [Set.preimage] at hu ⊢
          -- `interior_subset` turns `f u ∈ interior B` into `f u ∈ B`.
          exact (interior_subset hu)
        -- Hence this set is contained in the interior of `f ⁻¹' B`.
        have hT_subset_int :
            (f ⁻¹' interior (B : Set Y)) ⊆
              interior (f ⁻¹' (B : Set Y)) :=
          interior_maximal hT_subset hT_open
        exact hT_subset_int hw_in_pre
      -- Provide the required witness in `V ∩ interior (f ⁻¹' B)`.
      exact ⟨w, hwV, hw_int_pre⟩
    exact this
  -- Since `S` is open and contained in the closure, it is contained in its interior.
  have hS_sub_int :
      S ⊆ interior (closure (interior (f ⁻¹' (B : Set Y)))) :=
    interior_maximal hS_sub hS_open
  -- Conclude for the original point `x`.
  exact hS_sub_int hxS

theorem P2_iff_P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : Topology.P2 A ↔ Topology.P3 A := by
  -- `Dense (interior A)` already yields `P2 A`.
  have hP2_dense : Topology.P2 A :=
    P2_of_dense_interior (X := X) (A := A) h
  exact
    ⟨fun hP2 => P2_implies_P3 (X := X) (A := A) hP2,
     fun _hP3 => hP2_dense⟩