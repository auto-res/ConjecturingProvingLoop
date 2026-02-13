

theorem P1_preimage_open_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) (h_open : IsOpenMap f) {B : Set Y} (hB : Topology.P1 B) : Topology.P1 (f ⁻¹' B) := by
  -- Unfold the definition of `P1`.
  dsimp [Topology.P1] at hB ⊢
  -- Take a point of the preimage.
  intro x hx
  -- View this point in the image space.
  have hfxB : f x ∈ (B : Set Y) := hx
  -- Apply the hypothesis on `B`.
  have h_cl : f x ∈ closure (interior (B : Set Y)) := hB hfxB
  -- We will show that `x` is in the closure of `interior (f ⁻¹' B)`.
  apply (mem_closure_iff).2
  intro U hU_open hxU
  -- The image of `U` is an open neighbourhood of `f x`.
  have h_fU_open : IsOpen (f '' U) := h_open _ hU_open
  have hfx_in_fU : f x ∈ f '' U := ⟨x, hxU, rfl⟩
  -- Hence it meets `interior B`.
  have h_nonempty :
      ((f '' U) ∩ interior (B : Set Y)).Nonempty :=
    (mem_closure_iff).1 h_cl (f '' U) h_fU_open hfx_in_fU
  -- Pick a point in the intersection.
  rcases h_nonempty with ⟨y, ⟨⟨z, hzU, rfl⟩, hz_intB⟩⟩
  -- `z ∈ U` and `f z ∈ interior B`.
  -- Show that `z ∈ interior (f ⁻¹' B)`.
  have hz_int : z ∈ interior (f ⁻¹' (B : Set Y)) := by
    -- First, `z` belongs to the preimage of `interior B`.
    have hz_pre : z ∈ f ⁻¹' interior (B : Set Y) := hz_intB
    -- This preimage is open …
    have h_open_pre : IsOpen (f ⁻¹' interior (B : Set Y)) :=
      (isOpen_interior.preimage hf)
    -- … and contained in `f ⁻¹' B`.
    have h_sub_pre :
        (f ⁻¹' interior (B : Set Y) : Set X) ⊆ f ⁻¹' (B : Set Y) := by
      intro t ht
      dsimp [Set.preimage] at ht ⊢
      exact interior_subset ht
    -- Hence it is contained in the interior of `f ⁻¹' B`.
    have h_to_int :
        (f ⁻¹' interior (B : Set Y) : Set X) ⊆
          interior (f ⁻¹' (B : Set Y)) :=
      interior_maximal h_sub_pre h_open_pre
    exact h_to_int hz_pre
  -- Provide the required witness in `U ∩ interior (f ⁻¹' B)`.
  exact ⟨z, hzU, hz_int⟩

theorem exists_P1_closed_dense {X : Type*} [TopologicalSpace X] : ∃ F : Set X, IsClosed F ∧ Dense F ∧ Topology.P1 F := by
  refine ⟨(Set.univ : Set X), isClosed_univ, dense_univ, ?_⟩
  simpa using (P1_univ (X := X))