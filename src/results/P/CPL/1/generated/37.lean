

theorem P3_preimage_closed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} (hB : IsClosed B) {f : X → Y} (hf : Continuous f) (hB3 : P3 B) : P3 (f ⁻¹' B) := by
  intro x hx
  -- `B` is open because it is closed and satisfies `P3`.
  have h_int_eq : interior B = B :=
    interior_eq_of_P3_closed (A := B) hB hB3
  -- Regard `x` as belonging to the preimage of `interior B`.
  have hx_pre : x ∈ f ⁻¹' interior B := by
    simpa [Set.preimage, h_int_eq] using hx
  -- The preimage of `interior B` is open.
  have h_open : IsOpen (f ⁻¹' interior B) :=
    (isOpen_interior : IsOpen (interior B)).preimage hf
  -- This set is contained in the preimage of `B`.
  have h_sub : (f ⁻¹' interior B : Set X) ⊆ f ⁻¹' B :=
    Set.preimage_mono (interior_subset : (interior B : Set Y) ⊆ B)
  -- Hence it is contained in the interior of the preimage of `B`.
  have h_sub_int :
      (f ⁻¹' interior B : Set X) ⊆ interior (f ⁻¹' B) :=
    interior_maximal h_sub h_open
  -- Therefore `x` lies in `interior (f ⁻¹' B)`.
  have hx_int : x ∈ interior (f ⁻¹' B) := h_sub_int hx_pre
  -- Finally, use monotonicity of `interior` with respect to `closure`.
  exact
    (interior_mono
        (subset_closure : (f ⁻¹' B : Set X) ⊆ closure (f ⁻¹' B))) hx_int