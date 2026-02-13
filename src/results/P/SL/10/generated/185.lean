

theorem Topology.preimage_interior_subset_interior {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {B : Set Y} :
    f ⁻¹' interior B ⊆ interior (f ⁻¹' B) := by
  -- The preimage of an open set under a continuous map is open.
  have h_open : IsOpen (f ⁻¹' interior B) :=
    (isOpen_interior : IsOpen (interior B)).preimage hf
  -- Since `interior B ⊆ B`, their preimages satisfy the same inclusion.
  have h_subset : f ⁻¹' interior B ⊆ f ⁻¹' B := by
    intro x hx
    dsimp [Set.preimage] at hx ⊢
    exact interior_subset hx
  -- Any open subset of `f ⁻¹' B` is contained in its interior.
  exact interior_maximal h_subset h_open