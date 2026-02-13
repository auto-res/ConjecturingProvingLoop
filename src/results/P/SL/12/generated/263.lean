

theorem Topology.preimage_interior_subset_interior_preimage
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) {B : Set Y} :
    f ⁻¹' interior (B : Set Y) ⊆ interior (f ⁻¹' B) := by
  -- The preimage of an open set under a continuous map is open.
  have h_open : IsOpen (f ⁻¹' interior (B : Set Y)) := by
    have : IsOpen (interior (B : Set Y)) := isOpen_interior
    exact this.preimage hf
  -- `f ⁻¹' interior B` is contained in `f ⁻¹' B` since `interior B ⊆ B`.
  have h_subset :
      (f ⁻¹' interior (B : Set Y)) ⊆ f ⁻¹' B :=
    Set.preimage_mono (interior_subset : interior (B : Set Y) ⊆ B)
  -- Apply the maximality of the interior for the open set `f ⁻¹' interior B`.
  intro x hx
  exact (interior_maximal h_subset h_open) hx