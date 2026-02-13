

theorem Topology.interior_closure_preimage_subset
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {B : Set Y} :
    interior (closure (f ⁻¹' B)) ⊆ f ⁻¹' closure B := by
  intro x hx
  -- From `hx`, we know `x` lies in the interior of `closure (f ⁻¹' B)`.
  have hx_cl : x ∈ closure (f ⁻¹' B) := interior_subset hx
  -- Apply the previously proven inclusion for closures.
  have h_subset :
      closure (f ⁻¹' B) ⊆ f ⁻¹' closure B :=
    Topology.continuous_closure_preimage_subset (X := X) (Y := Y)
      (f := f) hf (B := B)
  exact h_subset hx_cl