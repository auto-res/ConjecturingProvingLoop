

theorem Topology.image_closure_interior_subset_closure_image_interior
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {A : Set X} :
    f '' closure (interior A) ⊆ closure (f '' interior A) := by
  simpa using
    Topology.image_closure_subset_closure_image
      (X := X) (Y := Y) (f := f) hf (A := interior A)