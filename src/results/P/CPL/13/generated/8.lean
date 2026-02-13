

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} (hB : Topology.P3 B) : Topology.P3 (e ⁻¹' B) := by
  -- Unfold the definition of `P3`
  dsimp [Topology.P3] at *
  intro x hx
  -- `hx` tells us that `e x ∈ B`
  have hxB : (e x : Y) ∈ B := hx
  -- Apply `hB` to obtain that `e x` lies in the interior of `closure B`
  have hx_int : (e x : Y) ∈ interior (closure B) := hB hxB
  -- We establish that `e '' (e ⁻¹' B) = B`
  have h_image_preimage : (e '' (e ⁻¹' B) : Set Y) = B := by
    ext y
    constructor
    · rintro ⟨x', hx', rfl⟩
      exact hx'
    · intro hy
      refine ⟨e.symm y, ?_, ?_⟩
      · dsimp [Set.preimage]
        simpa [e.apply_symm_apply] using hy
      · simpa [e.apply_symm_apply]
  -- Using the previous equality, rewrite the images of closures and interiors
  have h_image_closure :
      (e '' closure (e ⁻¹' B) : Set Y) = closure B := by
    have := e.image_closure (s := (e ⁻¹' B))
    simpa [h_image_preimage] using this
  have h_image_interior :
      (e '' interior (closure (e ⁻¹' B)) : Set Y) = interior (closure B) := by
    have := e.image_interior (s := closure (e ⁻¹' B))
    simpa [h_image_closure] using this
  -- Transport the membership of `e x`
  have h_in_img : (e x : Y) ∈ e '' interior (closure (e ⁻¹' B)) := by
    simpa [h_image_interior.symm] using hx_int
  -- Extract the witness from the image membership
  rcases h_in_img with ⟨y, hy_in, hyeq⟩
  -- Injectivity of `e` gives `y = x`
  have : (y : X) = x := by
    apply e.injective
    simpa using hyeq
  -- Conclude
  simpa [this] using hy_in