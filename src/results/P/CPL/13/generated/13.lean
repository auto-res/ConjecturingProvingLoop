

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} (hB : Topology.P2 B) : Topology.P2 (e ⁻¹' B) := by
  -- Unfold the definition of `P2`
  dsimp [Topology.P2] at hB ⊢
  -- Take an arbitrary point in `e ⁻¹' B`
  intro x hx
  -- Transport the membership through `e`
  have hxB : (e x : Y) ∈ B := by
    simpa [Set.preimage] using hx
  -- Apply the `P2` hypothesis on `B`
  have h_intB : (e x : Y) ∈ interior (closure (interior B)) := by
    have hB_sub : (B : Set Y) ⊆ interior (closure (interior B)) := by
      simpa using hB
    exact hB_sub hxB
  -- Identify the image of the preimage of `B`
  have h_image_preimage : (e '' (e ⁻¹' B) : Set Y) = B := by
    ext y
    constructor
    · rintro ⟨x', hx', rfl⟩
      simpa [Set.preimage] using hx'
    · intro hy
      refine ⟨e.symm y, ?_, ?_⟩
      · simpa [Set.preimage, e.apply_symm_apply] using hy
      · simpa [e.apply_symm_apply]
  -- Transport interiors and closures through `e`
  have h_image_interior :
      (e '' interior (e ⁻¹' B) : Set Y) = interior B := by
    simpa [h_image_preimage] using e.image_interior (s := (e ⁻¹' B))
  have h_image_closure :
      (e '' closure (interior (e ⁻¹' B)) : Set Y) = closure (interior B) := by
    simpa [h_image_interior] using
      e.image_closure (s := interior (e ⁻¹' B))
  have h_image_int_closure :
      (e '' interior (closure (interior (e ⁻¹' B))) : Set Y) =
        interior (closure (interior B)) := by
    simpa [h_image_closure] using
      e.image_interior (s := closure (interior (e ⁻¹' B)))
  -- Using the previous equality, rewrite the membership of `e x`
  have h_in_img :
      (e x : Y) ∈ e '' interior (closure (interior (e ⁻¹' B))) := by
    simpa [h_image_int_closure] using h_intB
  -- Extract the witness from the image membership
  rcases h_in_img with ⟨y, hy_in, hyeq⟩
  -- Injectivity of `e` gives `y = x`
  have : (y : X) = x := by
    apply e.injective
    simpa using hyeq
  -- Conclude
  simpa [this] using hy_in

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (hA : Topology.P2 A) : Topology.P2 (e '' A) := by
  dsimp [Topology.P2] at hA ⊢
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- Apply the `P2` hypothesis on `A`
  have hx : x ∈ interior (closure (interior A)) := hA hxA
  -- Transport this membership through `e`
  have hx₁ : (e x : Y) ∈ e '' interior (closure (interior A)) :=
    ⟨x, hx, rfl⟩
  -- Rewrite using `e.image_interior`
  have hx₂ : (e x : Y) ∈ interior (e '' closure (interior A)) := by
    simpa [e.image_interior (s := closure (interior A))] using hx₁
  -- Rewrite using `e.image_closure`
  have hx₃ : (e x : Y) ∈ interior (closure (e '' interior A)) := by
    simpa [e.image_closure (s := interior A)] using hx₂
  -- Rewrite using `e.image_interior` once more
  simpa [e.image_interior (s := A)] using hx₃

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} (hB : Topology.P1 B) : Topology.P1 (e ⁻¹' B) := by
  -- First, apply the image version to the inverse homeomorphism.
  have hP1 : Topology.P1 ((e.symm) '' B) :=
    Topology.P1_image_homeomorph (e := e.symm) (A := B) hB
  -- Identify this image with the desired preimage.
  have hEq : ((e.symm) '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      dsimp [Set.preimage] at *
      simpa using hy
    · intro hx
      dsimp [Set.preimage] at hx
      exact ⟨e x, hx, by
        simp⟩
  -- Conclude using the set equality.
  simpa [hEq] using hP1