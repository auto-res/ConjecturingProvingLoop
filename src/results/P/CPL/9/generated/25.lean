

theorem P1_image_homeomorph' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (hA : Topology.P1 (A := A)) : Topology.P1 (A := e.symm ⁻¹' A) := by
  -- Identify the preimage with the image of `A`.
  have hEq : (e.symm ⁻¹' A : Set Y) = e '' A := by
    ext y
    constructor
    · intro hy
      exact
        ⟨e.symm y, hy, by
          simpa using (e.apply_symm_apply y)⟩
    · intro hy
      rcases hy with ⟨x, hxA, rfl⟩
      simpa using hxA
  -- `P1` holds for `e '' A`.
  have hP1_image : Topology.P1 (A := e '' A) :=
    P1_image_homeomorph (e := e) (A := A) hA
  -- Prove the required inclusion using `hEq`.
  intro y hy
  have hy_image : y ∈ e '' A := by
    simpa [hEq] using hy
  have h_closure : y ∈ closure (interior (e '' A)) :=
    hP1_image hy_image
  simpa [hEq] using h_closure

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (hA : Topology.P2 (A := A)) : Topology.P2 (A := e '' A) := by
  intro y hy
  -- pick a preimage point
  rcases hy with ⟨x, hxA, rfl⟩
  -- `P2` for `A`
  have hx_int : (x : X) ∈ interior (closure (interior A)) := hA hxA
  -- map through the homeomorphism, using `image_interior`
  have hx_int_image : (e x : Y) ∈ interior (e '' closure (interior A)) := by
    -- first, `e x` lies in the image of the interior
    have h_mem : (e x : Y) ∈ e '' interior (closure (interior A)) :=
      ⟨x, hx_int, rfl⟩
    have h_eq := e.image_interior (s := closure (interior A))
    simpa [h_eq] using h_mem
  -- identify the closure via `image_closure`
  have hx_int_image' : (e x : Y) ∈ interior (closure (e '' interior A)) := by
    have h_closure_eq := e.image_closure (s := interior A)
    simpa [h_closure_eq] using hx_int_image
  -- rewrite using `image_interior` once more
  have h_int_eq : (e '' interior A : Set Y) = interior (e '' A) := by
    simpa using e.image_interior (s := A)
  have hx_target : (e x : Y) ∈ interior (closure (interior (e '' A))) := by
    simpa [h_int_eq] using hx_int_image'
  exact hx_target

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (hA : Topology.P3 (A := A)) : Topology.P3 (A := e '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` lies in the interior of the closure of `A`.
  have hx_int : (x : X) ∈ interior (closure A) := hA hxA
  -- Transport this fact through the homeomorphism.
  have hx_int_image : (e x : Y) ∈ interior (e '' closure A) := by
    -- First, `e x` belongs to `e '' interior (closure A)`.
    have h_mem : (e x : Y) ∈ (e '' interior (closure A) : Set Y) :=
      ⟨x, hx_int, rfl⟩
    -- Identify this image with the desired interior.
    have h_eq : (e '' interior (closure A) : Set Y) = interior (e '' closure A) := by
      simpa using e.image_interior (s := closure A)
    simpa [h_eq] using h_mem
  -- Relate `e '' closure A` to `closure (e '' A)`.
  have h_closure_eq : (e '' closure A : Set Y) = closure (e '' A) := by
    simpa using e.image_closure (s := A)
  -- Rewrite to obtain the final membership.
  have hx_target : (e x : Y) ∈ interior (closure (e '' A)) := by
    simpa [h_closure_eq] using hx_int_image
  exact hx_target

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} (hB : Topology.P1 (A := B)) : Topology.P1 (A := e ⁻¹' B) := by
  -- Identify the preimage with the image under `e.symm`.
  have hEq : (e ⁻¹' B : Set X) = (e.symm '' B) := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, by
        simp⟩
    · rintro ⟨y, hyB, rfl⟩
      simpa [e.apply_symm_apply] using hyB
  -- Apply the existing lemma to obtain `P1` for `e.symm '' B`.
  have hP1 : Topology.P1 (A := e.symm '' B) :=
    P1_image_homeomorph (e := e.symm) (A := B) hB
  -- Transport the property along the set equality.
  simpa [hEq] using hP1

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} (hB : Topology.P2 (A := B)) : Topology.P2 (A := e ⁻¹' B) := by
  -- Identify the preimage with the image under `e.symm`.
  have hEq : (e ⁻¹' B : Set X) = e.symm '' B := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, by simp⟩
    · rintro ⟨y, hyB, rfl⟩
      simpa using hyB
  -- `P2` holds for `e.symm '' B`.
  have hP2_image : Topology.P2 (A := e.symm '' B) :=
    P2_image_homeomorph (e := e.symm) (A := B) hB
  -- Use this to prove the goal.
  intro x hx
  -- View `x` as an element of `e.symm '' B`.
  have hx_image : (x : X) ∈ e.symm '' B := by
    exact ⟨e x, hx, by simp⟩
  -- Apply `P2` for the image.
  have hx_target : x ∈ interior (closure (interior (e.symm '' B))) :=
    hP2_image hx_image
  -- Reinterpret through the set equality `hEq`.
  simpa [hEq] using hx_target

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} (hB : Topology.P3 (A := B)) : Topology.P3 (A := e ⁻¹' B) := by
  -- Identify the preimage with the image under `e.symm`.
  have hEq : (e ⁻¹' B : Set X) = e.symm '' B := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, by simp⟩
    · rintro ⟨y, hyB, rfl⟩
      simpa using hyB
  -- `P3` holds for `e.symm '' B`.
  have hP3_image : Topology.P3 (A := e.symm '' B) :=
    P3_image_homeomorph (e := e.symm) (A := B) hB
  -- Transport the property using the set equality.
  simpa [P3, hEq] using hP3_image