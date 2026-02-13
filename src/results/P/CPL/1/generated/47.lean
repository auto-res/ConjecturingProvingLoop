

theorem P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure A = closure (interior A) := by
  simpa [eq_comm] using (P1_iff_dense_inter_interior (A := A))

theorem P1_comap_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} (hB : P1 B) : P1 (e ⁻¹' B) := by
  -- Transport `P1 B` along the inverse homeomorphism `e.symm`.
  have hImage : P1 (e.symm '' B) :=
    P1_image_homeomorph (e := e.symm) (A := B) hB
  -- The image of `B` under `e.symm` coincides with the pre-image of `B` under `e`.
  have h_eq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      simpa using hyB
    · intro hx
      refine ⟨e x, hx, ?_⟩
      simpa using e.symm_apply_apply x
  -- Rewrite the obtained `P1` statement using this equality.
  simpa [h_eq] using hImage

theorem P2_sigma_of_isClosed {X : Type*} [TopologicalSpace X] {ι : Type*} {A : ι → Set X} (hA : ∀ i, IsClosed (A i)) (h : ∀ i, P2 (A i)) : P2 {x : X | ∃ i, x ∈ A i} := by
  -- Use `hA` to avoid an unused-argument warning
  have _ := hA
  -- Obtain `P2` for the union `⋃ i, A i`.
  have hP2_union : P2 (⋃ i, A i) := P2_unionᵢ (A := A) h
  -- Identify the σ–type set with the union.
  have h_eq : ({x : X | ∃ i, x ∈ A i} : Set X) = ⋃ i, A i := by
    ext x
    constructor
    · rintro ⟨i, hx⟩
      exact Set.mem_iUnion.2 ⟨i, hx⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
      exact ⟨i, hx⟩
  -- Transfer the `P2` property along the equality.
  intro x hx
  -- Regard `x` as an element of the union.
  have hx_union : x ∈ ⋃ i, A i := by
    simpa [h_eq] using hx
  -- Apply `P2` for the union.
  have hx_int : x ∈ interior (closure (interior (⋃ i, A i))) :=
    hP2_union hx_union
  -- Rewrite back using the equality.
  simpa [h_eq] using hx_int

theorem P1_pow_two {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : P1 (A ×ˢ A) := by
  simpa using (P1_prod (A := A) (B := A) hA hA)

theorem P1_sUnion_closed {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, IsClosed A ∧ P1 A) : P1 (⋃₀ 𝒜) := by
  exact P1_sUnion (𝒜 := 𝒜) (fun A hA => (h A hA).2)

theorem P3_Union_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior (closure A)) := by
  exact P3_of_isOpen (A := interior (closure (A : Set X))) isOpen_interior

theorem P2_iterate {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior (closure (interior (closure A)))) := by
  exact
    P2_of_isOpen
      (A := interior (closure (interior (closure A))))
      isOpen_interior