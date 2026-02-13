

theorem P1_Union_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {f : X → Y} (hf : Continuous f) (hA : P1 A) : P1 (⋃ y, f ⁻¹' {y}) := by
  -- use the assumptions to avoid unused-variable warnings
  have _ := hf
  have _ := hA
  -- identify the union as the whole space
  have h_eq : (⋃ y, f ⁻¹' ({y} : Set Y)) = (Set.univ : Set X) := by
    ext x
    constructor
    · intro _; simp
    · intro _; exact Set.mem_iUnion.2 ⟨f x, by simp⟩
  simpa [h_eq] using (P1_univ (X := X))

theorem P3_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (h : P3 (Set.prod A B)) : P3 (Set.prod B A) := by
  -- Define the coordinate‐swap homeomorphism.
  let e : X × Y ≃ₜ Y × X := Homeomorph.prodComm (X := X) (Y := Y)
  -- Transport `P3` along `e`.
  have h_image : P3 (e '' (Set.prod A B)) :=
    P3_image_homeomorph (e := e) (A := Set.prod A B) h
  -- Identify the image of `A ×ˢ B` under `e`.
  have h_eq : (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with ⟨a, b⟩
      rcases hq with ⟨ha, hb⟩
      simpa using And.intro hb ha
    · intro hp
      rcases p with ⟨b, a⟩
      rcases hp with ⟨hb, ha⟩
      refine ⟨(a, b), ?_, ?_⟩
      · exact And.intro ha hb
      · simp [e]
  -- Now prove `P3` for `B ×ˢ A`.
  intro p hp
  -- Regard `p` as an element of the image set.
  have hp_image : p ∈ (e '' (Set.prod A B)) := by
    simpa [h_eq] using hp
  -- Apply `P3` for the image.
  have hp_int := h_image hp_image
  -- Rewrite back to the desired set.
  simpa [h_eq] using hp_int

theorem P1_sigma_subtype {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P1 (A i)) : P1 {x : X | ∃ i, x ∈ A i} := by
  -- First, obtain `P1` for the union `⋃ i, A i`.
  have hP1_union : P1 (⋃ i, A i) := P1_Unionᵢ (A := A) h
  -- Identify the σ-type set with the union.
  have h_eq : ({x : X | ∃ i, x ∈ A i} : Set X) = ⋃ i, A i := by
    ext x
    constructor
    · rintro ⟨i, hx⟩
      exact Set.mem_iUnion.2 ⟨i, hx⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
      exact ⟨i, hx⟩
  -- Now establish `P1` for the σ-type set.
  intro x hx
  -- Regard `x` as an element of the union.
  have hx_union : (x : X) ∈ ⋃ i, A i := by
    simpa [h_eq] using hx
  -- Apply `P1` for the union.
  have hx_cl : x ∈ closure (interior (⋃ i, A i)) := hP1_union hx_union
  -- Rewrite using the equality of sets.
  simpa [h_eq] using hx_cl

theorem P2_sUnion_closed {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h𝒜 : ∀ A ∈ 𝒜, IsClosed A ∧ P2 A) : P2 (⋃₀ 𝒜) := by
  exact P2_sUnion (fun A hA => (h𝒜 A hA).2)

theorem P3_dense_inter_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hd : closure (interior A) = (⊤ : Set X)) : P3 A := by
  exact P3_of_P2 (A := A) (P2_of_dense_interior (A := A) hd)

theorem exists_P1_dense_open {X : Type*} [TopologicalSpace X] : ∃ U : Set X, IsOpen U ∧ P1 U ∧ closure U = (⊤ : Set X) := by
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_, ?_⟩
  · exact P1_univ (X := X)
  · simpa [closure_univ]