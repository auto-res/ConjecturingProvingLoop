

theorem P2_interior_subset {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 A) : interior A ⊆ interior (closure (interior A)) := by
  dsimp [Topology.P2] at h
  exact fun x hx => h (interior_subset hx)

theorem P1_of_open_surrounds {X : Type*} [TopologicalSpace X] {A : Set X} (h : ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure (interior A)) : Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hxA
  rcases h x hxA with ⟨U, _hUopen, hxU, hU_subset⟩
  exact hU_subset hxU

theorem P2_prod_symmetric {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P2 (Set.prod A B) ↔ Topology.P2 (Set.prod B A) := by
  -- Let `e` be the swapping homeomorphism `(x, y) ↦ (y, x)`.
  let e := Homeomorph.prodComm X Y
  -- The image of `A × B` under `e` is `B × A`.
  have h_img :
      (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hA, hB⟩
      exact And.intro hB hA
    · rintro hp
      rcases p with ⟨b, a⟩
      rcases hp with ⟨hB, hA⟩
      refine ⟨(a, b), ?_, ?_⟩
      · exact And.intro hA hB
      · rfl
  -- The image of `B × A` under the inverse map is `A × B`.
  have h_img_symm :
      (e.symm '' (Set.prod B A) : Set (X × Y)) = Set.prod A B := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hB, hA⟩
      exact And.intro hA hB
    · rintro hp
      rcases p with ⟨a, b⟩
      rcases hp with ⟨hA, hB⟩
      refine ⟨(b, a), ?_, ?_⟩
      · exact And.intro hB hA
      · rfl
  -- Use the two transport lemmas for `P2`.
  constructor
  · intro hP2
    -- Transport through `e`.
    have h :=
      P2_image_homeomorph
        (e := e)
        (A := Set.prod A B)
        hP2
    simpa [h_img] using h
  · intro hP2
    -- Transport back through `e.symm`.
    have h :=
      P2_image_homeomorph
        (e := e.symm)
        (A := Set.prod B A)
        hP2
    simpa [h_img_symm] using h

theorem P1_closure_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, Topology.P1 A) : Topology.P1 (closure (⋃₀ 𝒜)) := by
  have hP1_union : Topology.P1 (⋃₀ 𝒜) :=
    P1_sUnion_family (X := X) (𝒜 := 𝒜) h
  simpa using
    (P1_closure (X := X) (A := ⋃₀ 𝒜) hP1_union)

theorem P2_closed_complement' {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P2 (Aᶜ) := by
  have hOpen : IsOpen (Aᶜ : Set X) := hA.isOpen_compl
  simpa using (openSet_P2 (X := X) (A := Aᶜ) hOpen)

theorem P3_interior_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P3 (Set.prod (interior A) (interior B)) := by
  -- First, observe that the product of two open sets is open.
  have hOpen : IsOpen (Set.prod (interior A) (interior B)) := by
    exact
      (isOpen_interior : IsOpen (interior A)).prod
        (isOpen_interior : IsOpen (interior B))
  -- Apply the `P3` lemma for open sets in the ambient space `X × Y`.
  simpa using
    (openSet_P3 (X := X × Y)
      (A := Set.prod (interior A) (interior B)) hOpen)

theorem P2_exists_basis {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → ∃ 𝔅 : Set (Set X), (∀ U ∈ 𝔅, IsOpen U) ∧ A ⊆ ⋃₀ 𝔅 ∧ ⋃₀ 𝔅 ⊆ interior (closure (interior A)) := by
  intro hP2
  refine ⟨{interior (closure (interior A))}, ?_, ?_, ?_⟩
  · intro U hU
    have hUeq : U = interior (closure (interior A)) := by
      simpa [Set.mem_singleton_iff] using hU
    simpa [hUeq] using isOpen_interior
  · simpa [Set.sUnion_singleton] using hP2
  ·
    simpa [Set.sUnion_singleton] using
      (subset_rfl :
        (interior (closure (interior A)) : Set X) ⊆
          interior (closure (interior A)))