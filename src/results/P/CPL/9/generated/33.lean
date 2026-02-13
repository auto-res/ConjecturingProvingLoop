

theorem P2_directed_Union {X : Type*} [TopologicalSpace X] {ι : Type*} (s : ι → Set X) (hmono : ∀ i j, s i ⊆ s j ∨ s j ⊆ s i) (h : ∀ i, Topology.P2 (A := s i)) : Topology.P2 (A := ⋃ i, s i) := by
  simpa using (P2_iUnion (s := s) (h := h))

theorem P1_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P1 (A := Set.prod A B) ↔ Topology.P1 (A := Set.prod B A) := by
  classical
  -- The homeomorphism swapping the coordinates.
  let e : X × Y ≃ₜ Y × X := Homeomorph.prodComm X Y
  ----------------------------------------------------------------
  -- 1.  The image of `A × B` under `e` is `B × A`.
  ----------------------------------------------------------------
  have h_image :
      (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with ⟨x, y⟩
      rcases hq with ⟨hxA, hyB⟩
      simpa [e, Homeomorph.prodComm, Set.prod] using And.intro hyB hxA
    · intro hp
      rcases p with ⟨y, x⟩
      rcases (by
        simpa [Set.prod] using hp : y ∈ B ∧ x ∈ A) with ⟨hyB, hxA⟩
      have hq : ((x, y) : X × Y) ∈ Set.prod A B := by
        simpa [Set.prod] using And.intro hxA hyB
      have : (y, x) ∈ (e '' Set.prod A B : Set (Y × X)) := by
        refine ⟨(x, y), hq, ?_⟩
        simp [e, Homeomorph.prodComm]
      simpa using this
  ----------------------------------------------------------------
  -- 2.  The image of `B × A` under `e.symm` is `A × B`.
  ----------------------------------------------------------------
  have h_image_symm :
      (e.symm '' (Set.prod B A) : Set (X × Y)) = Set.prod A B := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with ⟨y, x⟩
      rcases hq with ⟨hyB, hxA⟩
      simpa [e, Homeomorph.prodComm, Set.prod] using And.intro hxA hyB
    · intro hp
      rcases p with ⟨x, y⟩
      rcases (by
        simpa [Set.prod] using hp : x ∈ A ∧ y ∈ B) with ⟨hxA, hyB⟩
      have hq : ((y, x) : Y × X) ∈ Set.prod B A := by
        simpa [Set.prod] using And.intro hyB hxA
      have : (x, y) ∈ (e.symm '' Set.prod B A : Set (X × Y)) := by
        refine ⟨(y, x), hq, ?_⟩
        simp [e, Homeomorph.prodComm]
      simpa using this
  ----------------------------------------------------------------
  -- 3.  Transport the `P1` property along the homeomorphism.
  ----------------------------------------------------------------
  refine ⟨?_, ?_⟩
  · intro hP1
    have hImage : Topology.P1 (A := e '' Set.prod A B) :=
      P1_image_homeomorph (e := e) (A := Set.prod A B) hP1
    simpa [h_image] using hImage
  · intro hP1
    have hImage : Topology.P1 (A := e.symm '' Set.prod B A) :=
      P1_image_homeomorph (e := e.symm) (A := Set.prod B A) hP1
    simpa [h_image_symm] using hImage