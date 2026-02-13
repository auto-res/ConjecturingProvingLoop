

theorem P3_prod_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : (Topology.P3 (Set.prod A B) ↔ Topology.P3 (Set.prod B A)) := by
  -- Define the homeomorphism swapping the factors
  let e := (Homeomorph.prodComm X Y)
  -- Describe the image of `A ×ˢ B`
  have h_image_eq :
      (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with ⟨x, y⟩
      dsimp [e, Homeomorph.prodComm, Set.prod] at hq ⊢
      rcases hq with ⟨hxA, hyB⟩
      exact And.intro hyB hxA
    · intro hp
      rcases p with ⟨y, x⟩
      dsimp [Set.prod] at hp
      rcases hp with ⟨hyB, hxA⟩
      refine ⟨(x, y), ?_, ?_⟩
      · dsimp [Set.prod]
        exact And.intro hxA hyB
      · simp [e, Homeomorph.prodComm]
  -- Describe the preimage of `B ×ˢ A`
  have h_preimage_eq :
      (e ⁻¹' (Set.prod B A) : Set (X × Y)) = Set.prod A B := by
    ext p
    constructor
    · intro hp
      dsimp [Set.preimage] at hp
      dsimp [e, Homeomorph.prodComm, Set.prod] at hp
      exact And.intro hp.2 hp.1
    · intro hp
      dsimp [Set.preimage]
      dsimp [e, Homeomorph.prodComm, Set.prod]
      exact And.intro hp.2 hp.1
  -- Forward implication
  have forward :
      Topology.P3 (Set.prod A B) → Topology.P3 (Set.prod B A) := by
    intro h
    have h' : Topology.P3 (e '' Set.prod A B) :=
      Topology.P3_image_homeomorph (e := e) (A := Set.prod A B) h
    simpa [h_image_eq] using h'
  -- Backward implication
  have backward :
      Topology.P3 (Set.prod B A) → Topology.P3 (Set.prod A B) := by
    intro h
    have h' : Topology.P3 (e ⁻¹' Set.prod B A) :=
      Topology.P3_preimage_homeomorph (e := e) (B := Set.prod B A) h
    simpa [h_preimage_eq] using h'
  exact ⟨forward, backward⟩