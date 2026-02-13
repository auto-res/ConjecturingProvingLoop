

theorem P2_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : (Topology.P2 (A.prod B)) ↔ Topology.P2 (B.prod A) := by
  constructor
  · intro h
    -- transport `P2` through the coordinate‐swap homeomorphism
    have h_image :
        Topology.P2
          ((fun p : X × Y => Prod.swap p) '' (A.prod B) : Set (Y × X)) := by
      simpa using
        (P2_image_homeomorph
            (e := Homeomorph.prodComm (X := X) (Y := Y))
            (A := A.prod B)
            h)
    -- identify this image with `B × A`
    have h_eq :
        ((fun p : X × Y => Prod.swap p) '' (A.prod B) : Set (Y × X)) =
          B.prod A := by
      ext p
      constructor
      · rintro ⟨⟨x, y⟩, hxy, rfl⟩
        rcases hxy with ⟨hxA, hyB⟩
        exact And.intro hyB hxA
      · intro hp
        rcases p with ⟨y, x⟩
        rcases hp with ⟨hyB, hxA⟩
        refine ⟨(x, y), ?_, rfl⟩
        exact And.intro hxA hyB
    simpa [h_eq] using h_image
  · intro h
    -- transport `P2` in the opposite direction
    have h_image :
        Topology.P2
          ((fun p : Y × X => Prod.swap p) '' (B.prod A) : Set (X × Y)) := by
      simpa using
        (P2_image_homeomorph
            (e := Homeomorph.prodComm (X := Y) (Y := X))
            (A := B.prod A)
            h)
    -- identify this image with `A × B`
    have h_eq :
        ((fun p : Y × X => Prod.swap p) '' (B.prod A) : Set (X × Y)) =
          A.prod B := by
      ext p
      constructor
      · rintro ⟨⟨y, x⟩, hxy, rfl⟩
        rcases hxy with ⟨hyB, hxA⟩
        exact And.intro hxA hyB
      · intro hp
        rcases p with ⟨x, y⟩
        rcases hp with ⟨hxA, hyB⟩
        refine ⟨(y, x), ?_, rfl⟩
        exact And.intro hyB hxA
    simpa [h_eq] using h_image

theorem exists_P2_compact_subset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ K : Set X, IsCompact K ∧ K ⊆ A ∧ Topology.P2 K := by
  refine ⟨(∅ : Set X), isCompact_empty, ?_, ?_⟩
  · exact Set.empty_subset _
  · simpa using (P2_empty (X := X))

theorem P1_closure_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 ((closure A).prod (closure B)) := by
  -- Upgrade the hypotheses to the closures.
  have hA_cl : Topology.P1 (closure (A : Set X)) :=
    P1_closure (X := X) (A := A) hA
  have hB_cl : Topology.P1 (closure (B : Set Y)) :=
    P1_closure (X := Y) (A := B) hB
  -- Apply the product lemma.
  simpa using
    (P1_prod (X := X) (Y := Y)
      (A := closure (A : Set X)) (B := closure (B : Set Y)) hA_cl hB_cl)