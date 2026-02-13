

theorem P2_closed_complement' {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Topology.P2 Aᶜ := by
  intro hClosed
  exact P2_of_open hClosed.isOpen_compl

theorem P2_prod_symm {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P2 (A ×ˢ B) → Topology.P2 (B ×ˢ A) := by
  intro hP2
  ----------------------------------------------------------------
  -- 1.  The homeomorphism swapping the two coordinates.
  ----------------------------------------------------------------
  let hComm : (X × Y) ≃ₜ (Y × X) := Homeomorph.prodComm X Y
  ----------------------------------------------------------------
  -- 2.  Transport `P2` through this homeomorphism.
  ----------------------------------------------------------------
  have hP2_image :
      Topology.P2 ((hComm) '' (A ×ˢ B : Set (X × Y))) :=
    P2_image_of_homeomorph (A := A ×ˢ B) (h := hComm) hP2
  ----------------------------------------------------------------
  -- 3.  Identify the image `hComm '' (A ×ˢ B)` with `B ×ˢ A`.
  ----------------------------------------------------------------
  have hImage :
      ((hComm) '' (A ×ˢ B : Set (X × Y)) : Set (Y × X)) = B ×ˢ A := by
    ext p
    constructor
    · -- `p` comes from the image
      rintro ⟨q, hqAB, rfl⟩
      rcases q with ⟨x, y⟩
      rcases hqAB with ⟨hxA, hyB⟩
      -- After swapping we get `(y, x)`
      -- Show this belongs to `B ×ˢ A`
      simpa [hComm, Homeomorph.prodComm, Set.mem_prod] using
        And.intro hyB hxA
    · -- Start with a point in `B ×ˢ A`
      intro hp
      rcases p with ⟨y, x⟩
      have hp' : y ∈ B ∧ x ∈ A := by
        simpa [Set.mem_prod] using hp
      -- Pre-image point `(x, y)` lies in `A ×ˢ B`
      have hqAB : (x, y) ∈ (A ×ˢ B : Set (X × Y)) := by
        simpa [Set.mem_prod] using And.intro hp'.2 hp'.1
      -- Its image under `hComm` is `(y, x)`
      have : (y, x) ∈ ((hComm) '' (A ×ˢ B : Set (X × Y))) := by
        refine ⟨(x, y), hqAB, ?_⟩
        simp [hComm, Homeomorph.prodComm]
      simpa using this
  ----------------------------------------------------------------
  -- 4.  Rewrite with the computed image and conclude.
  ----------------------------------------------------------------
  simpa [hImage] using hP2_image