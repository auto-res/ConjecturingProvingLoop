

theorem P2_compl_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P2 (Aᶜ) := by
  intro hClosed
  simpa using P2_of_open (A := Aᶜ) hClosed.isOpen_compl

theorem P1_prod_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 (Set.prod A B) → P1 (Set.prod B A) := by
  intro hP1
  -- Transport `P1` through the coordinate‐swap homeomorphism.
  have hImage :
      P1
        ((fun a : X × Y => Prod.swap a) '' (Set.prod A B) : Set (Y × X)) := by
    simpa using
      (P1_image_homeomorph (f := Homeomorph.prodComm X Y) hP1)
  -- The image of `A × B` under the swap map is `B × A`.
  have hImageEq :
      ((fun a : X × Y => Prod.swap a) '' (Set.prod A B) : Set (Y × X)) =
        Set.prod B A := by
    ext p
    constructor
    · -- forward direction
      rintro ⟨q, ⟨hqA, hqB⟩, rfl⟩
      exact ⟨hqB, hqA⟩
    · -- reverse direction
      rintro ⟨hpB, hpA⟩
      refine ⟨Prod.swap p, ?_, ?_⟩
      · exact ⟨hpA, hpB⟩
      ·
        cases p with
        | mk y x =>
            simp [Prod.swap]        -- evaluates the swap
  -- Reinterpret `hImage` via the identified equality.
  simpa [hImageEq] using hImage