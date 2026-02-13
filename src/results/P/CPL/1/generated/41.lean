

theorem P1_union_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : P1 (A ∪ interior A) := by
  exact P1_union (A := A) (B := interior A) hA (P1_interior (A := A) hA)

theorem P1_prod_swap {X : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (h : P1 (Set.prod A B)) : P1 (Set.prod B A) := by
  -- Define the coordinate-swap homeomorphism.
  let e : X × Y ≃ₜ Y × X := Homeomorph.prodComm (X := X) (Y := Y)
  -- Transport `P1` along `e`.
  have h_image : P1 (e '' (Set.prod A B)) :=
    P1_image_homeomorph (e := e) (A := Set.prod A B) h
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
  -- Re-express `h_image` using the above identification.
  simpa [P1, h_eq] using h_image