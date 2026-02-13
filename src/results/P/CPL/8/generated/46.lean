

theorem P2_image_homeomorph_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (f : X ≃ₜ Y) (g : Y ≃ₜ Z) {A : Set X} : P2 A → P2 ((g ∘ f) '' A) := by
  intro hP2A
  -- First, transport the property along `f`.
  have h1 : P2 (f '' A) :=
    (P2_image_homeomorph (f := f) (A := A)) hP2A
  -- Next, transport the property along `g`.
  have h2 : P2 (g '' (f '' A)) :=
    (P2_image_homeomorph (f := g) (A := f '' A)) h1
  -- Relate the iterated image to the image under the composition.
  have hEq : (g '' (f '' A) : Set Z) = ((g ∘ f) '' A) := by
    ext z
    constructor
    · rintro ⟨y, ⟨x, hxA, rfl⟩, rfl⟩
      exact ⟨x, hxA, rfl⟩
    · rintro ⟨x, hxA, rfl⟩
      exact ⟨f x, ⟨x, hxA, rfl⟩, rfl⟩
  -- Rewrite using the established equality.
  simpa [hEq] using h2

theorem P3_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} : P3 A → P3 B → P3 C → P3 (A ∪ B ∪ C) := by
  intro hA hB hC
  -- Establish `P3` for `A ∪ B`.
  have hAB : P3 (A ∪ B) := P3_union (A := A) (B := B) hA hB
  -- Combine with `C`.
  have hABC : P3 ((A ∪ B) ∪ C) := P3_union (A := A ∪ B) (B := C) hAB hC
  simpa [Set.union_assoc] using hABC