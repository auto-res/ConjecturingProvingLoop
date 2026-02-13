

theorem dense_prod_right_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hAne : A.Nonempty) (hBne : B.Nonempty) (hDenseA : Dense A) :
    Dense (A ×ˢ B) ↔ Dense B := by
  -- Start with the general equivalence for products.
  have h₁ :=
    (dense_prod_iff
      (X := X) (Y := Y) (A := A) (B := B) hAne hBne)
  -- Under the extra hypothesis `Dense A`, the right‐hand side simplifies.
  have h₂ : (Dense A ∧ Dense B) ↔ Dense B := by
    constructor
    · intro h; exact h.2
    · intro hB; exact And.intro hDenseA hB
  -- Combine the two equivalences.
  exact h₁.trans h₂