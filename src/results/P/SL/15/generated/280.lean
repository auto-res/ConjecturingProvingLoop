

theorem dense_prod_left_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hDenseB : Dense B) :
    Dense (A ×ˢ B) ↔ Dense A := by
  -- Start from the general equivalence for products of arbitrary sets.
  have hProd :=
    (dense_prod_iff
        (X := X) (Y := Y) (A := A) (B := B) hAne hBne)
  -- Under the extra hypothesis `Dense B`, the right‐hand side simplifies.
  have hAux : (Dense A ∧ Dense B) ↔ Dense A := by
    constructor
    · intro h; exact h.1
    · intro hA; exact And.intro hA hDenseB
  exact hProd.trans hAux