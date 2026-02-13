

theorem dense_prod_closure_of_dense_left_and_dense_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    Dense A → Dense B → Dense (closure A ×ˢ closure B) := by
  intro hA hB
  -- `A` and `B` are dense, so their closures are the whole space.
  have hA_closure : (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa using hA.closure_eq
  have hB_closure : (closure (B : Set Y)) = (Set.univ : Set Y) := by
    simpa using hB.closure_eq
  -- Compute the closure of the product of these closures.
  have hProd :
      closure ((closure A) ×ˢ (closure B) : Set (X × Y)) =
        (Set.univ : Set (X × Y)) := by
    calc
      closure ((closure A) ×ˢ (closure B) : Set (X × Y))
          = closure (closure A) ×ˢ closure (closure B) := by
            simpa using closure_prod_eq (s := closure A) (t := closure B)
      _ = (closure A) ×ˢ (closure B) := by
            simp [closure_closure]
      _ = (Set.univ : Set X) ×ˢ (Set.univ : Set Y) := by
            simpa [hA_closure, hB_closure]
      _ = (Set.univ : Set (X × Y)) := by
            simpa using Set.univ_prod_univ
  -- Conclude density from the characterisation via closures.
  exact (dense_iff_closure_eq (s := closure A ×ˢ closure B)).2 hProd