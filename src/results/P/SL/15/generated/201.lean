

theorem dense_prod_univ_left_of_dense
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty Y]
    {A : Set X} :
    Dense (A ×ˢ (Set.univ : Set Y)) → Dense A := by
  intro hDenseProd
  -- We will show that `closure A = univ`, which implies `Dense A`.
  have h_closureA_univ : closure (A : Set X) = (Set.univ : Set X) := by
    -- The closure of the product is `univ`.
    have h_closure_prod_univ :
        closure (A ×ˢ (Set.univ : Set Y) : Set (X × Y)) =
          (Set.univ : Set (X × Y)) := by
      simpa using hDenseProd.closure_eq
    -- The closure of the product can also be written as a product of closures.
    have h_closure_prod :
        closure (A ×ˢ (Set.univ : Set Y) : Set (X × Y)) =
          closure (A : Set X) ×ˢ (Set.univ : Set Y) := by
      simpa [closure_univ] using
        (closure_prod_eq (s := A) (t := (Set.univ : Set Y)))
    -- Hence this product of closures is the whole space.
    have h_prod_eq_univ :
        closure (A : Set X) ×ˢ (Set.univ : Set Y) =
          (Set.univ : Set (X × Y)) :=
      (Eq.symm h_closure_prod).trans h_closure_prod_univ
    -- Prove the reverse inclusion `univ ⊆ closure A`.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
      intro x _
      classical
      let y : Y := Classical.arbitrary Y
      have h_mem_univ : ((x, y) : X × Y) ∈ (Set.univ : Set (X × Y)) := by
        trivial
      have h_mem_prod :
          ((x, y) : X × Y) ∈ closure (A : Set X) ×ˢ (Set.univ : Set Y) := by
        simpa [h_prod_eq_univ] using h_mem_univ
      exact (Set.mem_prod.1 h_mem_prod).1
    -- Assemble the set equality.
    apply Set.Subset.antisymm
    · -- `closure A ⊆ univ`
      intro _ _; trivial
    · exact h_univ_subset
  -- Conclude density from the characterization via closures.
  exact (dense_iff_closure_eq).2 h_closureA_univ