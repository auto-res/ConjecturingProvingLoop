

theorem dense_prod_univ_right_of_dense
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    {B : Set Y} :
    Dense ((Set.univ : Set X) ×ˢ B) → Dense B := by
  intro hDenseProd
  -- We show that `closure B = univ`, from which density follows.
  have h_closureB_univ : (closure (B : Set Y)) = (Set.univ : Set Y) := by
    -- First, the easy inclusion `closure B ⊆ univ`.
    have h₁ : (closure (B : Set Y)) ⊆ (Set.univ : Set Y) := by
      intro y _; trivial
    -- For the reverse inclusion, fix an arbitrary `y : Y`.
    have h₂ : (Set.univ : Set Y) ⊆ closure B := by
      intro y _hy
      classical
      -- Pick an arbitrary `x : X`.
      let x : X := Classical.arbitrary X
      -- The point `(x, y)` belongs to `univ`.
      have h_mem_univ : ((x, y) : X × Y) ∈ (Set.univ : Set (X × Y)) := by
        trivial
      -- Since the product set is dense, its closure is `univ`.
      have h_closure_prod_univ :
          closure ((Set.univ : Set X) ×ˢ B : Set (X × Y)) =
            (Set.univ : Set (X × Y)) := by
        simpa using hDenseProd.closure_eq
      -- The closure of the product can also be written as a product of closures.
      have h_closure_prod :
          closure ((Set.univ : Set X) ×ˢ B : Set (X × Y)) =
            (Set.univ : Set X) ×ˢ closure (B : Set Y) := by
        simpa [closure_univ] using
          closure_prod_eq (s := (Set.univ : Set X)) (t := B)
      -- Transport the membership of `(x, y)` through these equalities.
      have h_mem_prod_closure :
          ((x, y) : X × Y) ∈ (Set.univ : Set X) ×ˢ closure (B : Set Y) := by
        -- `(x, y)` lies in the closure of the product...
        have h_in_closure :
            ((x, y) : X × Y) ∈
              closure ((Set.univ : Set X) ×ˢ B : Set (X × Y)) := by
          simpa [h_closure_prod_univ] using h_mem_univ
        -- ...and hence in the product of the closures.
        simpa [h_closure_prod] using h_in_closure
      -- Extract the `Y`–component to obtain `y ∈ closure B`.
      exact (Set.mem_prod.1 h_mem_prod_closure).2
    -- Assemble the equality of sets.
    exact Set.Subset.antisymm h₁ h₂
  -- Conclude density from the characterization via closures.
  exact (dense_iff_closure_eq).2 h_closureB_univ