

theorem dense_prod_left_of_nonempty
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hBne : B.Nonempty) :
    Dense (A ×ˢ B) → Dense A := by
  intro hDense
  -- `closure (A ×ˢ B)` is the whole space.
  have h_closure_prod :
      (closure (A ×ˢ B : Set (X × Y))) = (Set.univ : Set (X × Y)) := by
    simpa using hDense.closure_eq
  -- We show `closure A = univ`, which is equivalent to `Dense A`.
  have h_closureA_univ : (closure (A : Set X)) = (Set.univ : Set X) := by
    -- First, the easy inclusion `closure A ⊆ univ`.
    apply Set.Subset.antisymm
    · intro _ _; trivial
    · -- For the reverse inclusion, fix an arbitrary `x : X`.
      intro x _
      -- Pick some `y ∈ B`.
      rcases hBne with ⟨y, hyB⟩
      -- The point `(x, y)` lies in `univ`, hence in `closure (A ×ˢ B)`.
      have h_mem_closure_prod :
          ((x, y) : X × Y) ∈ closure (A ×ˢ B) := by
        have : ((x, y) : X × Y) ∈ (Set.univ : Set (X × Y)) := by
          trivial
        simpa [h_closure_prod] using this
      -- Rewrite `closure (A ×ˢ B)` as a product of closures.
      have h_prod_eq :
          (closure (A ×ˢ B) : Set (X × Y)) =
            closure (A : Set X) ×ˢ closure (B : Set Y) := by
        simpa using closure_prod_eq (s := A) (t := B)
      -- Extract the first coordinate.
      have : ((x, y) : X × Y) ∈ closure A ×ˢ closure B := by
        simpa [h_prod_eq] using h_mem_closure_prod
      exact (Set.mem_prod.1 this).1
  -- Conclude density from the characterisation via closures.
  exact (dense_iff_closure_eq (s := A)).2 h_closureA_univ