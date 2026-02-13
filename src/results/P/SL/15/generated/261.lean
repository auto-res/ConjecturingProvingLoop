

theorem dense_prod_right_of_nonempty
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hAne : A.Nonempty) :
    Dense (A ×ˢ B) → Dense B := by
  intro hDenseProd
  -- `closure (A ×ˢ B)` is the whole space.
  have h_closure_prod :
      closure (A ×ˢ B : Set (X × Y)) = (Set.univ : Set (X × Y)) := by
    simpa using hDenseProd.closure_eq
  -- Express this closure as a product of closures.
  have h_prod_closure :
      closure (A ×ˢ B : Set (X × Y)) =
        (closure (A : Set X)) ×ˢ closure (B : Set Y) := by
    simpa using closure_prod_eq (s := A) (t := B)
  -- We prove `closure B = univ`, which implies `Dense B`.
  have h_closureB_univ : closure (B : Set Y) = (Set.univ : Set Y) := by
    -- First, the trivial inclusion.
    apply Set.Subset.antisymm
    · intro _ _; trivial
    · intro y _
      -- Choose an arbitrary `x ∈ A`.
      rcases hAne with ⟨x, hxA⟩
      -- The point `(x, y)` lies in `univ`, hence in `closure (A ×ˢ B)`.
      have h_mem_closure_prod :
          ((x, y) : X × Y) ∈ closure (A ×ˢ B) := by
        have : ((x, y) : X × Y) ∈ (Set.univ : Set (X × Y)) := by
          trivial
        simpa [h_closure_prod] using this
      -- Transport this membership through `h_prod_closure`.
      have h_mem_prod_closures :
          ((x, y) : X × Y) ∈
            (closure (A : Set X)) ×ˢ closure (B : Set Y) := by
        simpa [h_prod_closure] using h_mem_closure_prod
      -- Extract the `Y`-component.
      exact (Set.mem_prod.1 h_mem_prod_closures).2
  -- Conclude density via the characterisation using closures.
  exact (dense_iff_closure_eq (s := B)).2 h_closureB_univ