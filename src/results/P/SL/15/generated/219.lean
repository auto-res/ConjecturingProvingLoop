

theorem interior_closure_prod_eq_univ_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] [Nonempty Y] {A : Set X} {B : Set Y} :
    interior (closure (A ×ˢ B)) = (Set.univ : Set (X × Y)) ↔
      (interior (closure A) = (Set.univ : Set X)) ∧
        (interior (closure B) = (Set.univ : Set Y)) := by
  -- A convenient equality relating the two sides.
  have hProd :
      interior (closure (A ×ˢ B)) =
        interior (closure A) ×ˢ interior (closure B) :=
    interior_closure_prod (X := X) (Y := Y) (A := A) (B := B)
  constructor
  · intro hUniv
    -- First, show `interior (closure A) = univ`.
    have hA_sub : (Set.univ : Set X) ⊆ interior (closure A) := by
      intro x _
      classical
      let y : Y := Classical.arbitrary Y
      have hxy_in :
          ((x, y) : X × Y) ∈ interior (closure (A ×ˢ B)) := by
        -- This follows from `hUniv`.
        have : ((x, y) : X × Y) ∈ (Set.univ : Set (X × Y)) := by
          trivial
        simpa [hUniv] using this
      have hxy_prod :
          ((x, y) : X × Y) ∈
            interior (closure A) ×ˢ interior (closure B) := by
        simpa [hProd] using hxy_in
      exact (Set.mem_prod.1 hxy_prod).1
    have hIntA_eq :
        interior (closure A) = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro _ _; trivial
      · exact hA_sub
    -- Next, show `interior (closure B) = univ`.
    have hB_sub : (Set.univ : Set Y) ⊆ interior (closure B) := by
      intro y _
      classical
      let x : X := Classical.arbitrary X
      have hxy_in :
          ((x, y) : X × Y) ∈ interior (closure (A ×ˢ B)) := by
        have : ((x, y) : X × Y) ∈ (Set.univ : Set (X × Y)) := by
          trivial
        simpa [hUniv] using this
      have hxy_prod :
          ((x, y) : X × Y) ∈
            interior (closure A) ×ˢ interior (closure B) := by
        simpa [hProd] using hxy_in
      exact (Set.mem_prod.1 hxy_prod).2
    have hIntB_eq :
        interior (closure B) = (Set.univ : Set Y) := by
      apply Set.Subset.antisymm
      · intro _ _; trivial
      · exact hB_sub
    exact ⟨hIntA_eq, hIntB_eq⟩
  · rintro ⟨hA, hB⟩
    -- Use `hProd` together with the two equalities.
    calc
      interior (closure (A ×ˢ B))
          = interior (closure A) ×ˢ interior (closure B) := hProd
      _ = (Set.univ : Set X) ×ˢ (Set.univ : Set Y) := by
          simpa [hA, hB]
      _ = (Set.univ : Set (X × Y)) := by
          simpa using
            (Set.univ_prod_univ : ((Set.univ : Set X) ×ˢ (Set.univ : Set Y)) =
              (Set.univ : Set (X × Y)))