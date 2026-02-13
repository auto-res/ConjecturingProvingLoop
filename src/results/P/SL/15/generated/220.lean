

theorem closure_prod_eq_univ_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] [Nonempty Y]
    {A : Set X} {B : Set Y} :
    closure (A ×ˢ B) = (Set.univ : Set (X × Y)) ↔
      (closure (A : Set X) = (Set.univ : Set X)) ∧
        (closure (B : Set Y) = (Set.univ : Set Y)) := by
  classical
  -- Express the closure of a product as a product of closures.
  have hProd :
      closure (A ×ˢ B) =
        (closure (A : Set X)) ×ˢ (closure (B : Set Y)) := by
    simpa using closure_prod_eq (s := A) (t := B)
  constructor
  · intro hUniv
    -- From `hUniv`, deduce that the product of closures is `univ`.
    have hProdUniv :
        (closure (A : Set X)) ×ˢ (closure (B : Set Y)) =
          (Set.univ : Set (X × Y)) := by
      simpa [hProd] using hUniv
    -- Prove `closure A = univ`.
    have hA_univ : closure (A : Set X) = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro _ _; trivial
      · intro x _
        -- Choose an arbitrary `y : Y`.
        let y : Y := Classical.arbitrary Y
        have : ((x, y) : X × Y) ∈
            (closure (A : Set X)) ×ˢ (closure (B : Set Y)) := by
          have : ((x, y) : X × Y) ∈ (Set.univ : Set (X × Y)) := by
            trivial
          simpa [hProdUniv] using this
        exact (Set.mem_prod.1 this).1
    -- Prove `closure B = univ`.
    have hB_univ : closure (B : Set Y) = (Set.univ : Set Y) := by
      apply Set.Subset.antisymm
      · intro _ _; trivial
      · intro y _
        -- Choose an arbitrary `x : X`.
        let x : X := Classical.arbitrary X
        have : ((x, y) : X × Y) ∈
            (closure (A : Set X)) ×ˢ (closure (B : Set Y)) := by
          have : ((x, y) : X × Y) ∈ (Set.univ : Set (X × Y)) := by
            trivial
          simpa [hProdUniv] using this
        exact (Set.mem_prod.1 this).2
    exact ⟨hA_univ, hB_univ⟩
  · rintro ⟨hA_univ, hB_univ⟩
    -- The product of `univ` sets is `univ`.
    have hProdEqUniv :
        (closure (A : Set X)) ×ˢ (closure (B : Set Y)) =
          (Set.univ : Set (X × Y)) := by
      simpa [hA_univ, hB_univ, Set.univ_prod_univ]
    -- Rewrite back to the closure of the product.
    simpa [hProd] using hProdEqUniv