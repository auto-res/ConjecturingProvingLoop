

theorem P3_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty Y]
    {A : Set X} :
    Topology.P3 (A ×ˢ (Set.univ : Set Y)) → Topology.P3 A := by
  intro hProd
  dsimp [Topology.P3] at hProd
  dsimp [Topology.P3]
  intro x hxA
  classical
  -- Choose an arbitrary element of `Y` to build a point in the product.
  let y : Y := Classical.arbitrary Y
  have h_mem_prod : (x, y) ∈ A ×ˢ (Set.univ : Set Y) := by
    exact ⟨hxA, Set.mem_univ y⟩
  -- Apply the `P3` property of the product.
  have h_int_prod : (x, y) ∈ interior (closure (A ×ˢ (Set.univ : Set Y))) :=
    hProd h_mem_prod
  -- Identify the closure of the product with a product of closures.
  have h_closure_prod :
      closure (A ×ˢ (Set.univ : Set Y)) = (closure A) ×ˢ (Set.univ : Set Y) := by
    simpa using closure_prod_eq (s := A) (t := (Set.univ : Set Y))
  -- Rewrite the interior of this product.
  have h_int_prod_eq :
      interior ((closure A) ×ˢ (Set.univ : Set Y)) =
        interior (closure A) ×ˢ (Set.univ : Set Y) := by
    simpa using interior_prod_eq (s := closure A) (t := (Set.univ : Set Y))
  -- Transport membership through these equalities.
  have h_int_prod' : (x, y) ∈ interior ((closure A) ×ˢ (Set.univ : Set Y)) := by
    simpa [h_closure_prod] using h_int_prod
  have h_int_prod'' : (x, y) ∈ interior (closure A) ×ˢ (Set.univ : Set Y) := by
    simpa [h_int_prod_eq] using h_int_prod'
  -- Conclude the desired membership for `x`.
  exact (Set.mem_prod.1 h_int_prod'').1