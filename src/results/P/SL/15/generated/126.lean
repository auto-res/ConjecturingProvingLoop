

theorem P2_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty Y]
    {A : Set X} :
    Topology.P2 (A ×ˢ (Set.univ : Set Y)) → Topology.P2 A := by
  intro hProd
  dsimp [Topology.P2] at hProd ⊢
  intro x hxA
  classical
  -- Choose an arbitrary element of `Y` to form a point in the product.
  let y : Y := Classical.arbitrary Y
  have h_mem_prod : (x, y) ∈ A ×ˢ (Set.univ : Set Y) := by
    exact ⟨hxA, Set.mem_univ y⟩
  -- Apply the `P2` property of the product.
  have h_int_prod :
      (x, y) ∈ interior (closure (interior (A ×ˢ (Set.univ : Set Y)))) :=
    hProd h_mem_prod
  -- Identify `interior (A ×ˢ univ)` with a product of interiors.
  have h_int_prod_eq :
      interior (A ×ˢ (Set.univ : Set Y)) =
        interior A ×ˢ (Set.univ : Set Y) := by
    simpa [interior_univ] using
      interior_prod_eq (s := A) (t := (Set.univ : Set Y))
  -- Identify `closure` of this interior with a product of closures.
  have h_closure_prod :
      closure (interior (A ×ˢ (Set.univ : Set Y))) =
        closure (interior A) ×ˢ (Set.univ : Set Y) := by
    calc
      closure (interior (A ×ˢ (Set.univ : Set Y)))
          = closure (interior A ×ˢ (Set.univ : Set Y)) := by
              simpa [h_int_prod_eq]
      _ = closure (interior A) ×ˢ (Set.univ : Set Y) := by
              simpa [closure_univ] using
                closure_prod_eq
                  (s := interior A) (t := (Set.univ : Set Y))
  -- Rewrite the interior of this closure.
  have h_interior_closure_prod :
      interior (closure (interior (A ×ˢ (Set.univ : Set Y)))) =
        interior (closure (interior A)) ×ˢ (Set.univ : Set Y) := by
    calc
      interior (closure (interior (A ×ˢ (Set.univ : Set Y))))
          = interior ((closure (interior A)) ×ˢ (Set.univ : Set Y)) := by
              simpa [h_closure_prod]
      _ = interior (closure (interior A)) ×ˢ (Set.univ : Set Y) := by
              simpa [interior_univ] using
                interior_prod_eq
                  (s := closure (interior A)) (t := (Set.univ : Set Y))
  -- Transport membership through these identities.
  have h_prod_mem' :
      (x, y) ∈
        interior (closure (interior A)) ×ˢ (Set.univ : Set Y) := by
    simpa [h_interior_closure_prod] using h_int_prod
  -- Extract the `X`-coordinate to conclude.
  exact (Set.mem_prod.1 h_prod_mem').1