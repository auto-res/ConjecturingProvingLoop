

theorem P2_prod_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    {B : Set Y} :
    Topology.P2 ((Set.univ : Set X) ×ˢ B) → Topology.P2 B := by
  intro hProd
  dsimp [Topology.P2] at hProd ⊢
  intro y hyB
  classical
  -- Choose an arbitrary element of `X` to form a point in the product.
  have x : X := Classical.arbitrary X
  have h_mem_prod : ((x, y) : X × Y) ∈ (Set.univ : Set X) ×ˢ B :=
    by exact And.intro (by trivial) hyB
  -- Apply the `P2` property of the product set.
  have h_int_prod :
      ((x, y) : X × Y) ∈ interior (closure (interior ((Set.univ : Set X) ×ˢ B))) :=
    hProd h_mem_prod
  -- Identify `interior ((univ) ×ˢ B)` with a product of interiors.
  have h_int_eq :
      interior ((Set.univ : Set X) ×ˢ B) =
        (Set.univ : Set X) ×ˢ interior B := by
    simpa [interior_univ] using
      interior_prod_eq (s := (Set.univ : Set X)) (t := B)
  -- Identify the closure of this interior with a product of closures.
  have h_closure_eq :
      closure (interior ((Set.univ : Set X) ×ˢ B)) =
        (Set.univ : Set X) ×ˢ closure (interior B) := by
    have :
        closure ((Set.univ : Set X) ×ˢ interior B) =
          closure (Set.univ : Set X) ×ˢ closure (interior B) := by
      simpa using
        closure_prod_eq (s := (Set.univ : Set X)) (t := interior B)
    simpa [h_int_eq, closure_univ] using this
  -- Rewrite the interior of this closure.
  have h_interior_closure_eq :
      interior (closure (interior ((Set.univ : Set X) ×ˢ B))) =
        (Set.univ : Set X) ×ˢ interior (closure (interior B)) := by
    have :
        interior ((Set.univ : Set X) ×ˢ closure (interior B)) =
          (Set.univ : Set X) ×ˢ interior (closure (interior B)) := by
      simpa [interior_univ] using
        interior_prod_eq (s := (Set.univ : Set X)) (t := closure (interior B))
    simpa [h_closure_eq] using this
  -- Transport membership through these identities.
  have h_mem_prod_int :
      ((x, y) : X × Y) ∈
        (Set.univ : Set X) ×ˢ interior (closure (interior B)) := by
    simpa [h_interior_closure_eq] using h_int_prod
  -- Extract the `Y`-coordinate to conclude.
  exact (Set.mem_prod.1 h_mem_prod_int).2