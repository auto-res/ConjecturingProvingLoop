

theorem P3_prod_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    {B : Set Y} :
    Topology.P3 ((Set.univ : Set X) ×ˢ B) → Topology.P3 B := by
  intro hProd
  dsimp [Topology.P3] at hProd
  dsimp [Topology.P3]
  intro y hyB
  classical
  -- pick an arbitrary element of `X`
  have x : X := Classical.arbitrary X
  -- the point `(x, y)` lies in the product set
  have h_mem_prod : ((x, y) : X × Y) ∈ (Set.univ : Set X) ×ˢ B := by
    exact And.intro (by trivial) hyB
  -- apply the `P3` property of the product
  have h_int_prod :
      ((x, y) : X × Y) ∈ interior (closure ((Set.univ : Set X) ×ˢ B)) :=
    hProd h_mem_prod
  -- identify the closure of the product
  have h_closure_prod :
      closure ((Set.univ : Set X) ×ˢ B) =
        (Set.univ : Set X) ×ˢ closure B := by
    simpa [closure_univ] using
      closure_prod_eq (s := (Set.univ : Set X)) (t := B)
  -- rewrite membership using the equality above
  have h_int_prod' :
      ((x, y) : X × Y) ∈ interior ((Set.univ : Set X) ×ˢ closure B) := by
    simpa [h_closure_prod] using h_int_prod
  -- identify the interior of the product
  have h_int_eq :
      interior ((Set.univ : Set X) ×ˢ closure B) =
        (Set.univ : Set X) ×ˢ interior (closure B) := by
    simpa [interior_univ] using
      interior_prod_eq (s := (Set.univ : Set X)) (t := closure B)
  -- transport membership through this last equality
  have h_final :
      ((x, y) : X × Y) ∈ (Set.univ : Set X) ×ˢ interior (closure B) := by
    simpa [h_int_eq] using h_int_prod'
  -- extract the `Y`-coordinate
  exact (Set.mem_prod.1 h_final).2