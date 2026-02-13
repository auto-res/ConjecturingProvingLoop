

theorem P1_prod_implies_P1_left_and_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hProd : Topology.P1 (A ×ˢ B))
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    Topology.P1 A ∧ Topology.P1 B := by
  -- First derive `P1 A`
  have hP1A : Topology.P1 A := by
    dsimp [Topology.P1] at hProd ⊢
    intro x hxA
    -- Choose an element of `B` to form a point in the product.
    rcases hBne with ⟨y, hyB⟩
    have hxy_mem : ((x, y) : X × Y) ∈ A ×ˢ B := ⟨hxA, hyB⟩
    -- Apply `P1` to the product.
    have h_cl_prod : ((x, y) : X × Y) ∈ closure (interior (A ×ˢ B)) :=
      hProd hxy_mem
    -- Rewrite the relevant closures using product rules.
    have h_int_prod :
        interior (A ×ˢ B) = interior A ×ˢ interior B := by
      simpa using interior_prod_eq (s := A) (t := B)
    have h_closure_prod :
        closure (interior (A ×ˢ B)) =
          closure (interior A) ×ˢ closure (interior B) := by
      calc
        closure (interior (A ×ˢ B))
            = closure (interior A ×ˢ interior B) := by
                simpa [h_int_prod]
        _ = closure (interior A) ×ˢ closure (interior B) := by
                simpa using
                  closure_prod_eq (s := interior A) (t := interior B)
    -- Extract the `X`-coordinate.
    have h_mem :
        ((x, y) : X × Y) ∈
          closure (interior A) ×ˢ closure (interior B) := by
      simpa [h_closure_prod] using h_cl_prod
    exact (Set.mem_prod.1 h_mem).1
  -- Next derive `P1 B`
  have hP1B : Topology.P1 B := by
    dsimp [Topology.P1] at hProd ⊢
    intro y hyB
    -- Choose an element of `A` to form a point in the product.
    rcases hAne with ⟨x, hxA⟩
    have hxy_mem : ((x, y) : X × Y) ∈ A ×ˢ B := ⟨hxA, hyB⟩
    -- Apply `P1` to the product.
    have h_cl_prod : ((x, y) : X × Y) ∈ closure (interior (A ×ˢ B)) :=
      hProd hxy_mem
    -- Rewrite closures as above.
    have h_int_prod :
        interior (A ×ˢ B) = interior A ×ˢ interior B := by
      simpa using interior_prod_eq (s := A) (t := B)
    have h_closure_prod :
        closure (interior (A ×ˢ B)) =
          closure (interior A) ×ˢ closure (interior B) := by
      calc
        closure (interior (A ×ˢ B))
            = closure (interior A ×ˢ interior B) := by
                simpa [h_int_prod]
        _ = closure (interior A) ×ˢ closure (interior B) := by
                simpa using
                  closure_prod_eq (s := interior A) (t := interior B)
    -- Extract the `Y`-coordinate.
    have h_mem :
        ((x, y) : X × Y) ∈
          closure (interior A) ×ˢ closure (interior B) := by
      simpa [h_closure_prod] using h_cl_prod
    exact (Set.mem_prod.1 h_mem).2
  exact ⟨hP1A, hP1B⟩