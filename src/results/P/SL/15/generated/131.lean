

theorem P2_prod_implies_P2_left_and_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hProd : Topology.P2 (A ×ˢ B))
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    Topology.P2 A ∧ Topology.P2 B := by
  -- First, derive `P2 A`.
  have hP2A : Topology.P2 A := by
    dsimp [Topology.P2] at hProd ⊢
    intro x hxA
    -- Choose a witness in `B` to build a point in the product.
    rcases hBne with ⟨y, hyB⟩
    have h_mem_prod : ((x, y) : X × Y) ∈ A ×ˢ B := ⟨hxA, hyB⟩
    -- Apply the `P2` property to the product.
    have h_int_prod : ((x, y) : X × Y) ∈
        interior (closure (interior (A ×ˢ B))) := hProd h_mem_prod
    -- Rewrite the relevant interiors and closures.
    have h_int_prod_eq :
        interior (A ×ˢ B) = interior A ×ˢ interior B := by
      simpa using interior_prod_eq (s := A) (t := B)
    have h_closure_prod :
        closure (interior (A ×ˢ B)) =
          closure (interior A) ×ˢ closure (interior B) := by
      calc
        closure (interior (A ×ˢ B))
            = closure (interior A ×ˢ interior B) := by
                simpa [h_int_prod_eq]
        _ = closure (interior A) ×ˢ closure (interior B) := by
                simpa using
                  closure_prod_eq (s := interior A) (t := interior B)
    have h_interior_closure_prod :
        interior (closure (interior (A ×ˢ B))) =
          interior (closure (interior A)) ×ˢ
            interior (closure (interior B)) := by
      calc
        interior (closure (interior (A ×ˢ B)))
            = interior ((closure (interior A)) ×ˢ (closure (interior B))) := by
                simpa [h_closure_prod]
        _ = interior (closure (interior A)) ×ˢ
            interior (closure (interior B)) := by
                simpa using
                  interior_prod_eq
                    (s := closure (interior A))
                    (t := closure (interior B))
    -- Extract the `X`-coordinate from the membership.
    have h_mem :
        ((x, y) : X × Y) ∈
          interior (closure (interior A)) ×ˢ
            interior (closure (interior B)) := by
      simpa [h_interior_closure_prod] using h_int_prod
    exact (Set.mem_prod.1 h_mem).1
  -- Next, derive `P2 B`.
  have hP2B : Topology.P2 B := by
    dsimp [Topology.P2] at hProd ⊢
    intro y hyB
    -- Choose a witness in `A` to build a point in the product.
    rcases hAne with ⟨x, hxA⟩
    have h_mem_prod : ((x, y) : X × Y) ∈ A ×ˢ B := ⟨hxA, hyB⟩
    -- Apply the `P2` property to the product.
    have h_int_prod : ((x, y) : X × Y) ∈
        interior (closure (interior (A ×ˢ B))) := hProd h_mem_prod
    -- Reuse the computations above (they remain valid).
    have h_int_prod_eq :
        interior (A ×ˢ B) = interior A ×ˢ interior B := by
      simpa using interior_prod_eq (s := A) (t := B)
    have h_closure_prod :
        closure (interior (A ×ˢ B)) =
          closure (interior A) ×ˢ closure (interior B) := by
      calc
        closure (interior (A ×ˢ B))
            = closure (interior A ×ˢ interior B) := by
                simpa [h_int_prod_eq]
        _ = closure (interior A) ×ˢ closure (interior B) := by
                simpa using
                  closure_prod_eq (s := interior A) (t := interior B)
    have h_interior_closure_prod :
        interior (closure (interior (A ×ˢ B))) =
          interior (closure (interior A)) ×ˢ
            interior (closure (interior B)) := by
      calc
        interior (closure (interior (A ×ˢ B)))
            = interior ((closure (interior A)) ×ˢ (closure (interior B))) := by
                simpa [h_closure_prod]
        _ = interior (closure (interior A)) ×ˢ
            interior (closure (interior B)) := by
                simpa using
                  interior_prod_eq
                    (s := closure (interior A))
                    (t := closure (interior B))
    -- Extract the `Y`-coordinate from the membership.
    have h_mem :
        ((x, y) : X × Y) ∈
          interior (closure (interior A)) ×ˢ
            interior (closure (interior B)) := by
      simpa [h_interior_closure_prod] using h_int_prod
    exact (Set.mem_prod.1 h_mem).2
  exact ⟨hP2A, hP2B⟩