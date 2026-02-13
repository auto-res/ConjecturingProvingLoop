

theorem P3_prod_implies_P3_left_and_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hProd : Topology.P3 (A ×ˢ B))
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    Topology.P3 A ∧ Topology.P3 B := by
  -- First, derive `P3 A`.
  have hP3A : Topology.P3 A := by
    dsimp [Topology.P3] at hProd
    dsimp [Topology.P3]
    intro x hx
    rcases hBne with ⟨y, hy⟩
    have h_mem_prod : ((x, y) : X × Y) ∈ A ×ˢ B := ⟨hx, hy⟩
    have h_int_prod : ((x, y) : X × Y) ∈ interior (closure (A ×ˢ B)) :=
      hProd h_mem_prod
    -- Rewrite the interior of the closure of the product.
    have h_closure_prod :
        closure (A ×ˢ B) = closure A ×ˢ closure B := by
      simpa using closure_prod_eq (s := A) (t := B)
    have h_int_prod' :
        ((x, y) : X × Y) ∈
          interior ((closure A) ×ˢ (closure B)) := by
      simpa [h_closure_prod] using h_int_prod
    have h_int_eq :
        interior ((closure A) ×ˢ (closure B)) =
          interior (closure A) ×ˢ interior (closure B) := by
      simpa using interior_prod_eq (s := closure A) (t := closure B)
    have h_mem :
        ((x, y) : X × Y) ∈
          interior (closure A) ×ˢ interior (closure B) := by
      simpa [h_int_eq] using h_int_prod'
    exact (Set.mem_prod.1 h_mem).1
  -- Next, derive `P3 B`.
  have hP3B : Topology.P3 B := by
    dsimp [Topology.P3] at hProd
    dsimp [Topology.P3]
    intro y hy
    rcases hAne with ⟨x, hx⟩
    have h_mem_prod : ((x, y) : X × Y) ∈ A ×ˢ B := ⟨hx, hy⟩
    have h_int_prod : ((x, y) : X × Y) ∈ interior (closure (A ×ˢ B)) :=
      hProd h_mem_prod
    -- Rewrite as above.
    have h_closure_prod :
        closure (A ×ˢ B) = closure A ×ˢ closure B := by
      simpa using closure_prod_eq (s := A) (t := B)
    have h_int_prod' :
        ((x, y) : X × Y) ∈
          interior ((closure A) ×ˢ (closure B)) := by
      simpa [h_closure_prod] using h_int_prod
    have h_int_eq :
        interior ((closure A) ×ˢ (closure B)) =
          interior (closure A) ×ˢ interior (closure B) := by
      simpa using interior_prod_eq (s := closure A) (t := closure B)
    have h_mem :
        ((x, y) : X × Y) ∈
          interior (closure A) ×ˢ interior (closure B) := by
      simpa [h_int_eq] using h_int_prod'
    exact (Set.mem_prod.1 h_mem).2
  exact ⟨hP3A, hP3B⟩