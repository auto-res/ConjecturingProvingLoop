

theorem P2_prod_left_of_nonempty
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hBne : B.Nonempty) :
    Topology.P2 (A ×ˢ B) → Topology.P2 A := by
  intro hProd
  dsimp [Topology.P2] at hProd ⊢
  intro x hxA
  classical
  obtain ⟨y, hyB⟩ := hBne
  -- Form the point `(x, y)` in the product.
  have h_mem_prod : ((x, y) : X × Y) ∈ A ×ˢ B := by
    exact And.intro hxA hyB
  -- Apply the `P2` property of the product.
  have h_int_prod :
      ((x, y) : X × Y) ∈ interior (closure (interior (A ×ˢ B))) :=
    hProd h_mem_prod
  -- Identify `interior (A ×ˢ B)` with a product of interiors.
  have h_int_eq :
      interior (A ×ˢ B) = interior A ×ˢ interior B := by
    simpa using interior_prod_eq (s := A) (t := B)
  -- Identify the closure of this interior with a product of closures.
  have h_closure_eq :
      closure (interior (A ×ˢ B)) =
        closure (interior A) ×ˢ closure (interior B) := by
    calc
      closure (interior (A ×ˢ B))
          = closure (interior A ×ˢ interior B) := by
              simpa [h_int_eq]
      _ = closure (interior A) ×ˢ closure (interior B) := by
              simpa using
                closure_prod_eq (s := interior A) (t := interior B)
  -- Rewrite the relevant interior once more.
  have h_interior_closure_eq :
      interior (closure (interior (A ×ˢ B))) =
        interior (closure (interior A)) ×ˢ
          interior (closure (interior B)) := by
    calc
      interior (closure (interior (A ×ˢ B)))
          = interior ((closure (interior A)) ×ˢ (closure (interior B))) := by
              simpa [h_closure_eq]
      _ = interior (closure (interior A)) ×ˢ
          interior (closure (interior B)) := by
              simpa using
                interior_prod_eq
                  (s := closure (interior A))
                  (t := closure (interior B))
  -- Transport membership through these identifications and extract the `X`–coordinate.
  have h_mem :
      ((x, y) : X × Y) ∈
        interior (closure (interior A)) ×ˢ
          interior (closure (interior B)) := by
    simpa [h_interior_closure_eq] using h_int_prod
  exact (Set.mem_prod.1 h_mem).1