

theorem P1_prod_left_of_nonempty
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hBne : B.Nonempty) :
    Topology.P1 (A ×ˢ B) → Topology.P1 A := by
  intro hProd
  dsimp [Topology.P1] at hProd ⊢
  intro x hxA
  classical
  -- Choose any element of `B` to build a point in the product.
  obtain ⟨y, hyB⟩ := hBne
  have h_mem_prod : ((x, y) : X × Y) ∈ A ×ˢ B := by
    exact And.intro hxA hyB
  -- Apply `P1` to the product.
  have h_cl_prod : ((x, y) : X × Y) ∈ closure (interior (A ×ˢ B)) :=
    hProd h_mem_prod
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