

theorem denseInterior_left_and_P2_right_implies_P2_prod
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    Dense (interior A) → Topology.P2 B → Topology.P2 (A ×ˢ B) := by
  intro hDenseInt hP2B
  dsimp [Topology.P2] at hP2B ⊢
  intro p hp
  -- Coordinates of the point `p`
  have hxA : p.1 ∈ A := hp.1
  have hyB : p.2 ∈ B := hp.2
  -- Thanks to the density of `interior A`, its closure's interior is the whole space
  have hIntA_univ :
      interior (closure (interior A : Set X)) = (Set.univ : Set X) :=
    interior_closure_interior_eq_univ_of_dense (X := X) (A := A) hDenseInt
  -- Hence `p.1` lies in `interior (closure (interior A))`
  have hx_int :
      p.1 ∈ interior (closure (interior A)) := by
    have : p.1 ∈ (Set.univ : Set X) := by
      trivial
    simpa [hIntA_univ] using this
  -- Apply the `P2` property of `B` to the second coordinate
  have hy_int :
      p.2 ∈ interior (closure (interior B)) := hP2B hyB
  -- Combine the two interior memberships
  have h_mem_prod :
      (p : X × Y) ∈
        interior (closure (interior A)) ×ˢ
          interior (closure (interior B)) :=
    And.intro hx_int hy_int
  -- Identify `interior (closure (interior (A ×ˢ B)))`
  have h_eq :=
    interior_closure_interior_prod (X := X) (Y := Y) (A := A) (B := B)
  -- Conclude the desired membership
  simpa [h_eq] using h_mem_prod