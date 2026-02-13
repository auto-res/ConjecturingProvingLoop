

theorem dense_left_and_P3_right_implies_P3_prod
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hDense : Dense A) (hP3B : Topology.P3 B) :
    Topology.P3 (A ×ˢ B) := by
  dsimp [Topology.P3] at hP3B ⊢
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- `interior (closure A)` is the whole space, thanks to the density of `A`.
  have h_closureA : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  have h_int_closureA : interior (closure A) = (Set.univ : Set X) := by
    have : interior (closure A) = interior ((Set.univ : Set X)) := by
      simpa [h_closureA]
    simpa [interior_univ] using this
  -- Coordinates belong to the corresponding interiors.
  have hx : p.1 ∈ interior (closure A) := by
    have : p.1 ∈ (Set.univ : Set X) := by
      trivial
    simpa [h_int_closureA] using this
  have hy : p.2 ∈ interior (closure B) := hP3B hpB
  -- Relate `interior (closure (A ×ˢ B))` to a product of interiors.
  have h_closure_prod :
      closure (A ×ˢ B) = (closure A) ×ˢ (closure B) := by
    simpa using closure_prod_eq (s := A) (t := B)
  have h_int_prod :
      interior (closure (A ×ˢ B)) =
        interior (closure A) ×ˢ interior (closure B) := by
    have h := interior_prod_eq (s := closure A) (t := closure B)
    simpa [h_closure_prod] using h
  -- Assemble the conclusion.
  have h_mem : (p : X × Y) ∈
      interior (closure A) ×ˢ interior (closure B) := by
    exact And.intro hx hy
  simpa [h_int_prod] using h_mem