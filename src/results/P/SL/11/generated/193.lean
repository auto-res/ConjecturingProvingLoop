

theorem P1_of_P2_prod_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : A.Nonempty)
    (hP2 : Topology.P2 (A ×ˢ B)) :
    Topology.P1 B := by
  dsimp [Topology.P1] at *
  intro y hyB
  -- Pick an element `x ∈ A` to form the product point `(x, y)`.
  rcases hA with ⟨x, hxA⟩
  have hxy_prod : (x, y) ∈ A ×ˢ B := ⟨hxA, hyB⟩
  -- Apply `P2` for the product to obtain interior membership.
  have hxy_int :
      (x, y) ∈ interior (closure (interior (A ×ˢ B))) := hP2 hxy_prod
  -- The interior is contained in the closure of the same set.
  have hxy_closure₁ :
      (x, y) ∈ closure (interior (A ×ˢ B)) :=
    (interior_subset : interior (closure (interior (A ×ˢ B)))
        ⊆ closure (interior (A ×ˢ B))) hxy_int
  -- Rewrite `interior (A ×ˢ B)` via `interior_prod_eq`.
  have hxy_closure₂ :
      (x, y) ∈ closure ((interior A) ×ˢ (interior B)) := by
    simpa [interior_prod_eq] using hxy_closure₁
  -- Rewrite the closure of a product via `closure_prod_eq`.
  have hxy_closure₃ :
      (x, y) ∈ closure (interior A) ×ˢ closure (interior B) := by
    simpa [closure_prod_eq] using hxy_closure₂
  -- Extract the second coordinate to conclude `y ∈ closure (interior B)`.
  exact hxy_closure₃.2