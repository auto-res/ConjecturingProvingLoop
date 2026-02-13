

theorem P1_of_P1_prod_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : A.Nonempty)
    (h : Topology.P1 (A ×ˢ B)) :
    Topology.P1 B := by
  dsimp [Topology.P1] at h ⊢
  intro y hyB
  rcases hA with ⟨x, hxA⟩
  -- Form the point `(x, y) ∈ A ×ˢ B`.
  have hxy_prod : (x, y) ∈ A ×ˢ B := ⟨hxA, hyB⟩
  -- Apply `P1` for the product.
  have hxy_closure₁ :
      (x, y) ∈ closure (interior (A ×ˢ B)) := h hxy_prod
  -- Rewrite `interior (A ×ˢ B)` via `interior_prod_eq`.
  have hxy_closure₂ :
      (x, y) ∈ closure ((interior A) ×ˢ (interior B)) := by
    simpa [interior_prod_eq] using hxy_closure₁
  -- Rewrite the closure of a product via `closure_prod_eq`.
  have hxy_closure₃ :
      (x, y) ∈ closure (interior A) ×ˢ closure (interior B) := by
    simpa [closure_prod_eq] using hxy_closure₂
  -- Extract the second coordinate to conclude `P1` for `B`.
  exact hxy_closure₃.2