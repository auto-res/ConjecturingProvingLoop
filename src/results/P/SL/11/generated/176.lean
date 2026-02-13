

theorem P3_of_P3_prod_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : A.Nonempty)
    (h : Topology.P3 (A ×ˢ B)) :
    Topology.P3 B := by
  dsimp [Topology.P3] at h ⊢
  intro y hyB
  rcases hA with ⟨x, hxA⟩
  -- Form the point in the product set.
  have hxy_prod : (x, y) ∈ A ×ˢ B := ⟨hxA, hyB⟩
  -- Apply `P3` for the product.
  have hxy_int : (x, y) ∈ interior (closure (A ×ˢ B)) := h hxy_prod
  -- Rewrite using properties of `closure` and `interior` for products.
  have hxy_int' : (x, y) ∈ interior (closure A ×ˢ closure B) := by
    simpa [closure_prod_eq] using hxy_int
  have hxy_int'' : (x, y) ∈ interior (closure A) ×ˢ interior (closure B) := by
    simpa [interior_prod_eq] using hxy_int'
  -- Extract the second coordinate.
  exact hxy_int''.2