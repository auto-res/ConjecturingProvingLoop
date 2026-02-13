

theorem P3_of_P3_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hB : B.Nonempty)
    (h : Topology.P3 (A ×ˢ B)) :
    Topology.P3 A := by
  dsimp [Topology.P3] at h ⊢
  intro x hxA
  rcases hB with ⟨y, hyB⟩
  have hxy_prod : (x, y) ∈ A ×ˢ B := by
    exact And.intro hxA hyB
  have hxy_int : (x, y) ∈ interior (closure (A ×ˢ B)) := h hxy_prod
  have hxy_int' : (x, y) ∈ interior (closure A ×ˢ closure B) := by
    simpa [closure_prod_eq] using hxy_int
  have hxy_int'' :
      (x, y) ∈ interior (closure A) ×ˢ interior (closure B) := by
    simpa [interior_prod_eq] using hxy_int'
  exact hxy_int''.1