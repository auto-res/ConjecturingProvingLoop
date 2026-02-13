

theorem P3_sUnion_interiors {X : Type*} [TopologicalSpace X] {S : Set (Set X)} : Topology.P3 (⋃₀ (Set.image interior S)) := by
  have hP3 : ∀ U ∈ Set.image interior S, Topology.P3 U := by
    intro U hU
    rcases hU with ⟨A, hAS, rfl⟩
    exact P3_interior (X := X) (A := A)
  simpa using (P3_unionₛ (X := X) (S := Set.image interior S) hP3)

theorem P3_product_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P3 (A ×ˢ B) → Topology.P3 (B ×ˢ A) := by
  intro hP3
  simpa using
    (P3_image_homeomorph
        (e := Homeomorph.prodComm X Y)
        (A := (A ×ˢ B))) hP3