

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : Topology.P1 A → Topology.P1 (e '' A) := by
  intro hP1
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `P1` gives a point of the closure of `interior A`.
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- Apply the homeomorphism.
  have h_in : (e x : Y) ∈ e '' closure (interior A) := ⟨x, hx_cl, rfl⟩
  -- A homeomorphism sends closures to closures.
  have h_image_closure :
      (e '' closure (interior A) : Set Y) = closure (e '' interior A) := by
    simpa using e.image_closure (interior A)
  have h1 : (e x : Y) ∈ closure (e '' interior A) := by
    simpa [h_image_closure] using h_in
  -- A homeomorphism sends interiors to interiors.
  have h_image_interior :
      (e '' interior A : Set Y) = interior (e '' A) := by
    simpa using e.image_interior A
  simpa [h_image_interior] using h1

theorem P2_prod_univ_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : Topology.P2 A → Topology.P2 (A ×ˢ (Set.univ : Set Y)) := by
  intro hP2A
  apply P2_prod (A := A) (B := (Set.univ : Set Y))
  · exact hP2A
  · exact P2_univ (X := Y)

theorem P2_union_iInter {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, Topology.P2 (A i)) : Topology.P2 (⋃ i, interior (A i)) := by
  -- Each `interior (A i)` satisfies `P2`.
  have hP2_int : ∀ i, Topology.P2 (interior (A i)) := by
    intro i
    simpa using (Topology.P2_interior (A := A i))
  -- Apply `P2_iUnion` to the family `interior (A i)`.
  simpa using
    (Topology.P2_iUnion (X := X) (A := fun i => interior (A i)) hP2_int)

theorem P3_prod_univ_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : Topology.P3 B → Topology.P3 ((Set.univ : Set X) ×ˢ B) := by
  intro hP3B
  have hP3_univ : Topology.P3 (Set.univ : Set X) := by
    simpa using (Topology.P3_univ (X := X))
  simpa using
    (Topology.P3_prod (A := (Set.univ : Set X)) (B := B) hP3_univ hP3B)